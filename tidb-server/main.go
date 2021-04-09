// Copyright 2015 PingCAP, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// See the License for the specific language governing permissions and
// limitations under the License.

package main

import (
	"context"
	"flag"
	"fmt"
	"io/ioutil"
	"os"
	"runtime"
	"strconv"
	"strings"
	"sync/atomic"
	"time"

	"github.com/opentracing/opentracing-go"
	"github.com/pingcap/errors"
	"github.com/pingcap/log"
	"github.com/pingcap/parser/mysql"
	"github.com/pingcap/parser/terror"
	parsertypes "github.com/pingcap/parser/types"
	pumpcli "github.com/pingcap/tidb-tools/tidb-binlog/pump_client"
	"github.com/pingcap/tidb/bindinfo"
	"github.com/pingcap/tidb/config"
	"github.com/pingcap/tidb/ddl"
	"github.com/pingcap/tidb/domain"
	"github.com/pingcap/tidb/executor"
	"github.com/pingcap/tidb/kv"
	"github.com/pingcap/tidb/metrics"
	plannercore "github.com/pingcap/tidb/planner/core"
	"github.com/pingcap/tidb/plugin"
	"github.com/pingcap/tidb/privilege/privileges"
	"github.com/pingcap/tidb/server"
	"github.com/pingcap/tidb/session"
	"github.com/pingcap/tidb/sessionctx/binloginfo"
	"github.com/pingcap/tidb/sessionctx/variable"
	"github.com/pingcap/tidb/statistics"
	kvstore "github.com/pingcap/tidb/store"
	"github.com/pingcap/tidb/store/driver"
	"github.com/pingcap/tidb/store/mockstore"
	"github.com/pingcap/tidb/store/tikv"
	"github.com/pingcap/tidb/util"
	"github.com/pingcap/tidb/util/disk"
	"github.com/pingcap/tidb/util/domainutil"
	"github.com/pingcap/tidb/util/kvcache"
	"github.com/pingcap/tidb/util/logutil"
	"github.com/pingcap/tidb/util/memory"
	"github.com/pingcap/tidb/util/printer"
	"github.com/pingcap/tidb/util/profile"
	"github.com/pingcap/tidb/util/signal"
	"github.com/pingcap/tidb/util/sys/linux"
	storageSys "github.com/pingcap/tidb/util/sys/storage"
	"github.com/pingcap/tidb/util/systimemon"
	"github.com/prometheus/client_golang/prometheus"
	"github.com/prometheus/client_golang/prometheus/push"
	pd "github.com/tikv/pd/client"
	"go.uber.org/automaxprocs/maxprocs"
	"go.uber.org/zap"
	"google.golang.org/grpc/grpclog"
)

// Flag Names 标志名称
const (
	nmVersion                = "V"
	nmConfig                 = "config"
	nmConfigCheck            = "config-check"
	nmConfigStrict           = "config-strict"
	nmStore                  = "store"
	nmStorePath              = "path"
	nmHost                   = "host"
	nmAdvertiseAddress       = "advertise-address"
	nmPort                   = "P"
	nmCors                   = "cors"
	nmSocket                 = "socket"
	nmEnableBinlog           = "enable-binlog"
	nmRunDDL                 = "run-ddl"
	nmLogLevel               = "L"
	nmLogFile                = "log-file"
	nmLogSlowQuery           = "log-slow-query"
	nmReportStatus           = "report-status"
	nmStatusHost             = "status-host"
	nmStatusPort             = "status"
	nmMetricsAddr            = "metrics-addr"
	nmMetricsInterval        = "metrics-interval"
	nmDdlLease               = "lease"
	nmTokenLimit             = "token-limit"
	nmPluginDir              = "plugin-dir"
	nmPluginLoad             = "plugin-load"
	nmRepairMode             = "repair-mode"
	nmRepairList             = "repair-list"
	nmRequireSecureTransport = "require-secure-transport"

	nmProxyProtocolNetworks      = "proxy-protocol-networks"
	nmProxyProtocolHeaderTimeout = "proxy-protocol-header-timeout"
	nmAffinityCPU                = "affinity-cpus"
)

var (
	version      = flagBoolean(nmVersion, false, "print version information and exit")
	configPath   = flag.String(nmConfig, "", "config file path")
	configCheck  = flagBoolean(nmConfigCheck, false, "check config file validity and exit")
	configStrict = flagBoolean(nmConfigStrict, false, "enforce config file validity")

	// Base
	store            = flag.String(nmStore, "unistore", "registered store name, [tikv, mocktikv, unistore]")
	storePath        = flag.String(nmStorePath, "/tmp/tidb", "tidb storage path")
	host             = flag.String(nmHost, "0.0.0.0", "tidb server host")
	advertiseAddress = flag.String(nmAdvertiseAddress, "", "tidb server advertise IP")
	port             = flag.String(nmPort, "4000", "tidb server port")
	cors             = flag.String(nmCors, "", "tidb server allow cors origin")
	socket           = flag.String(nmSocket, "", "The socket file to use for connection.")
	enableBinlog     = flagBoolean(nmEnableBinlog, false, "enable generate binlog")
	runDDL           = flagBoolean(nmRunDDL, true, "run ddl worker on this tidb-server")
	ddlLease         = flag.String(nmDdlLease, "45s", "schema lease duration, very dangerous to change only if you know what you do")
	tokenLimit       = flag.Int(nmTokenLimit, 1000, "the limit of concurrent executed sessions")
	pluginDir        = flag.String(nmPluginDir, "/data/deploy/plugin", "the folder that hold plugin")
	pluginLoad       = flag.String(nmPluginLoad, "", "wait load plugin name(separated by comma)")
	affinityCPU      = flag.String(nmAffinityCPU, "", "affinity cpu (cpu-no. separated by comma, e.g. 1,2,3)")
	repairMode       = flagBoolean(nmRepairMode, false, "enable admin repair mode")
	repairList       = flag.String(nmRepairList, "", "admin repair table list")
	requireTLS       = flag.Bool(nmRequireSecureTransport, false, "require client use secure transport")

	// Log
	logLevel     = flag.String(nmLogLevel, "info", "log level: info, debug, warn, error, fatal")
	logFile      = flag.String(nmLogFile, "", "log file path")
	logSlowQuery = flag.String(nmLogSlowQuery, "", "slow query file path")

	// Status
	reportStatus    = flagBoolean(nmReportStatus, true, "If enable status report HTTP service.")
	statusHost      = flag.String(nmStatusHost, "0.0.0.0", "tidb server status host")
	statusPort      = flag.String(nmStatusPort, "10080", "tidb server status port")
	metricsAddr     = flag.String(nmMetricsAddr, "", "prometheus pushgateway address, leaves it empty will disable prometheus push.")
	metricsInterval = flag.Uint(nmMetricsInterval, 15, "prometheus client push interval in second, set \"0\" to disable prometheus push.")

	// PROXY Protocol
	proxyProtocolNetworks      = flag.String(nmProxyProtocolNetworks, "", "proxy protocol networks allowed IP or *, empty mean disable proxy protocol support")
	proxyProtocolHeaderTimeout = flag.Uint(nmProxyProtocolHeaderTimeout, 5, "proxy protocol header read timeout, unit is second.")
)

var (
	storage  kv.Storage
	dom      *domain.Domain
	svr      *server.Server
	graceful bool
)

func main() {
	// 返回在系统中注册的flag，必须在所有的flag都注册好而未访问其值时执行，未注册会返回err
	flag.Parse()

	/*默认是false*/
	if *version {
		fmt.Println(printer.GetTiDBInfo())
		os.Exit(0)
	}

	/*注册存储引擎*/
	registerStores()

	/*注册指标*/
	registerMetrics()

	/*初始化配置信息*/
	config.InitializeConfig(*configPath, *configCheck, *configStrict, overrideConfig)
	if config.GetGlobalConfig().OOMUseTmpStorage {
		config.GetGlobalConfig().UpdateTempStoragePath()
		err := disk.InitializeTempDir()
		terror.MustNil(err)
		checkTempStorageQuota()
	}

	/*设置全局变量*/
	setGlobalVars()
	/*设置CPU*/
	setCPUAffinity()
	/*设置日志*/
	setupLog()
	/*设置堆文件跟踪器*/
	setHeapProfileTracker()
	/*设置追踪*/
	setupTracing() // Should before createServer and after setup config.
	/*打印tidb的信息*/
	printInfo()
	/*设置二进制日志客户端*/
	setupBinlogClient()
	/*设置指标*/
	setupMetrics()
	/*创建存储和抽象域，抽象域可以理解为一个抽象的存储空间，可以在其中创建数据库和数据表，不通的域之间可以存在相同名称的数据库*/
	createStoreAndDomain()
	/*创建服务器*/
	createServer()
	/*设置信号处理程序，参数是一个bool类型的处理函数*/
	signal.SetupSignalHandler(serverShutdown)

	/*启动服务器*/
	runServer()

	/*清除*/
	cleanup()
	/*同步日志*/
	syncLog()
}

/*程序以给出的状态码退出，状态码o表示成功，非0表示出错，程序会立即终止*/
func exit() {
	syncLog()
	os.Exit(0)
}

func syncLog() {
	if err := log.Sync(); err != nil {
		fmt.Fprintln(os.Stderr, "sync log err:", err)
		os.Exit(1)
	}
}

/*检查临时存储指标*/
func checkTempStorageQuota() {
	// check capacity and the quota when OOMUseTmpStorage is enabled
	c := config.GetGlobalConfig()
	if c.TempStorageQuota < 0 {
		// means unlimited, do nothing
	} else {
		capacityByte, err := storageSys.GetTargetDirectoryCapacity(c.TempStoragePath)
		if err != nil {
			log.Fatal(err.Error())
		} else if capacityByte < uint64(c.TempStorageQuota) {
			log.Fatal(fmt.Sprintf("value of [tmp-storage-quota](%d byte) exceeds the capacity(%d byte) of the [%s] directory", c.TempStorageQuota, capacityByte, c.TempStoragePath))
		}
	}
}

/*设置CPU*/
func setCPUAffinity() {
	if affinityCPU == nil || len(*affinityCPU) == 0 {
		return
	}
	var cpu []int
	for _, af := range strings.Split(*affinityCPU, ",") {
		af = strings.TrimSpace(af)
		if len(af) > 0 {
			c, err := strconv.Atoi(af)
			if err != nil {
				fmt.Fprintf(os.Stderr, "wrong affinity cpu config: %s", *affinityCPU)
				exit()
			}
			cpu = append(cpu, c)
		}
	}
	err := linux.SetAffinity(cpu)
	if err != nil {
		fmt.Fprintf(os.Stderr, "set cpu affinity failure: %v", err)
		exit()
	}
	runtime.GOMAXPROCS(len(cpu))
	metrics.MaxProcs.Set(float64(runtime.GOMAXPROCS(0)))
}

/*设置堆配置文件追踪器*/
func setHeapProfileTracker() {
	c := config.GetGlobalConfig()
	d := parseDuration(c.Performance.MemProfileInterval)
	go profile.HeapProfileForGlobalMemTracker(d)
}

/*在里可以添加其它的kv数据库*/
func registerStores() {
	err := kvstore.Register("tikv", driver.TiKVDriver{})
	terror.MustNil(err)
	err = kvstore.Register("mocktikv", mockstore.MockTiKVDriver{})
	terror.MustNil(err)
	err = kvstore.Register("unistore", mockstore.EmbedUnistoreDriver{})
	terror.MustNil(err)
}

/*注册指标*/
func registerMetrics() {
	metrics.RegisterMetrics()
}

/*创建存储引擎和工作空间*/
func createStoreAndDomain() {
	cfg := config.GetGlobalConfig()
	fullPath := fmt.Sprintf("%s://%s", cfg.Store, cfg.Path)
	var err error
	storage, err = kvstore.New(fullPath)
	terror.MustNil(err)
	// Bootstrap a session to load information schema.
	dom, err = session.BootstrapSession(storage)
	terror.MustNil(err)
}

/*设置二进制文件客户端*/
func setupBinlogClient() {
	cfg := config.GetGlobalConfig()
	if !cfg.Binlog.Enable {
		return
	}

	if cfg.Binlog.IgnoreError {
		binloginfo.SetIgnoreError(true)
	}

	var (
		client *pumpcli.PumpsClient
		err    error
	)
	/*CA机构path、证书path、key path*/
	securityOption := pd.SecurityOption{
		CAPath:   cfg.Security.ClusterSSLCA,
		CertPath: cfg.Security.ClusterSSLCert,
		KeyPath:  cfg.Security.ClusterSSLKey,
	}

	/*套接字信息，使用套接字文件编写二进制日志文件*/
	if len(cfg.Binlog.BinlogSocket) == 0 {
		/*创建新的*/
		client, err = pumpcli.NewPumpsClient(cfg.Path, cfg.Binlog.Strategy, parseDuration(cfg.Binlog.WriteTimeout), securityOption)
	} else {
		client, err = pumpcli.NewLocalPumpsClient(cfg.Path, cfg.Binlog.BinlogSocket, parseDuration(cfg.Binlog.WriteTimeout), securityOption)
	}

	/*如果err不为nil，将err清理并重置*/
	terror.MustNil(err)

	/*初始化*/
	err = pumpcli.InitLogger(cfg.Log.ToLogConfig())
	terror.MustNil(err)

	binloginfo.SetPumpsClient(client)
	log.Info("tidb-server", zap.Bool("create pumps client success, ignore binlog error", cfg.Binlog.IgnoreError))
}

// Prometheus push.
const zeroDuration = time.Duration(0)

// pushMetric pushes metrics in background. 取指标
func pushMetric(addr string, interval time.Duration) {
	if interval == zeroDuration || len(addr) == 0 {
		log.Info("disable Prometheus push client")
		return
	}
	log.Info("start prometheus push client", zap.String("server addr", addr), zap.String("interval", interval.String()))
	go prometheusPushClient(addr, interval)
}

// prometheusPushClient pushes metrics to Prometheus Pushgateway.
func prometheusPushClient(addr string, interval time.Duration) {
	// TODO: TiDB do not have uniq name, so we use host+port to compose a name.
	job := "tidb"
	pusher := push.New(addr, job)
	pusher = pusher.Gatherer(prometheus.DefaultGatherer)
	pusher = pusher.Grouping("instance", instanceName())
	for {
		err := pusher.Push()
		if err != nil {
			log.Error("could not push metrics to prometheus pushgateway", zap.String("err", err.Error()))
		}
		time.Sleep(interval)
	}
}

func instanceName() string {
	cfg := config.GetGlobalConfig()
	hostname, err := os.Hostname()
	if err != nil {
		return "unknown"
	}
	return fmt.Sprintf("%s_%d", hostname, cfg.Port)
}

// parseDuration parses lease argument string.
func parseDuration(lease string) time.Duration {
	dur, err := time.ParseDuration(lease)
	if err != nil {
		dur, err = time.ParseDuration(lease + "s")
	}
	if err != nil || dur < 0 {
		log.Fatal("invalid lease duration", zap.String("lease", lease))
	}
	return dur
}

func flagBoolean(name string, defaultVal bool, usage string) *bool {
	if !defaultVal {
		// Fix #4125, golang do not print default false value in usage, so we append it.
		usage = fmt.Sprintf("%s (default false)", usage)
		return flag.Bool(name, defaultVal, usage)
	}
	return flag.Bool(name, defaultVal, usage)
}

// overrideConfig considers command arguments and overrides some config items in the Config.重写部分配置信息
func overrideConfig(cfg *config.Config) {
	actualFlags := make(map[string]bool)
	flag.Visit(func(f *flag.Flag) {
		actualFlags[f.Name] = true
	})

	// Base
	if actualFlags[nmHost] {
		cfg.Host = *host
	}
	if actualFlags[nmAdvertiseAddress] {
		var err error
		if len(strings.Split(*advertiseAddress, " ")) > 1 {
			err = errors.Errorf("Only support one advertise-address")
		}
		terror.MustNil(err)
		cfg.AdvertiseAddress = *advertiseAddress
	}
	if len(cfg.AdvertiseAddress) == 0 && cfg.Host == "0.0.0.0" {
		cfg.AdvertiseAddress = util.GetLocalIP()
	}
	if len(cfg.AdvertiseAddress) == 0 {
		cfg.AdvertiseAddress = cfg.Host
	}
	var err error
	if actualFlags[nmPort] {
		var p int
		p, err = strconv.Atoi(*port)
		terror.MustNil(err)
		cfg.Port = uint(p)
	}
	if actualFlags[nmCors] {
		fmt.Println(cors)
		cfg.Cors = *cors
	}
	if actualFlags[nmStore] {
		cfg.Store = *store
	}
	if actualFlags[nmStorePath] {
		cfg.Path = *storePath
	}
	if actualFlags[nmSocket] {
		cfg.Socket = *socket
	}
	if actualFlags[nmEnableBinlog] {
		cfg.Binlog.Enable = *enableBinlog
	}
	if actualFlags[nmRunDDL] {
		cfg.RunDDL = *runDDL
	}
	if actualFlags[nmDdlLease] {
		cfg.Lease = *ddlLease
	}
	if actualFlags[nmTokenLimit] {
		cfg.TokenLimit = uint(*tokenLimit)
	}
	if actualFlags[nmPluginLoad] {
		cfg.Plugin.Load = *pluginLoad
	}
	if actualFlags[nmPluginDir] {
		cfg.Plugin.Dir = *pluginDir
	}
	if actualFlags[nmRequireSecureTransport] {
		cfg.Security.RequireSecureTransport = *requireTLS
	}
	if actualFlags[nmRepairMode] {
		cfg.RepairMode = *repairMode
	}
	if actualFlags[nmRepairList] {
		if cfg.RepairMode {
			cfg.RepairTableList = stringToList(*repairList)
		}
	}

	// Log
	if actualFlags[nmLogLevel] {
		cfg.Log.Level = *logLevel
	}
	if actualFlags[nmLogFile] {
		cfg.Log.File.Filename = *logFile
	}
	if actualFlags[nmLogSlowQuery] {
		cfg.Log.SlowQueryFile = *logSlowQuery
	}

	// Status
	if actualFlags[nmReportStatus] {
		cfg.Status.ReportStatus = *reportStatus
	}
	if actualFlags[nmStatusHost] {
		cfg.Status.StatusHost = *statusHost
	}
	if actualFlags[nmStatusPort] {
		var p int
		p, err = strconv.Atoi(*statusPort)
		terror.MustNil(err)
		cfg.Status.StatusPort = uint(p)
	}
	if actualFlags[nmMetricsAddr] {
		cfg.Status.MetricsAddr = *metricsAddr
	}
	if actualFlags[nmMetricsInterval] {
		cfg.Status.MetricsInterval = *metricsInterval
	}

	// PROXY Protocol
	if actualFlags[nmProxyProtocolNetworks] {
		cfg.ProxyProtocol.Networks = *proxyProtocolNetworks
	}
	if actualFlags[nmProxyProtocolHeaderTimeout] {
		cfg.ProxyProtocol.HeaderTimeout = *proxyProtocolHeaderTimeout
	}
}

/*设置全局变量*/
func setGlobalVars() {
	cfg := config.GetGlobalConfig()

	// Disable automaxprocs log
	nopLog := func(string, ...interface{}) {}
	_, err := maxprocs.Set(maxprocs.Logger(nopLog))
	terror.MustNil(err)
	// We should respect to user's settings in config file.
	// The default value of MaxProcs is 0, runtime.GOMAXPROCS(0) is no-op.
	runtime.GOMAXPROCS(int(cfg.Performance.MaxProcs))
	metrics.MaxProcs.Set(float64(runtime.GOMAXPROCS(0)))

	util.SetGOGC(cfg.Performance.GOGC)

	ddlLeaseDuration := parseDuration(cfg.Lease)
	session.SetSchemaLease(ddlLeaseDuration)
	statsLeaseDuration := parseDuration(cfg.Performance.StatsLease)
	session.SetStatsLease(statsLeaseDuration)
	indexUsageSyncLeaseDuration := parseDuration(cfg.Performance.IndexUsageSyncLease)
	session.SetIndexUsageSyncLease(indexUsageSyncLeaseDuration)
	bindinfo.Lease = parseDuration(cfg.Performance.BindInfoLease)
	domain.RunAutoAnalyze = cfg.Performance.RunAutoAnalyze
	statistics.FeedbackProbability.Store(cfg.Performance.FeedbackProbability)
	statistics.MaxQueryFeedbackCount.Store(int64(cfg.Performance.QueryFeedbackLimit))
	statistics.RatioOfPseudoEstimate.Store(cfg.Performance.PseudoEstimateRatio)
	ddl.RunWorker = cfg.RunDDL
	if cfg.SplitTable {
		atomic.StoreUint32(&ddl.EnableSplitTableRegion, 1)
	}
	plannercore.AllowCartesianProduct.Store(cfg.Performance.CrossJoin)
	privileges.SkipWithGrant = cfg.Security.SkipGrantTable
	kv.TxnTotalSizeLimit = cfg.Performance.TxnTotalSizeLimit
	if cfg.Performance.TxnEntrySizeLimit > 120*1024*1024 {
		log.Fatal("cannot set txn entry size limit larger than 120M")
	}
	kv.TxnEntrySizeLimit = cfg.Performance.TxnEntrySizeLimit

	priority := mysql.Str2Priority(cfg.Performance.ForcePriority)
	variable.ForcePriority = int32(priority)

	variable.SetSysVar(variable.TiDBForcePriority, mysql.Priority2Str[priority])
	variable.SetSysVar(variable.TiDBOptDistinctAggPushDown, variable.BoolToOnOff(cfg.Performance.DistinctAggPushDown))
	variable.SetSysVar(variable.TIDBMemQuotaQuery, strconv.FormatInt(cfg.MemQuotaQuery, 10))
	variable.SetSysVar("lower_case_table_names", strconv.Itoa(cfg.LowerCaseTableNames))
	variable.SetSysVar(variable.LogBin, variable.BoolToOnOff(config.GetGlobalConfig().Binlog.Enable))
	variable.SetSysVar(variable.Port, fmt.Sprintf("%d", cfg.Port))
	variable.SetSysVar(variable.Socket, cfg.Socket)
	variable.SetSysVar(variable.DataDir, cfg.Path)
	variable.SetSysVar(variable.TiDBSlowQueryFile, cfg.Log.SlowQueryFile)
	variable.SetSysVar(variable.TiDBIsolationReadEngines, strings.Join(cfg.IsolationRead.Engines, ", "))
	variable.MemoryUsageAlarmRatio.Store(cfg.Performance.MemoryUsageAlarmRatio)

	// For CI environment we default enable prepare-plan-cache.
	plannercore.SetPreparedPlanCache(config.CheckTableBeforeDrop || cfg.PreparedPlanCache.Enabled)
	if plannercore.PreparedPlanCacheEnabled() {
		plannercore.PreparedPlanCacheCapacity = cfg.PreparedPlanCache.Capacity
		plannercore.PreparedPlanCacheMemoryGuardRatio = cfg.PreparedPlanCache.MemoryGuardRatio
		if plannercore.PreparedPlanCacheMemoryGuardRatio < 0.0 || plannercore.PreparedPlanCacheMemoryGuardRatio > 1.0 {
			plannercore.PreparedPlanCacheMemoryGuardRatio = 0.1
		}
		plannercore.PreparedPlanCacheMaxMemory.Store(cfg.Performance.ServerMemoryQuota)
		total, err := memory.MemTotal()
		terror.MustNil(err)
		if plannercore.PreparedPlanCacheMaxMemory.Load() > total || plannercore.PreparedPlanCacheMaxMemory.Load() <= 0 {
			plannercore.PreparedPlanCacheMaxMemory.Store(total)
		}
	}

	atomic.StoreUint64(&tikv.CommitMaxBackoff, uint64(parseDuration(cfg.TiKVClient.CommitTimeout).Seconds()*1000))
	tikv.RegionCacheTTLSec = int64(cfg.TiKVClient.RegionCacheTTL)
	domainutil.RepairInfo.SetRepairMode(cfg.RepairMode)
	domainutil.RepairInfo.SetRepairTableList(cfg.RepairTableList)
	c := config.GetGlobalConfig()
	executor.GlobalDiskUsageTracker.SetBytesLimit(c.TempStorageQuota)
	if c.Performance.ServerMemoryQuota < 1 {
		// If MaxMemory equals 0, it means unlimited
		executor.GlobalMemoryUsageTracker.SetBytesLimit(-1)
	} else {
		executor.GlobalMemoryUsageTracker.SetBytesLimit(int64(c.Performance.ServerMemoryQuota))
	}
	kvcache.GlobalLRUMemUsageTracker.AttachToGlobalTracker(executor.GlobalMemoryUsageTracker)

	t, err := time.ParseDuration(cfg.TiKVClient.StoreLivenessTimeout)
	if err != nil {
		logutil.BgLogger().Fatal("invalid duration value for store-liveness-timeout",
			zap.String("currentValue", config.GetGlobalConfig().TiKVClient.StoreLivenessTimeout))
	}
	tikv.StoreLivenessTimeout = t
	parsertypes.TiDBStrictIntegerDisplayWidth = config.GetGlobalConfig().DeprecateIntegerDisplayWidth
}

/*设置日志*/
func setupLog() {
	cfg := config.GetGlobalConfig()
	err := logutil.InitZapLogger(cfg.Log.ToLogConfig())
	terror.MustNil(err)

	err = logutil.InitLogger(cfg.Log.ToLogConfig())
	terror.MustNil(err)

	if len(os.Getenv("GRPC_DEBUG")) > 0 {
		grpclog.SetLoggerV2(grpclog.NewLoggerV2WithVerbosity(os.Stderr, os.Stderr, os.Stderr, 999))
	} else {
		grpclog.SetLoggerV2(grpclog.NewLoggerV2(ioutil.Discard, ioutil.Discard, os.Stderr))
	}
	// trigger internal http(s) client init.
	util.InternalHTTPClient()
}

/*输出tidb的信息*/
func printInfo() {
	// Make sure the TiDB info is always printed.
	level := log.GetLevel()
	log.SetLevel(zap.InfoLevel)
	printer.PrintTiDBInfo()
	log.SetLevel(level)
}

/*创建服务器*/
func createServer() {
	cfg := config.GetGlobalConfig()
	driver := server.NewTiDBDriver(storage)
	var err error
	svr, err = server.NewServer(cfg, driver)
	// Both domain and storage have started, so we have to clean them before exiting.
	terror.MustNil(err, closeDomainAndStorage)
	svr.SetDomain(dom)
	svr.InitGlobalConnID(dom.ServerID)
	go dom.ExpensiveQueryHandle().SetSessionManager(svr).Run()
	dom.InfoSyncer().SetSessionManager(svr)
}

/*服务器关闭处理程序*/
func serverShutdown(isgraceful bool) {
	if isgraceful {
		/*默认是false，如果需要关闭服务器，这里重置为真*/
		graceful = true
	}

	/*关闭服务器程序*/
	svr.Close()
}

/*设置指标*/
func setupMetrics() {
	cfg := config.GetGlobalConfig()
	// Enable the mutex profile, 1/10 of mutex blocking event sampling.
	runtime.SetMutexProfileFraction(10)
	systimeErrHandler := func() {
		metrics.TimeJumpBackCounter.Inc()
	}
	callBackCount := 0
	sucessCallBack := func() {
		callBackCount++
		// It is callback by monitor per second, we increase metrics.KeepAliveCounter per 5s.
		if callBackCount >= 5 {
			callBackCount = 0
			metrics.KeepAliveCounter.Inc()
		}
	}
	go systimemon.StartMonitor(time.Now, systimeErrHandler, sucessCallBack)

	pushMetric(cfg.Status.MetricsAddr, time.Duration(cfg.Status.MetricsInterval)*time.Second)
}

/*设置追踪器*/
func setupTracing() {
	cfg := config.GetGlobalConfig()
	tracingCfg := cfg.OpenTracing.ToTracingConfig()
	tracingCfg.ServiceName = "TiDB"
	tracer, _, err := tracingCfg.NewTracer()
	if err != nil {
		log.Fatal("setup jaeger tracer failed", zap.String("error message", err.Error()))
	}
	opentracing.SetGlobalTracer(tracer)
}
/*启动服务器*/
func runServer() {
	/*!!!!!启动server*/
	err := svr.Run()
	terror.MustNil(err)
}
/*关闭工作域和存储*/
func closeDomainAndStorage() {
	atomic.StoreUint32(&tikv.ShuttingDown, 1)
	dom.Close()
	err := storage.Close()
	terror.Log(errors.Trace(err))
}

/*清理*/
func cleanup() {
	if graceful {
		svr.GracefulDown(context.Background(), nil)
	} else {
		svr.TryGracefulDown()
	}
	plugin.Shutdown(context.Background())
	closeDomainAndStorage()
	disk.CleanUp()
}

/*讲字符串转换为一个列表*/
func stringToList(repairString string) []string {
	if len(repairString) <= 0 {
		return []string{}
	}
	if repairString[0] == '[' && repairString[len(repairString)-1] == ']' {
		repairString = repairString[1 : len(repairString)-1]
	}
	return strings.FieldsFunc(repairString, func(r rune) bool {
		return r == ',' || r == ' ' || r == '"'
	})
}
