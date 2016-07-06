var version = '0.162095';

// Core modules
var util = require('util'),
    fs = require('fs'),
    http = require('http'),
    path = require('path'),
    exec = require('child_process').exec,
    spawn = require('child_process').spawn,
    os = require('os'),
    url = require('url'),
    crypto = require('crypto'),
    zlib = require('zlib');

// Global variables
var htmlLog = [],
    scriptDir = __dirname, // path.dirname(fs.realpathSync(process.argv[1])),
    hostname = os.hostname(),
    config = null,
    running = false,
    waiting = false,
    useCache = true,
    proxySelenium = null,
    frontend = null,
    frontendServer = null,
    frontendReady = false,
    io = null,
    socket = null,
    standalone = true,
    fileReceived = false,
    connected = false,
    state = {},
    p4Process = null,
    mavenProcess = null,
    serverProcess = null,
    serverReadyRequestTimeout = null,
    CLIProcess = null,
    phantomProcess = null,
    FourDServerProcess = null,
    firstLaunch = true,
    shutDown = false,
    cachedData = {},
    newChangelist = null,
    deployingNewWakandaBuild = false,
    downloadingNewWakandaBuild = false,
    downloadingNewWakandaBuildDone = false,
    downloadingNewWakandaBuildExpect = 0,
    deployingNewWakandaInstaller = false,
    downloadingNewWakandaInstaller = false,
    downloadingNewWakandaInstallerDone = false,
    downloadingNewWakandaInstallerExpect = 0,
    deployingNew4DBuild = false,
    downloadingNew4DBuild = false,
    downloadingNew4DBuildDone = false,
    downloadingNew4DBuildExpect = 0,
    currentServerPath = null,
    currentStudioPath = null,
    currentInstallerPath = null,
    current4DServerPath = null,
    currentShellPath = null,
    currentStatus = null,
    previousChangelist = 0,
    FourDBFileToOpen = null,
    shutdownTimeout = null,
    navigation = [],
    dynamicTimeout = 3 * 60 * 1000,
    softKilled = false,
    hardKilled = false,
    shellProcessKilled = false,
    shellProcessKill = null,
    shellProcess = null,
    softMavenKillTimeout = null,
    softMavenKillTimeoutTestname = null,
    hardMavenKillTimeout = null,
    hardMavenKillTimeoutTestname = null,
    softKillTimeout = null,
    softKillTimeoutTestname = null,
    hardKillTimeout = null,
    hardKillTimeoutTestname = null,
    softCLIKillTimeout = null,
    softCLIKillTimeoutTestname = null,
    hardCLIKillTimeout = null,
    hardCLIKillTimeoutTestname = null,
    monitoringInterval = null,
    monitoringDelay = null,
    auth = null,
    locked = false,
    paused = false,
    runningManual = false,
    runningManualQueue = [],
    runningManualDone = [],
    runningManualCurrentJob = null,
    stopManualTests = false,
    runFromWeb = false,
    crashlocationContentBefore = null,
    crashes = [],
    testHasTimeouted = false,
    runLog = [],
    processListBefore = null,
    forceRebuild = false,
    doNotOverwriteState = false,
    forceRelaunch = false,
    buildRequested = false,
    getAvailableJobsCache = null,
    changelistCache = {};

// Safeguards
process.on('uncaughtException', function(err) {
    consoleLog('[ERROR] unexpected error', err);
    console.log(err.stack);
    if (running === true || runningManual === true) {
        killMainProcesses();
        exterminate(function() {

        });
    }
});
process.on('SIGHUP', exitGracefully);
process.on('SIGBREAK', exitGracefully);
process.on('SIGTERM', exitGracefully);
process.on('SIGINT', exitGracefully);
process.on('exit', exitGracefully);

// Load local JSON config file
loadConfig();

if (typeof config.locked !== 'undefined' && config.locked === true) {
    running = true;
}

// Third-party modules
var request = require('request'),
    bag = require('bagofrequest'),
    temp = require('temp'),
    ncp = require('ncp').ncp,
    parseString = require('xml2js').parseString,
    express = require('express'),
    psTree = require('ps-tree'),
    colors = require('colors'),
    mu = require('mu2'),
    ansi = require('ansi-to-html'),
    async = require('async'),
    moment = require('moment'),
    fs = require('fs-extra');
temp.track();
ncp.limit = 16;

// load config file
function loadConfig(doNotExit) {
    var _config = null;
    if (typeof doNotExit === 'undefined') {
        doNotExit = false;
    }
    try {
        _config = JSON.parse(fs.readFileSync(path.join(scriptDir, 'config', hostname + '.config.json')).toString());
    } catch (e) {
        if (hostname !== 'localhost') {
            try {
                _config = JSON.parse(fs.readFileSync(path.join(scriptDir, 'config', 'localhost.config.json')).toString());
            } catch (e) {
                if (doNotExit === true) {
                    console.log('[WARN] cannot find ' + path.join(scriptDir, 'config', hostname + '.config.json') + ' or ' + path.join(scriptDir, 'config', 'localhost.config.json') + ' config file');
                } else {
                    console.log('[ERROR] cannot find ' + path.join(scriptDir, 'config', hostname + '.config.json') + ' or ' + path.join(scriptDir, 'config', 'localhost.config.json') + ' config file');
                    process.exit(1);
                }
            }
        } else {
            if (doNotExit === true) {
                console.log('[WARN] cannot find ' + path.join(scriptDir, 'config', hostname + '.config.json') + ' config file');
            } else {
                console.log('[ERROR] cannot find ' + path.join(scriptDir, 'config', hostname + '.config.json') + ' config file');
                process.exit(1);
            }
        }
    }
    for (var i in process.env) {
        if (typeof _config[i] === 'undefined') {
            _config[i] = process.env[i];
        }
    }
    if (_config !== null) {
        config = _config;
    }
}

function getProcessListBefore(cb) {
    processListBefore = [];
    if (isMac() || isLinux()) {
        exec('ps ax -o pid,command', function(error, stdout, stderr) {
            var skipFirstLine = true;
            stdout.split(/\r?\n/).forEach(function(_ps) {
                if (skipFirstLine === true) {
                    skipFirstLine = false;
                } else {
                    _ps = _ps.replace(/^\s+/g, '').replace(/\s+$/g, '');
                    if (_ps !== '' && /ps\s+ax\s+-o\s+pid,command/i.test(_ps) === false) {
                        _ps = _ps.split(/\s+/);
                        var pid = parseInt(_ps[0].replace(/^\s+/g, '').replace(/\s+$/g, ''));
                        var cmd = _ps.slice(1).join(' ').replace(/^\s+/g, '').replace(/\s+$/g, '');
                        processListBefore.push({
                            pid: pid,
                            cmd: cmd
                        });
                    }
                }
            });
            processListBefore.sort(function(a, b) {
                if (a.pid < b.pid) {
                    return -1;
                }
                if (a.pid > b.pid) {
                    return 1;
                }
                return 0;
            });
            cb(null);
        });
    } else {
        exec('tasklist /nh', function(error, stdout, stderr) {
            stdout.split(/\r?\n/).forEach(function(_ps) {
                _ps = _ps.replace(/^\s+/g, '').replace(/\s+$/g, '');
                if (_ps !== '' && /tasklist/i.test(_ps) === false) {
                    _ps = /^([a-z0-9\.\s_-]+)\s+([0-9]+)\s+[a-z]+\s+/i.exec(_ps);
                    try {
                        var pid = parseInt(_ps[2].replace(/^\s+/g, '').replace(/\s+$/g, ''));
                        var cmd = _ps[1].replace(/^\s+/g, '').replace(/\s+$/g, '');
                        processListBefore.push({
                            pid: pid,
                            cmd: cmd
                        });
                    } catch (e) {

                    }
                }
            });
            processListBefore.sort(function(a, b) {
                if (a.pid < b.pid) {
                    return -1;
                }
                if (a.pid > b.pid) {
                    return 1;
                }
                return 0;
            });
            cb(null);
        });
    }
}

function getProcessListDiffAfter(cb) {
    if (processListBefore === null) {
        cb(null);
    } else {
        var processListAfter = [];
        if (isMac() || isLinux()) {
            exec('ps ax -o pid,command', function(error, stdout, stderr) {
                var skipFirstLine = true;
                stdout.split(/\r?\n/).forEach(function(_ps) {
                    if (skipFirstLine === true) {
                        skipFirstLine = false;
                    } else {
                        _ps = _ps.replace(/^\s+/g, '').replace(/\s+$/g, '');
                        if (_ps !== '' && /ps\s+ax\s+-o\s+pid,command/i.test(_ps) === false) {
                            _ps = _ps.split(/\s+/);
                            var pid = parseInt(_ps[0].replace(/^\s+/g, '').replace(/\s+$/g, ''));
                            var cmd = _ps.slice(1).join(' ').replace(/^\s+/g, '').replace(/\s+$/g, '');
                            processListAfter.push({
                                pid: pid,
                                cmd: cmd
                            });
                        }
                    }
                });
                processListAfter.sort(function(a, b) {
                    if (a.pid < b.pid) {
                        return -1;
                    }
                    if (a.pid > b.pid) {
                        return 1;
                    }
                    return 0;
                });
                var diff = {
                    less: [],
                    more: []
                };
                for (var i = 0; i < processListBefore.length; i++) {
                    var found = false;
                    for (var j = 0; j < processListAfter.length; j++) {
                        if (processListBefore[i].pid === processListAfter[j].pid) {
                            found = true;
                            break;
                        }
                    }
                    if (found === false) {
                        diff.less.push(processListBefore[i]);
                    }
                }
                for (var i = 0; i < processListAfter.length; i++) {
                    var found = false;
                    for (var j = 0; j < processListBefore.length; j++) {
                        if (processListAfter[i].pid === processListBefore[j].pid) {
                            found = true;
                            break;
                        }
                    }
                    if (found === false) {
                        diff.more.push(processListAfter[i]);
                    }
                }
                cb(diff);
            });
        } else {
            exec('tasklist /nh', function(error, stdout, stderr) {
                stdout.split(/\r?\n/).forEach(function(_ps) {
                    _ps = _ps.replace(/^\s+/g, '').replace(/\s+$/g, '');
                    if (_ps !== '' && /tasklist/i.test(_ps) === false) {
                        _ps = /^([a-z0-9\.\s_-]+)\s+([0-9]+)\s+[a-z]+\s+/i.exec(_ps);
                        try {
                            var pid = parseInt(_ps[2].replace(/^\s+/g, '').replace(/\s+$/g, ''));
                            var cmd = _ps[1].replace(/^\s+/g, '').replace(/\s+$/g, '');
                            processListAfter.push({
                                pid: pid,
                                cmd: cmd
                            });
                        } catch (e) {

                        }
                    }
                });
                processListAfter.sort(function(a, b) {
                    if (a.pid < b.pid) {
                        return -1;
                    }
                    if (a.pid > b.pid) {
                        return 1;
                    }
                    return 0;
                });
                var diff = {
                    less: [],
                    more: []
                };
                for (var i = 0; i < processListBefore.length; i++) {
                    var found = false;
                    for (var j = 0; j < processListAfter.length; j++) {
                        if (processListBefore[i].pid === processListAfter[j].pid) {
                            found = true;
                            break;
                        }
                    }
                    if (found === false) {
                        diff.less.push(processListBefore[i]);
                    }
                }
                for (var i = 0; i < processListAfter.length; i++) {
                    var found = false;
                    for (var j = 0; j < processListBefore.length; j++) {
                        if (processListAfter[i].pid === processListBefore[j].pid) {
                            found = true;
                            break;
                        }
                    }
                    if (found === false) {
                        diff.more.push(processListAfter[i]);
                    }
                }
                cb(diff);
            });
        }
    }
}

// Watch for crashes (any new file created in the dedicated location)
function getCrashlocationContentBefore() {
    crashes = [];
    crashlocationContentBefore = [];
    if (typeof config.crashlocation !== 'undefined') {
        try {
            fs.readdirSync(config.crashlocation).forEach(function(fileName) {
                var file = path.join(config.crashlocation, fileName);
                try {
                    var stat = fs.statSync(file);
                } catch (e) {
                    var stat = false;
                }
                if (stat && stat.isFile() && /^\./i.test(fileName) === false) {
                    crashlocationContentBefore.push(file);
                }
            });
        } catch (e) {
            consoleLog('[WARN] cannot look for crashes (1):', e);
        }
    }
}

function getCrashlocationContentAfter() {
    crashes = [];
    if (typeof config.crashlocation !== 'undefined' && crashlocationContentBefore !== null) {
        try {
            fs.readdirSync(config.crashlocation).forEach(function(fileName) {
                var file = path.join(config.crashlocation, fileName);
                try {
                    var stat = fs.statSync(file);
                } catch (e) {
                    var stat = false;
                }
                if (stat && stat.isFile() && /^\./i.test(fileName) === false) {
                    if (crashlocationContentBefore.indexOf(file) === -1) {
                        crashes.push(file);
                    }
                }
            });
        } catch (e) {
            consoleLog('[WARN] cannot look for crashes (2):', e);
        }
    }
}

// clear frontend cache
function clearCache(notifyClients) {
    
}

function clearCachedData() {
    if (arguments.length === 0) {
        for (var i in cachedData) {
            try {
                fs.unlinkSync(path.join(config.reportsBasePath, i + '.json'));
            } catch (e) {
                // Doesn't matter
            }
        }
        cachedData = {};
    } else if (arguments.length === 1 && typeof arguments[0] !== 'string') {
        for (var i = 0; i < arguments[0].length; i++) {
            try {
                fs.unlinkSync(path.join(config.reportsBasePath, arguments[0][i] + '.json'));
            } catch (e) {
                // Doesn't matter
            }
            cachedData[arguments[0][i]] = null;
        }
    } else {
        for (var i = 0; i < arguments.length; i++) {
            try {
                fs.unlinkSync(path.join(config.reportsBasePath, arguments[i] + '.json'));
            } catch (e) {
                // Doesn't matter
            }
            cachedData[arguments[i]] = null;
        }
    }
}

// is in debug mode
function isInDebugMode() {
    return (typeof config.debug !== 'undefined' && config.debug === true);
}

// Main: initialize then run given test (as command line argument) or all tests
consoleLog('[INFO] initializing...');
try {
    var statForceRebuild = fs.statSync(path.join(config.reportsBasePath, 'forceRebuild'));
} catch (e) {
    var statForceRebuild = false;
}
try {
    fs.unlinkSync(path.join(config.reportsBasePath, 'forceRebuild'));
} catch (e) {
    // Doesn't matter
}
if (statForceRebuild !== false) {
    forceRebuild = true
}

try {
    var _state = JSON.parse(fs.readFileSync(path.join(config.reportsBasePath, 'state.json')).toString());
    if (typeof _state.relaunch !== 'undefined' && _state.relaunch === true) {
        forceRelaunch = true;
    }
} catch (e) {
    // Doesn't matter
}

currentStatus = getStatus();
previousChangelist = currentStatus.changelist;
cleanDirs();
clearCache();
if (process.argv.length > 2 && process.argv[2] !== 'rebuild') {
    deployingNewWakandaBuild = false;
    downloadingNewWakandaBuild = true;
    downloadingNewWakandaBuildDone = true;
    downloadingNewWakandaBuildExpect = 0;
    deployingNewWakandaInstaller = false;
    downloadingNewWakandaInstaller = true;
    downloadingNewWakandaInstallerDone = true;
    downloadingNewWakandaInstallerExpect = 0;
    deployingNew4DBuild = false;
    downloadingNew4DBuild = true;
    downloadingNew4DBuildDone = true;
    downloadingNew4DBuildExpect = 0;
    exterminate(function() {
        if (process.argv[2] === 'run') {
            standalone = false;
            runFromWeb = false;
            startFrontend();
            startWebSocket();
            consoleLog('[INFO] ready!');
            if (forceRelaunch === true) {
                state = {
                    currentJob: -1,
                    done: [],
                    queue: [],
                    changelist: state.changelist
                };
            } else {
                state = {
                    currentJob: -1,
                    done: [],
                    queue: [],
                    changelist: getCurrentChangelist((typeof process.argv[3] !== 'undefined' && process.argv[3] === 'latest'))
                };
            }

            runLog = [];
            try {
                fs.writeFileSync(path.join(config.reportsBasePath, 'state.json'), JSON.stringify(state));
            } catch (e) {
                consoleLog('[WARN] cannot write current state (6)', e);
            }
            try {
                fs.unlinkSync(path.join(config.reportsBasePath, 'current.json'));
            } catch (e) {
                // Doesn't matter
            }
            frontendReady = true;
            runAll(null, (typeof process.argv[3] !== 'undefined' && process.argv[3] === 'latest'));
        } else if (process.argv[2] === 'resume') {
            standalone = false;
            runFromWeb = false;
            startFrontend();
            startWebSocket();
            consoleLog('[INFO] ready!');
            frontendReady = true;
            runAll(null, (typeof process.argv[3] !== 'undefined' && process.argv[3] === 'latest'));
        } else {
            consoleLog('[INFO] ready!');
            runFromWeb = false;
            frontendReady = true;
            if (/^x\d+$/.test(process.argv[2]) === true) {
                var match = /^x(\d+)$/.exec(process.argv[2]);
                runManual(process.argv.slice(3), true, parseInt(match[1]));
            } else {
                runManual(process.argv.slice(2), true);
            }
        }
    });
} else {
    var actual = [];
    var expected = [];
    try {
        var availables = JSON.parse(fs.readFileSync(path.join(config.reportsBasePath, 'availableTestRuns.json')).toString());
        availables.forEach(function(available) {
            expected.push(parseInt(available.changelist));
        });
    } catch (e) {

    }
    try {
        var dir = path.join(config.reportsBasePath, config.WAKANDA_BRANCH, config.TEST_BRANCH);
        fs.readdirSync(dir).forEach(function(fileName) {
            if (/^[0-9]+$/.test(fileName) === true) {
                actual.push(parseInt(fileName));
            }
        });
    } catch (e) {

    }
    actual = arrayUnique(actual);
    actual.sort();
    expected = arrayUnique(expected);
    expected.sort();
    var resultsHaveError = false;
    if (actual.length !== expected.length) {
        consoleLog('[WARN] error in results - expected length: ' + expected.length + ' / actual length: ' + actual.length);
        resultsHaveError = true;
    } else {
        for (var i = 0; i < actual.length; i++) {
            if (actual[i] !== expected[i]) {
                consoleLog('[WARN] error in results - expected changelist: ' + expected[i] + ' / actual changelist: ' + actual[i]);
                resultsHaveError = true;
                break;
            }
        }
    }
    if ((resultsHaveError === true && forceRebuild === true) || (process.argv.length > 2 && process.argv[2] === 'rebuild')) {
        cachedData.availableTestRuns = null;
        try {
            fs.unlinkSync(path.join(config.reportsBasePath, 'availableTestRuns.json'));
        } catch (e) {
            // Doesn't matter
        }
        if (forceRelaunch === false) {
            try {
                fs.unlinkSync(path.join(config.reportsBasePath, 'state.json'));
            } catch (e) {
                // Doesn't matter
            }
        }
        try {
            fs.unlinkSync(path.join(config.reportsBasePath, 'current.json'));
        } catch (e) {
            // Doesn't matter
        }
        if (resultsHaveError === true && forceRebuild === true) {
            consoleLog('[WARN] rebuilding data (FORCED), this could take some time...');
        } else {
            consoleLog('[WARN] rebuilding data, this could take some time...');
        }
        clearCachedData();
        clearCache();
    }
    standalone = false;
    startFrontend();
    startWebSocket();
    getListOfAvailableTestRuns(function(listOfAvailableTestRuns) {
        var cb = function() {
            consoleLog('[INFO] ready!');
            try {
                var statCurrent = fs.statSync(path.join(config.reportsBasePath, 'current.json'));
            } catch (e) {
                var statCurrent = false;
            }
            try {
                var current = JSON.parse(fs.readFileSync(path.join(config.reportsBasePath, 'current.json')).toString());
            } catch (e) {
                statCurrent = false;
            }
            frontendReady = true;
            if (statCurrent) {
                if (typeof config.automatic !== "undefined" && config.automatic === true) {
                    runAll();
                } else {
                    ask('do you want to retry the previously failed test (' + current.testName + ') and continue the chain? (y/n)'.white.bold, function(answer) {
                        if (/y/i.test(answer) === true) {
                            runAll();
                        } else {
                            try {
                                fs.unlinkSync(path.join(config.reportsBasePath, 'current.json'));
                            } catch (e) {
                                // Doesn't matter
                            }
                            ask('do you want to run all the tests now? (y/n)'.white.bold, function(answer) {
                                if (/y/i.test(answer) === true) {
                                    runAll();
                                } else if (typeof config.hub !== 'undefined' && typeof config.hub.listen !== 'undefined' && config.hub.listen === true) {
                                    hello();
                                    consoleLog('[INFO] waiting for a new build (>' + previousChangelist + ')...');
                                } else {
                                    consoleLog('[WARN] not listening to the Hub and no action given, so there is nothing to do right now...');
                                }
                            });
                        }
                    });
                }
            } else {
                if (typeof config.automatic !== "undefined" && config.automatic === true) {
                    if (typeof config.hub !== 'undefined' && typeof config.hub.listen !== 'undefined' && config.hub.listen === true) {
                        hello();
                        consoleLog('[INFO] waiting for a new build (>' + previousChangelist + ')...');
                    } else {
                        consoleLog('[WARN] not listening to the Hub and no action given, so there is nothing to do right now...');
                        ask('do you want to exit now? (y/n)'.white.bold, function(answer) {
                            if (/y/i.test(answer) === true) {
                                exitGracefully();
                            }
                        });
                    }
                } else {
                    ask('do you want to run all the tests now? (y/n)'.white.bold, function(answer) {
                        if (/y/i.test(answer) === true) {
                            runAll();
                        } else if (typeof config.hub !== 'undefined' && typeof config.hub.listen !== 'undefined' && config.hub.listen === true) {
                            hello();
                            consoleLog('[INFO] waiting for a new build (>' + previousChangelist + ')...');
                        } else {
                            consoleLog('[WARN] not listening to the Hub and no action given, so there is nothing to do right now...');
                            ask('do you want to exit now? (y/n)'.white.bold, function(answer) {
                                if (/y/i.test(answer) === true) {
                                    exitGracefully();
                                }
                            });
                        }
                    });
                }
            }
        };
        if (listOfAvailableTestRuns.length > 0) {
            getGraphDataForTestRun(listOfAvailableTestRuns[0], cb, ((resultsHaveError === true && forceRebuild === true) || (process.argv.length > 2 && process.argv[2] === 'rebuild')));
        } else {
            cb();
        }
    }, ((resultsHaveError === true && forceRebuild === true) || (process.argv.length > 2 && process.argv[2] === 'rebuild')));
}

// Run manual tests
function runManual(pattern, fromCommandLine, nTimes) {
    stopManualTests = false;
    killMainProcesses();
    if (typeof fromCommandLine === 'undefined') {
        fromCommandLine = false;
    }
    if (typeof nTimes === 'undefined') {
        nTimes = 1;
    }
    if (fromCommandLine === true) {
        if (typeof process.argv[process.argv.length - 1] !== 'undefined' && process.argv[process.argv.length - 1] === 'latest') {
            state.changelist = getCurrentChangelist(true);
        } else if (typeof process.argv[process.argv.length - 1] !== 'undefined' && /^\d+$/.test(process.argv[process.argv.length - 1]) === true) {
            state.changelist = parseInt(/^(\d+)$/.exec(process.argv[process.argv.length - 1])[1]);
        }
    } else {
        state.changelist = getCurrentChangelist(true);
    }
    try {
        fs.unlinkSync(path.join(config.reportsBasePath, 'current.json'));
    } catch (e) {
        // Doesn't matter
    }
    if (typeof pattern === 'string') {
        pattern = [pattern];
    }
    var foundTest = [];
    pattern.forEach(function(_path) {
        if (_path.indexOf(path.sep) !== -1) {
            _path = actualPath(_path);
            if (_path !== null) {
                try {
                    var statPath = fs.statSync(_path);
                } catch (e) {
                    var statPath = false;
                }
                if (statPath !== false) {
                    var basePathDev = actualPath(path.join(config.P4_WORKSPACE_PATH, 'RIA', 'tests', 'dev', config.WAKANDA_BRANCH), true);
                    var basePathStable = actualPath(path.join(config.P4_WORKSPACE_PATH, 'depot', 'Wakanda', config.WAKANDA_BRANCH), true);
                    var testBaseName = null;
                    var statMaven = false;
                    var statOther = false;
                    if (_path.indexOf(basePathStable) === 0) {
                        config.TEST_BRANCH = 'stable';
                        testBaseName = _path.replace(basePathStable + path.sep, '').toLowerCase().split(path.sep);
                    }
                    if (testBaseName !== null) {
                        if (statPath.isFile()) {
                            if (path.basename(_path) === 'pom.xml') {
                                _path = path.dirname(_path);
                                testBaseName.pop();
                                statMaven = (true && (typeof config.noJavaTest === 'undefined' || config.noJavaTest === false));
                            } else if (path.basename(_path) === 'pom.json') {
                                _path = path.dirname(_path);
                                testBaseName.pop();
                                statOther = true;
                            } else if (/^test.*\.js$/i.test(path.basename(_path)) === true) {
                                testBaseName.pop();
                                var match = /^test(.*)\.js$/i.exec(path.basename(_path));
                                if (match[1] === '') {
                                    if (config.TEST_BRANCH === 'dev') {
                                        foundTest.push((testBaseName.join('_') + '_main').replace(/_+/g, '_'));
                                    } else {
                                        foundTest.push((testBaseName[0] + '_' + testBaseName.slice(2).join('_') + '_main').replace(/_+/g, '_'));
                                    }
                                } else {
                                    if (config.TEST_BRANCH === 'dev') {
                                        foundTest.push((testBaseName.join('_') + '_' + match[1].toLowerCase()).replace(/_+/g, '_'));
                                    } else {
                                        foundTest.push((testBaseName[0] + '_' + testBaseName.slice(2).join('_') + '_' + match[1].toLowerCase()).replace(/_+/g, '_'));
                                    }
                                }
                            }
                        }
                        if (statMaven || statOther || statPath.isDirectory()) {
                            if (statMaven === false) {
                                try {
                                    statMaven = fs.statSync(actualPath(path.join(_path, 'pom.xml'), true));
                                } catch (e) {
                                    statMaven = false;
                                }
                            }
                            if (statOther === false) {
                                try {
                                    statOther = fs.statSync(actualPath(path.join(_path, 'pom.json'), true));
                                } catch (e) {
                                    statOther = false;
                                }
                            }
                            if (statMaven && (typeof config.noJavaTest === 'undefined' || config.noJavaTest === false)) {
                                if (config.TEST_BRANCH === 'dev') {
                                    foundTest.push((testBaseName.join('_') + '_main').replace(/_+/g, '_'));
                                } else {
                                    foundTest.push((testBaseName[0] + '_' + testBaseName.slice(2).join('_') + '_main').replace(/_+/g, '_'));
                                }
                            } else if (statOther) {
                                try {
                                    fs.readdirSync(_path).forEach(function(fileName) {
                                        if (/^test.*\.js$/i.test(fileName) === true) {
                                            var match = /^test(.*)\.js$/i.exec(fileName);
                                            if (match[1] === '') {
                                                if (config.TEST_BRANCH === 'dev') {
                                                    foundTest.push((testBaseName.join('_') + '_main').replace(/_+/g, '_'));
                                                } else {
                                                    foundTest.push((testBaseName[0] + '_' + testBaseName.slice(2).join('_') + '_main').replace(/_+/g, '_'));
                                                }
                                            } else {
                                                if (config.TEST_BRANCH === 'dev') {
                                                    foundTest.push((testBaseName.join('_') + '_' + match[1].toLowerCase()).replace(/_+/g, '_'));
                                                } else {
                                                    foundTest.push((testBaseName[0] + '_' + testBaseName.slice(2).join('_') + '_' + match[1].toLowerCase()).replace(/_+/g, '_'));
                                                }
                                            }
                                        }
                                    });
                                } catch (e) {

                                }
                            }
                        }
                    }
                }
            }
        } else {
            var testNameFilter = new RegExp('^' + _path.replace(/\*/ig, '.*') + '$', 'i');
            foundTest = foundTest.concat(getAvailableJobs(function(item) {
                return testNameFilter.test(item);
            }));
        }
    });
    if (foundTest.length === 0) {
        consoleLog('[ERROR] erroneous path or no test found:', pattern);
        if (fromCommandLine === true) {
            exitGracefully();
        }
    } else {
        foundTest = foundTest.map(function(item) {
            return item.replace(/_core/ig, '_main').replace(/_main_main/ig, '_main').replace(/_+/g, '_');
        });
        var nTimesStr = ''.grey;
        if (nTimes > 1) {
            nTimesStr = (' ' + nTimes + ' times').yellow;
        }
        if (foundTest.length === 1) {
            consoleLog('[INFO] will run the following test: '.grey + ''.white + foundTest.join(''.white + ', '.grey) + nTimesStr);
        } else {
            consoleLog('[INFO] will run the following '.grey + foundTest.length.toString().white + ' tests: '.grey + ''.white + foundTest.join(''.white + ', '.grey) + nTimesStr);
        }
        var finalFoundTest = foundTest
        for (var cc = 1; cc < nTimes; cc++) {
            finalFoundTest = finalFoundTest.concat(foundTest);
        }
        runningManual = true;
        runningManualQueue = finalFoundTest;
        runningManualDone = [];
        runningManualCurrentJob = null;
        var summary = [];
        async.eachSeries(
            finalFoundTest,
            function(testName, serieCallback) {
                runningManualCurrentJob = testName;
                setTimeout(function() {
                    runTest(testName, function(res) {
                        runningManualDone.push(res.testName);
                        stopMonitoring();
                        try {
                            fs.writeFileSync(path.join(res.resultDir, 'runlog.json'), JSON.stringify(res));
                        } catch (e) {
                            consoleLog('[WARN] cannot write job runlog (2)', e);
                        }
                        if (typeof res.pom !== 'undefined' && res.pom) {
                            try {
                                fs.writeFileSync(path.join(res.resultDir, 'pom.json'), JSON.stringify(res.pom));
                            } catch (e) {
                                consoleLog('[WARN] cannot write job pom (2)', e);
                            }
                        }
                        try {
                            fs.unlinkSync(path.join(res.resultDir, '.auto'));
                        } catch (e) {
                            // Doesn't matter
                        }
                        try {
                            fs.writeFileSync(path.join(res.resultDir, '.manual'), 'true');
                        } catch (e) {
                            consoleLog('[WARN] cannot write job .manual flag (1)', e);
                        }
                        var status = 'UNKNOWN'.grey;
                        if (res.status === null) {
                            status = 'FAILURE'.red;
                        } else if (res.status === false) {
                            status = 'UNSTABLE'.yellow;
                        } else if (res.status === true) {
                            status = 'SUCCESS'.green;
                        }
                        consoleLog('[INFO] '.grey + res.testName.bold.white + ' --> '.grey + status.bold);
                        summary.push('[INFO] '.grey + res.testName.bold.white + ' --> '.grey + status.bold);
                        try {
                            var report = JSON.parse(fs.readFileSync(path.join(res.resultDir, 'report.json')).toString());
                            var reportString = '[INFO] '.grey;
                            reportString += ('passed: ' + report.abstract.passed).green;
                            reportString += ', '.grey;
                            reportString += ('failed: ' + report.abstract.failures).red;
                            reportString += ', '.grey;
                            reportString += ('skipped: ' + report.abstract.skipped).grey;
                            reportString += ', '.grey;
                            reportString += ('total: ' + report.abstract.total).white;
                            consoleLog(reportString + ''.grey);
                            summary.push(reportString + ''.grey);
                            if (report.abstract.failures > 0) {
                                reportString = '[INFO] failed tests: '.grey;
                                var failures = [];
                                report.failed.forEach(function(failure) {
                                    failures.push(failure.name.red);
                                });
                                reportString += failures.join(', '.grey);
                                consoleLog(reportString + ''.grey);
                                summary.push(reportString + ''.grey);
                            }
                        } catch (e) {
                            consoleLog('[WARN] JSON report not available');
                        }
                        if (res.resultDir) {
                            consoleLog('[INFO] results are available in the folder ' + res.resultDir.bold.white + ''.grey);
                            summary.push('[INFO] results are available in the folder ' + res.resultDir.bold.white + ''.grey);
                        }
                        var cleanup = temp.cleanup();
                        if (typeof res.tmpDir !== 'undefined') {
                            try {
                                rmdir(res.tmpDir);
                            } catch (e) {
                                // Doesn't matter
                            }
                        }
                        consoleLog('[INFO] test ended at ' + new Date());
                        killMainProcesses();
                        exterminate(function() {
                            getCrashlocationContentAfter();
                            getProcessListDiffAfter(function(diff) {
                                if (diff !== null && (diff.less.length > 0 || diff.more.length > 0)) {
                                    var diffLog = '';
                                    if (diff.less.length > 0) {
                                        diffLog += '-- Lost Processes (killed during the test):\n';
                                        diff.less.forEach(function(proc) {
                                            diffLog += '\t' + proc.pid + '\t' + proc.cmd + '\n';
                                        });
                                        diffLog += ' \n\n';
                                    }
                                    if (diff.more.length > 0) {
                                        diffLog += '++ Additional Processes (spawned during the test):\n';
                                        diff.more.forEach(function(proc) {
                                            diffLog += '\t' + proc.pid + '\t' + proc.cmd + '\n';
                                        });
                                        diffLog += ' \n\n';
                                    }
                                    try {
                                        fs.writeFileSync(path.join(res.resultDir, 'procdiff.txt'), diffLog);
                                    } catch (e) {
                                        consoleLog('[WARN] cannot archive process diff (2)', e);
                                    }
                                }
                                if (crashes.length > 0) {
                                    consoleLog('[WARN] test ' + res.testName + ' produced ' + crashes.length + ' crash(es)');
                                    summary.push('[WARN] test ' + res.testName + ' produced ' + crashes.length + ' crash(es)');
                                    for (var i = 0; i < crashes.length; i++) {
                                        if (/server/i.test(crashes[i])) {
                                            var crashName = 'server_crash_' + (i + 1) + path.extname(crashes[i]);
                                        } else if (/studio/i.test(crashes[i])) {
                                            var crashName = 'studio_crash_' + (i + 1) + path.extname(crashes[i]);
                                        } else if (/4d/i.test(crashes[i])) {
                                            var crashName = '4d_crash_' + (i + 1) + path.extname(crashes[i]);
                                        } else {
                                            var crashName = 'other_crash_' + (i + 1) + path.extname(crashes[i]);
                                        }
                                        try {
                                            copyFileSync(crashes[i], path.join(res.resultDir, crashName));
                                        } catch (e) {
                                            consoleLog('[WARN] cannot archive crash log', e);
                                        }
                                    }
                                }
                                if (stopManualTests === true) {
                                    serieCallback(true);
                                } else {
                                    serieCallback(null);
                                }
                            });
                        });
                    }, false);
                }, 125);
            },
            function(err) {
                if (finalFoundTest.length > 1) {
                    consoleLog('[INFO] '.grey + '--------'.white + ''.grey);
                    consoleLog('[INFO] '.grey + 'SUMMARY:'.white + ''.grey);
                    consoleLog('[INFO] '.grey + '--------'.white + ''.grey);
                    summary.forEach(function(log) {
                        consoleLog(log);
                    });
                }
                runningManual = false;
                runningManualQueue = [];
                runningManualDone = [];
                runningManualCurrentJob = null;
                running = false;
                hello();
                if (shutDown == false && fromCommandLine === true) {
                    exitGracefully();
                } else {
                    startMonitoring();
                    killMainProcesses();
                    exterminate(function() {
                        consoleLog('[INFO] done.');
                        stopMonitoring();
                        doShutdown(true);
                    });
                }
            }
        );
    }
}

// clean working dirs
function cleanDirs() {
    if (config !== null && typeof config.BUILD_TEMP_DIR !== 'undefined' && standalone === false && (typeof config.deepCleaning === 'undefined' || config.deepCleaning === true)) {
        rmdir(config.BUILD_TEMP_DIR, true);
    }
    if (config !== null && typeof config.BUILD_TEST_DIR !== 'undefined' && standalone === false && (typeof config.deepCleaning === 'undefined' || config.deepCleaning === true)) {
        var list = fs.readdirSync(config.BUILD_TEST_DIR).filter(function(item) {
            return (/^\d+$/.test(item));
        }).sort();
        var maxBuilds = 5;
        if (list.length > maxBuilds) {
            for (var i = 0; i < Math.min(maxBuilds, list.length); i++) {
                rmdir(path.join(config.BUILD_TEST_DIR, list[i]));
            }
        }
    }
}

// console.log with flavours
function consoleLog() {
    var log = '';
    var asError = false;
    var asWarn = false;
    var asStdout = false;
    var asStderr = false;
    for (var i = 0; i < arguments.length; i++) {
        var entry = arguments[i];
        if ((/\[ERROR\]/.test(entry) === true) && (/\[STDOUT\]/.test(entry) === true)) {
            entry = entry.replace(/\[stdout\]\s*/ig, '');
            entry = entry.replace(/\[error\]\s*/ig, '[STDERR]');
        }
        if (/\[ERROR\]/.test(entry) === true) {
            asError = true;
        } else if (/\[WARN\]/.test(entry) === true) {
            asWarn = true;
        } else if (/\[STDOUT\]/.test(entry) === true) {
            asStdout = true;
        } else if (/\[STDERR\]/.test(entry) === true) {
            asStderr = true;
        }
        log += entry + ' ';
    }
    log = log.replace(/^\s+/g, '').replace(/\s+$/g, '');
    if (asStdout === true) {
        log = log.cyan;
    } else if (asStderr === true) {
        log = log.red;
    } else if (asError === true) {
        log = log.magenta;
    } else if (asWarn === true) {
        log = log.blue;
    } else {
        log = log.grey;
    }
    if (standalone === false && io !== null) {
        try {
            var myAnsi = new ansi();
            var logAsHtml = myAnsi.toHtml(log.replace(/</g, '&lt;').replace(/>/g, '&gt;'));
            htmlLog.push(logAsHtml);
            htmlLog = htmlLog.slice(-500);
            io.sockets.emit('log', logAsHtml);
        } catch (e) {

        }
    }
    if (standalone === true || (!asStdout && !asStderr)) {
        var now = new Date();
        var time = (now.getHours() < 10 ? '0' + now.getHours() : now.getHours()) + ':' + (now.getMinutes() < 10 ? '0' + now.getMinutes() : now.getMinutes()) + ':' + (now.getSeconds() < 10 ? '0' + now.getSeconds() : now.getSeconds()) + '.' + (now.getMilliseconds() < 10 ? '00' + now.getMilliseconds() : ((now.getMilliseconds() < 100 ? '0' + now.getMilliseconds() : now.getMilliseconds())));
        if (!asStdout && !asStderr) {
            console.log(time.grey + ' - '.grey + log);
        }
        if (running === true && !asStdout && !asStderr) {
            try {
                var myAnsi = new ansi();
                var logAsHtml = myAnsi.toHtml((time.grey + ' - '.grey + log).replace(/</g, '&lt;').replace(/>/g, '&gt;'));
                fs.appendFileSync(path.join(config.reportsBasePath, config.WAKANDA_BRANCH, config.TEST_BRANCH, config.CHANGELIST.toString(), 'runlog.html'), logAsHtml + '<br/>');
            } catch (e) {

            }
        }
    }
}

// Setup HTTP "proxy" for Selenium tests (Windows and Mac only)
function setUpSeleniumProxy(studioFolder, pom, dir) {
    if (typeof studioFolder === 'undefined') {
        var _studioPaths = getCurrentStudioPath();
        studioFolder = _studioPaths.folder;
    }
    try {
        var initProxySelenium = false;
        if (proxySelenium === null) {
            initProxySelenium = true;
        }
        if (initProxySelenium === true) {
            proxySelenium = express();
            proxySelenium.use(function noCachePlease(req, res, next) {
                res.header("Cache-Control", "no-cache, private, no-store, must-revalidate, max-stale=0, post-check=0, pre-check=0");
                res.header("Pragma", "no-cache");
                res.header("Expires", -1);
                next();
            });
        }
        consoleLog('[INFO] setup Selenium proxy to ' + studioFolder);
        proxySelenium.use('/eme', express.static(path.join(studioFolder, 'Resources', 'Web Components', 'emEditor'), {
            maxAge: 0
        }));
        proxySelenium.use('/guid', express.static(path.join(studioFolder, 'Resources', 'Web Components', 'GUIDesigner'), {
            maxAge: 0
        }));
        proxySelenium.use('/Resources', express.static(path.join(studioFolder, 'Resources'), {
            maxAge: 0
        }));
        proxySelenium.use('/common', express.static(path.join(studioFolder, 'Resources', 'Web Components', 'common'), {
            maxAge: 0
        }));
        proxySelenium.use('/Web Components', express.static(path.join(studioFolder, 'Resources', 'Web Components'), {
            maxAge: 0
        }));
        proxySelenium.use('/walib', express.static(path.join(studioFolder, 'Resources', 'Web Components', 'walib'), {
            maxAge: 0
        }));
        proxySelenium.use('/icons', express.static(path.join(studioFolder, 'Resources', 'Web Components', 'GUIDesigner', 'icons'), {
            maxAge: 0
        }));
        proxySelenium.use('/', express.static(path.join(studioFolder, 'Resources'), {
            maxAge: 0
        }));
        if (typeof pom !== 'undefined' && typeof dir !== 'undefined' && typeof pom.virtualPath !== 'undefined' && pom.virtualPath.length !== 'undefined' && pom.virtualPath.length > 0) {
            pom.virtualPath.forEach(function(vPath) {
                consoleLog('[INFO] setup virtual path /' + vPath.name + ' to ' + path.join(dir, vPath.path));
                proxySelenium.use('/' + vPath.name, express.static(path.join(dir, vPath.path), {
                    maxAge: 0
                }));
                if (/widgets_custom/i.test(vPath.name) === true) {
                    consoleLog('[INFO] setup virtual path /widgets-custom to ' + path.join(dir, vPath.path));
                    proxySelenium.use('/widgets-custom', express.static(path.join(dir, vPath.path), {
                        maxAge: 0
                    }));
                    var widgetsPath = path.join(getUserHome(), 'Documents')
                    try {
                        fs.mkdirSync(widgetsPath);
                    } catch (e) {

                    }
                    widgetsPath = path.join(widgetsPath, 'Wakanda');
                    try {
                        fs.mkdirSync(widgetsPath);
                    } catch (e) {

                    }
                    widgetsPath = path.join(widgetsPath, 'Widgets');
                    try {
                        fs.mkdirSync(widgetsPath);
                    } catch (e) {

                    }
                    try {
                        var list = fs.readdirSync(widgetsPath);
                        for (var i = 0; i < list.length; i++) {
                            var filename = path.join(widgetsPath, list[i]);
                            try {
                                fs.unlinkSync(filename);
                            } catch (e) {
                                // Doesn't matter
                            }
                        }
                    } catch (e) {
                        // Doesn't matter
                    }
                    ncp(path.join(dir, vPath.path), widgetsPath + path.sep, function(err) {
                        if (err) {
                            consoleLog('[WARN] cannot copy custom widgets into', widgetsPath, err);
                        } else {
                            consoleLog('[INFO] custom widgets copied into', widgetsPath);
                        }
                    });
                }
            });
        }
        if (initProxySelenium === true) {
            consoleLog('[INFO] Selenium proxy starts listening to port 9100');
            proxySelenium.listen(9100);
        }
    } catch (e) {
        consoleLog('[ERROR] cannot setup Selenium proxy (1):', e);
    }
}

// get home
function getUserHome() {
    return process.env.HOME || process.env.HOMEPATH || process.env.USERPROFILE;
}

// MD5
function createHash(req) {
    var authenticated = false;
    req.query.callback = null;
    req.query._ = null;
    return crypto.createHash('md5').update(JSON.stringify({
        query: req.query,
        params: req.params,
        auth: authenticated
    })).digest('hex');
}

// Monitoring
function startMonitoring() {
    
}

function stopMonitoring() {
    
}

// Escape string for regexp
function escapeRegExp(str) {
    return str.replace(/[\-\[\]\/\{\}\(\)\*\+\?\.\\\^\$\|]/g, "\\$&");
}

// Setup HTTP frontend
function startFrontend() {
    
}

function getDuration(duration, ms, prefix) {
    if (typeof prefix === 'undefined') {
        prefix = '<i class="icon-clock"></i>';
    }
    if (typeof ms === 'undefined') {
        ms = false;
    }
    if (isNaN(duration) || duration < 0) {
        return '';
    }
    if (ms && duration < 1) {
        return prefix + '<1ms';
    }
    if (ms && duration < 1000) {
        return prefix + duration + 'ms';
    }
    if (duration < 1000) {
        return prefix + '<1s';
    }
    var d = duration / 1000;
    var j = Math.floor(d / 86400);
    var h = Math.floor(d % 86400 / 3600);
    var m = Math.floor(d % 3600 / 60);
    var s = Math.floor(d % 3600 % 60);
    return prefix + ((j > 0 ? j + 'd ' : '') + (h > 0 ? h + 'h ' : '') + (m > 0 ? (h > 0 && m < 10 ? '0' : '') + m + 'mn ' : '') + (s > 0 ? (m > 0 && s < 10 ? '0' : '') + s + 's' : ''));
}

// Setup WebSocket stuff
function startWebSocket() {
    
}

// Say hello to the hub
function hello(silent) {
    
}

// Say bye to the hub
function bye() {
    
}

// Capitalize
function capitalize(str, ellipsis) {
    if (typeof ellipsis === "undefined") {
        ellipsis = false;
    }
    str = new String(str);
    if (ellipsis === true && str.length > 18) {
        str = str.substr(0, 7) + '...' + str.substr(-7);
    }
    if (str.length <= 4) return str.toUpperCase();
    return str.replace(/\w\S*/g, function(txt) {
        return txt.charAt(0).toUpperCase() + txt.substr(1).toLowerCase();
    });
}

function getPomForTest(testName) {
    var testPom = null;
    var stack = testName.split('_');
    var parentPath = stack.slice(0, stack.length - 1);
    parentPath = parentPath.map(function(elt) {
        if (elt === 'main') {
            return 'core';
        }
        return elt;
    });
    try {
        parentPath = actualPath(path.join(config.P4_WORKSPACE_PATH, 'depot', 'Wakanda', config.WAKANDA_BRANCH, parentPath[0], 'tests', parentPath.slice(1).join(path.sep)));
    } catch (e) {
        return null;
    }
    if (stack[stack.length - 1] === 'main') {
        try {
            var statMaven = fs.statSync(actualPath(path.join(parentPath, 'pom.xml')));
        } catch (e) {
            var statMaven = false;
        }
        try {
            var statOther = fs.statSync(actualPath(path.join(parentPath, 'pom.json')));
        } catch (e) {
            var statOther = false;
        }
        try {
            var statNewArchi = fs.statSync(actualPath(path.join(parentPath, 'test.conf.json')));
        } catch (e) {
            var statNewArchi = false;
        }
        try {
            var statMaven2 = fs.statSync(actualPath(path.join(parentPath, 'core', 'pom.xml')));
        } catch (e) {
            var statMaven2 = false;
        }
        try {
            var statOther2 = fs.statSync(actualPath(path.join(parentPath, 'core', 'pom.json')));
        } catch (e) {
            var statOther2 = false;
        }
        try {
            var statNewArchi2 = fs.statSync(actualPath(path.join(parentPath, 'core', 'test.conf.json')));
        } catch (e) {
            var statNewArchi2 = false;
        }
        if (statNewArchi && statNewArchi.isFile()) {
            try {
                testPom = JSON.parse(fs.readFileSync(actualPath(path.join(parentPath, 'test.conf.json'))).toString());
            } catch (e) {
                testPom = null;
            }
        } else if (statNewArchi2 && statNewArchi2.isFile()) {
            parentPath = actualPath(path.join(parentPath, 'core'));
            try {
                testPom = JSON.parse(fs.readFileSync(actualPath(path.join(parentPath, 'test.conf.json'))).toString());
            } catch (e) {
                testPom = null;
            }
        } else if (statMaven && statMaven.isFile()) {
            pom = fs.readFileSync(actualPath(path.join(parentPath, 'pom.xml'))).toString();
            try {
                parseString(pom, function(err, rawresult) {
                    if (!err) {
                        testPom = {};
                        for (var prop in rawresult.project.properties[0]) {
                            if (/^virtualpath$/i.test(prop) === true) {
                                if (typeof testPom.virtualPath === 'undefined') {
                                    testPom.virtualPath = [];
                                }
                                testPom.virtualPath.push({
                                    name: rawresult.project.properties[0][prop][0].$.name,
                                    path: rawresult.project.properties[0][prop][0].$.path,
                                });
                            } else {
                                if (/^\d+$/.test(rawresult.project.properties[0][prop][0]) === true) {
                                    testPom[prop.replace('jenkins.', '').toLowerCase()] = parseInt(rawresult.project.properties[0][prop][0]);
                                } else {
                                    testPom[prop.replace('jenkins.', '').toLowerCase()] = rawresult.project.properties[0][prop][0].toLowerCase();
                                }
                            }
                        }
                        testPom.kind = 'maven';
                    }
                });
            } catch (e) {
                testPom = null;
            }
        } else if (statOther && statOther.isFile()) {
            try {
                testPom = JSON.parse(fs.readFileSync(actualPath(path.join(parentPath, 'pom.json'))).toString());
            } catch (e) {
                testPom = null;
            }
        } else if (statMaven2 && statMaven2.isFile()) {
            parentPath = actualPath(path.join(parentPath, 'core'));
            pom = fs.readFileSync(actualPath(path.join(parentPath, 'pom.xml'))).toString();
            try {
                parseString(pom, function(err, rawresult) {
                    if (!err) {
                        testPom = {};
                        for (var prop in rawresult.project.properties[0]) {
                            if (/^virtualpath$/i.test(prop) === true) {
                                if (typeof testPom.virtualPath === 'undefined') {
                                    testPom.virtualPath = [];
                                }
                                testPom.virtualPath.push({
                                    name: rawresult.project.properties[0][prop][0].$.name,
                                    path: rawresult.project.properties[0][prop][0].$.path,
                                });
                            } else {
                                if (/^\d+$/.test(rawresult.project.properties[0][prop][0]) === true) {
                                    testPom[prop.replace('jenkins.', '').toLowerCase()] = parseInt(rawresult.project.properties[0][prop][0]);
                                } else {
                                    testPom[prop.replace('jenkins.', '').toLowerCase()] = rawresult.project.properties[0][prop][0].toLowerCase();
                                }
                            }
                        }
                        testPom.kind = 'maven';
                    }
                });
            } catch (e) {
                testPom = null;
            }
        } else if (statOther2 && statOther2.isFile()) {
            parentPath = actualPath(path.join(parentPath, 'core'));
            try {
                testPom = JSON.parse(fs.readFileSync(actualPath(path.join(parentPath, 'pom.json'))).toString());
            } catch (e) {
                testPom = null;
            }
        }
    } else {
        try {
            var statNewArchi = fs.statSync(actualPath(path.join(parentPath, 'test.conf.json')));
        } catch (e) {
            var statNewArchi = false;
        }
        try {
            var statOther = fs.statSync(actualPath(path.join(parentPath, 'pom.json')));
        } catch (e) {
            var statOther = false;
        }
        if (statNewArchi && statNewArchi.isFile()) {
            try {
                testPom = JSON.parse(fs.readFileSync(actualPath(path.join(parentPath, 'test.conf.json'))).toString());
            } catch (e) {
                testPom = null;
            }
        } else if (statOther && statOther.isFile()) {
            try {
                testPom = JSON.parse(fs.readFileSync(actualPath(path.join(parentPath, 'pom.json'))).toString());
            } catch (e) {
                testPom = null;
            }
        }
    }
    if (testPom !== null) {
        var testUUID = null;
        try {
            var statUUID = fs.statSync(actualPath(path.join(parentPath, 'uuid')));
        } catch (e) {
            var statUUID = false;
            consoleLog('[WARN] UUID not found (2)');
        }
        if (statUUID && statUUID.isFile()) {
            try {
                testUUID = fs.readFileSync(actualPath(path.join(parentPath, 'uuid'))).toString();
            } catch (e) {
                consoleLog('[WARN] cannot read UUID (2)');
            }
        }
        testPom.uuid = testUUID;
    }
    return testPom;
}

// Get the graph data for the given test run {productBranch, testBranch, changelist}
function getGraphDataForTestRun(testRun, callback, forceRefresh) {
    callback(null);
}

// Get the list of available completed test runs
function getListOfAvailableTestRuns(callback, forceRefresh) {
    if (typeof forceRefresh === 'undefined') {
        forceRefresh = false;
    }
    if (forceRefresh === true || typeof cachedData.availableTestRuns === 'undefined' || cachedData.availableTestRuns === null) {
        try {
            var stat = fs.statSync(path.join(config.reportsBasePath, 'availableTestRuns.json'));
        } catch (e) {
            var stat = false;
        }
        if (forceRefresh === true || stat === false) {
            var expected = getAvailableJobs();
            var completed = findFiles(config.reportsBasePath, /^runlog\.json$/, /^[^_]+$/);
            cachedData.availableTestRuns = [];
            if (completed.length > 0) {
                completed.forEach(function(item) {
                    try {
                        if (forceRefresh === true || stat === false) {
                            var log = [];
                            var actual = [];
                            var dir = path.dirname(item);
                            fs.readdirSync(dir).forEach(function(fileName) {
                                var file = dir + path.sep + fileName;
                                try {
                                    var _stat = fs.statSync(file);
                                } catch (e) {
                                    var _stat = false;
                                }
                                if (_stat && _stat.isDirectory()) {
                                    var autos = findFiles(file, /^\.auto$/);
                                    var latestAutoDir = [];
                                    autos.forEach(function(auto) {
                                        latestAutoDir.push(path.dirname(auto));
                                    })
                                    latestAutoDir.sort();
                                    if (latestAutoDir.length > 0) {
                                        var reportDir = latestAutoDir[latestAutoDir.length - 1];
                                        try {
                                            var reportData = JSON.parse(fs.readFileSync(path.join(reportDir, 'runlog.json')).toString());
                                            log.push({
                                                name: reportData.testName,
                                                start: reportData.start,
                                                end: reportData.end,
                                                duration: reportData.duration,
                                                status: reportData.status,
                                                dir: reportDir
                                            });
                                            actual.push(reportData.testName);
                                        } catch (e) {

                                        }
                                    }
                                }
                            });
                            if (expected.length > actual.length) {
                                expected.forEach(function(item) {
                                    if (actual.indexOf(item) === -1) {
                                        log.push({
                                            name: item,
                                            start: null,
                                            end: null,
                                            duration: 0,
                                            status: null,
                                            dir: null
                                        });
                                    }
                                });
                            }
                            fs.writeFileSync(item, JSON.stringify(log));
                        } else {
                            var log = JSON.parse(fs.readFileSync(item).toString());
                        }
                        log.sort(function(a, b) {
                            if (a.start === null) {
                                return 1;
                            }
                            try {
                                var as = new Date(a.start);
                                try {
                                    var bs = new Date(b.start);
                                    if (as.getTime() < bs.getTime()) {
                                        return -1;
                                    }
                                    if (as.getTime() > bs.getTime()) {
                                        return 1;
                                    }
                                    return 0;
                                } catch (e) {
                                    return -1;
                                }
                            } catch (e) {
                                return 1;
                            }
                        });
                        cachedData.availableTestRuns.push({
                            log: log,
                            inprogress: false,
                            basePath: path.dirname(item),
                            changelist: parseInt(path.basename(path.dirname(item))),
                            testBranch: path.basename(path.dirname(path.dirname(item))),
                            productBranch: path.basename(path.dirname(path.dirname(path.dirname(item)))),
                            score: (log.reduce(function(previousValue, currentValue, index, array) {
                                if (typeof previousValue === 'number') {
                                    return previousValue + (currentValue.status === true ? 1 : 0);
                                } else {
                                    return (previousValue.status === true ? 1 : 0);
                                }
                            }) / log.length)
                        });
                    } catch (e) {
                        // Doesn't matter
                    }
                });
                async.eachSeries(
                    cachedData.availableTestRuns,
                    function(item, serieCallback) {
                        if (typeof item.date === 'undefined' || item.date === null) {
                            getChangelistDate(item.changelist, function(date) {
                                item.date = date,
                                serieCallback(null);
                            });
                        } else {
                            serieCallback(null);
                        }
                    },
                    function(err) {
                        cachedData.availableTestRuns.sort(function(a, b) {
                            if (a.changelist < b.changelist) {
                                return 1;
                            } else if (a.changelist > b.changelist) {
                                return -1;
                            } else {
                                return 0;
                            }
                        });
                        fs.writeFileSync(path.join(config.reportsBasePath, 'availableTestRuns.json'), JSON.stringify(cachedData.availableTestRuns));
                        wrapAvailableTestsRuns(cachedData.availableTestRuns, callback);
                    }
                );
            } else {
                wrapAvailableTestsRuns(cachedData.availableTestRuns, callback);
            }
        } else {
            cachedData.availableTestRuns = JSON.parse(fs.readFileSync(path.join(config.reportsBasePath, 'availableTestRuns.json')).toString());
            wrapAvailableTestsRuns(cachedData.availableTestRuns, callback);
        }
    } else {
        wrapAvailableTestsRuns(cachedData.availableTestRuns, callback);
    }
}

function wrapAvailableTestsRuns(availableTestRuns, callback) {
    var baseDir = path.join(config.reportsBasePath, config.WAKANDA_BRANCH, config.TEST_BRANCH);
    var hasAddition = false;
    var expected = null;
    var changelists = [];
    availableTestRuns.forEach(function(item) {
        changelists.push(item.changelist.toString());
    });
    try {
        fs.readdirSync(baseDir).forEach(function(fileName) {
            if (/^\d+$/.test(fileName) && changelists.indexOf(fileName) === -1) {
                if (expected === null) {
                    expected = getAvailableJobs();
                }
                if (running === true && runningManual === false && typeof config.CHANGELIST !== 'undefined' && config.CHANGELIST.toString() === fileName) {
                    hasAddition = true;
                    var log = [];
                    var actual = [];
                    var dir = path.join(baseDir, fileName);
                    fs.readdirSync(dir).forEach(function(fileName) {
                        var file = dir + path.sep + fileName;
                        try {
                            var _stat = fs.statSync(file);
                        } catch (e) {
                            var _stat = false;
                        }
                        if (_stat && _stat.isDirectory()) {
                            var autos = findFiles(file, /^\.auto$/);
                            var latestAutoDir = [];
                            autos.forEach(function(auto) {
                                latestAutoDir.push(path.dirname(auto));
                            })
                            latestAutoDir.sort();
                            if (latestAutoDir.length > 0) {
                                var reportDir = latestAutoDir[latestAutoDir.length - 1];
                                try {
                                    var reportData = JSON.parse(fs.readFileSync(path.join(reportDir, 'runlog.json')).toString());
                                    log.push({
                                        name: reportData.testName,
                                        start: reportData.start,
                                        end: reportData.end,
                                        duration: reportData.duration,
                                        status: reportData.status,
                                        dir: reportDir
                                    });
                                    actual.push(reportData.testName);
                                } catch (e) {

                                }
                            }
                        }
                    });
                    if (expected.length > actual.length) {
                        expected.forEach(function(item) {
                            if (actual.indexOf(item) === -1) {
                                log.push({
                                    name: item,
                                    start: null,
                                    end: null,
                                    duration: 0,
                                    status: null,
                                    dir: null
                                });
                            }
                        });
                    }
                    availableTestRuns.push({
                        log: log,
                        inprogress: true,
                        basePath: baseDir,
                        changelist: config.CHANGELIST,
                        testBranch: config.TEST_BRANCH,
                        productBranch: config.WAKANDA_BRANCH,
                        score: (log.reduce(function(previousValue, currentValue, index, array) {
                            if (typeof previousValue === 'number') {
                                return previousValue + (currentValue.status === true ? 1 : 0);
                            } else {
                                return (previousValue.status === true ? 1 : 0);
                            }
                        }) / log.length)
                    });
                } else {
                    // TODO: .manual 
                }
            }
        });
    } catch (e) {

    }
    if (hasAddition === true) {
        async.eachSeries(
            availableTestRuns,
            function(item, serieCallback) {
                if (typeof item.date === 'undefined' || item.date === null) {
                    getChangelistDate(item.changelist, function(date) {
                        item.date = date,
                        serieCallback(null);
                    });
                } else {
                    serieCallback(null);
                }
            },
            function(err) {
                availableTestRuns.sort(function(a, b) {
                    // TODO: don't order by changelist for manual!
                    if (a.changelist < b.changelist) {
                        return 1;
                    } else if (a.changelist > b.changelist) {
                        return -1;
                    } else {
                        return 0;
                    }
                });
                callback(availableTestRuns);
            }
        );
    } else {
        callback(availableTestRuns);
    }
}

function killMainProcesses() {
    if (p4Process !== null && p4Process.pid > 0 && p4Process.pid != process.pid) {
        consoleLog('[WARN] terminate a Perforce process (PID ' + p4Process.pid + ')');
        p4Process.kill('SIGKILL');
    }
    if (FourDServerProcess !== null && FourDServerProcess.pid > 0 && FourDServerProcess.pid != process.pid) {
        consoleLog('[WARN] terminate a 4D Server process (PID ' + FourDServerProcess.pid + ')');
        FourDServerProcess.kill('SIGKILL');
    }
    if (mavenProcess !== null && mavenProcess.pid > 0 && mavenProcess.pid != process.pid) {
        consoleLog('[WARN] terminate a Maven process (PID ' + mavenProcess.pid + ')');
        psTree(mavenProcess.pid, function(err, children) {
            children.forEach(function(p) {
                if (p.PID > 0 && p.PID != process.pid) {
                    consoleLog('[WARN] terminate a Maven child process (PID ' + p.PID + ')');
                    if (isWindows()) {
                        exec('taskkill /pid ' + p.PID + ' /T /F');
                    } else {
                        spawn('kill', ['-9', p.PID]);
                    }
                }
            });
        });
        mavenProcess.kill('SIGKILL');
    }
    if (serverProcess !== null && serverProcess.pid > 0 && serverProcess.pid != process.pid) {
        consoleLog('[WARN] terminate a Wakanda Server process (Web - PID ' + serverProcess.pid + ')');
        serverProcess.kill('SIGKILL');
    }
    if (CLIProcess !== null && CLIProcess.pid > 0 && CLIProcess.pid != process.pid) {
        consoleLog('[WARN] terminate a Wakanda Server process (CLI - PID ' + CLIProcess.pid + ')');
        CLIProcess.kill('SIGKILL');
    }
    if (phantomProcess !== null && phantomProcess.pid > 0 && phantomProcess.pid != process.pid) {
        consoleLog('[WARN] terminate a PhantomJS process (PID ' + phantomProcess.pid + ')');
        phantomProcess.kill('SIGKILL');
    }
}

// Try to exit gracefully
function exitGracefully(code) {
    frontendReady = false;
    if (typeof code === 'undefined') {
        code = 0;
    }
    if (shutDown === false) {
        shutDown = true;
        consoleLog('[INFO] about to exit...');
        killMainProcesses();
        if (running === true && runLog.length > 0) {
            try {
                fs.writeFileSync(path.join(config.reportsBasePath, config.WAKANDA_BRANCH, config.TEST_BRANCH, config.CHANGELIST.toString(), 'runlog.json'), JSON.stringify(runLog));
            } catch (e) {
                consoleLog('[WARN] cannot write global log file (1)', e);
            }
        }
        bye();
        exterminate(function() {
            consoleLog('[INFO] bye.');
            process.exit(code);
        });
    }
}

function killWindowsProcess(filter, callback) {
    exec('wmic path win32_process where (' + filter + ' and not CommandLine like "%node%" and not CommandLine like "%xendpriv%") get name,processid',
        function(error, stdout, stderr) {
            var skipFirstLine = true;
            var lines = stdout.split(/\r?\n/);
            async.eachSeries(
                lines,
                function(line, serieCallback) {
                    var _ps = line.replace(/^\s+/g, '').replace(/\s+$/g, '');
                    if (skipFirstLine === true) {
                        skipFirstLine = false;
                        serieCallback(null);
                    } else if (_ps !== '') {
                        _ps = /^([a-z0-9\.\s_-]+)\s+([0-9]+)$/i.exec(_ps);
                        if (_ps !== null) {
                            var cmd = _ps[1].replace(/^\s+/g, '').replace(/\s+$/g, '');
                            var pid = parseInt(_ps[2].replace(/^\s+/g, '').replace(/\s+$/g, ''));
                            if (isNaN(pid) === false && pid > 0 && pid != process.pid) {
                                exec('taskkill /pid ' + pid + ' /T /F', function(error, stdout, stderr) {
                                    consoleLog('[WARN] terminate a process named "' + cmd + '" (PID ' + pid + ')');
                                    serieCallback(null);
                                });
                            } else {
                                serieCallback(null);
                            }
                        } else {
                            serieCallback(null);
                        }
                    } else {
                        serieCallback(null);
                    }
                },
                function(err) {
                    callback(null);
                }
            );
        });
}

function killUnixProcess(filter, callback) {
    exec('ps aux | grep -i ' + filter, function(error, stdout, stderr) {
        var lines = stdout.split(/\r?\n/);
        async.eachSeries(
            lines,
            function(line, serieCallback) {
                if (/\/coreservices\//i.test(line) === false && /grep/.test(line) === false && /[a-z0-9]+/i.test(line) === true) {
                    var line = line.split(/\s+/);
                    var cmd = line[line.length - 1].replace(/^\s+/g, '').replace(/\s+$/g, '');
                    var pid = parseInt(line[1].replace(/^\s+/g, '').replace(/\s+$/g, ''));
                    if (isNaN(pid) === false && pid > 0 && pid != process.pid) {
                        spawn('kill', ['-9', pid]);
                        consoleLog('[WARN] terminate a process named "' + cmd + '" (PID ' + pid + ')');
                        serieCallback(null);
                    } else {
                        serieCallback(null);
                    }
                } else {
                    serieCallback(null);
                }
            },
            function(err) {
                callback(null);
            }
        );
    });
}

// EXTERMINATE
function exterminate(callback, secondPass) {
    if (typeof secondPass === 'undefined') {
        secondPass = false;
    }
    var filterDir = path.basename(config.BUILD_TEST_DIR).toLowerCase();
    if (isWindows()) {
        var filters = [{
            filter: 'CommandLine like "%wakanda%server.exe%"',
            restricted: true
        }, {
            filter: 'CommandLine like "%\\\\' + filterDir + '%" and CommandLine like "%wakanda%server.exe%"',
            restricted: false
        }, {
            filter: 'CommandLine like "%wakanda%studio.exe%"',
            restricted: true
        }, {
            filter: 'CommandLine like "%\\\\' + filterDir + '%" and CommandLine like "%wakanda%studio.exe%"',
            restricted: false
        }, {
            filter: 'CommandLine like "%surfire%"',
            restricted: false
        }, {
            filter: 'CommandLine like "%chromedriver%"',
            restricted: false
        }, {
            filter: 'CommandLine like "%chrome.exe%"',
            restricted: true
        }, {
            filter: 'CommandLine like "%iexplore.exe%"',
            restricted: true
        }, {
            filter: 'CommandLine like "%firefox.exe%"',
            restricted: true
        }, {
            filter: 'CommandLine like "%\\\\target\\\\temp\\\\chrome%"',
            restricted: false
        }, {
            filter: 'CommandLine like "%\\\\' + filterDir + '%" and CommandLine like "%4d%server.exe%"',
            restricted: false
        }, {
            filter: 'CommandLine like "%4d%server.exe%"',
            restricted: false
        }, {
            filter: 'CommandLine like "%4d%"',
            restricted: false
        }, {
            filter: 'CommandLine like "%msiexec.exe%"',
            restricted: false
        }, {
            filter: 'CommandLine like "%\\\\' + filterDir + '%" and CommandLine like "%java%"',
            restricted: false
        }, {
            filter: 'CommandLine like "' + filterDir + '%"',
            restricted: false
        }];
        async.eachSeries(
            filters,
            function(filter, serieCallback) {
                if (filter.restricted === true && (typeof config.deepCleaning === 'undefined' || config.deepCleaning === true)) {
                    killWindowsProcess(filter.filter, serieCallback);
                } else if (filter.restricted === false) {
                    killWindowsProcess(filter.filter, serieCallback);
                } else {
                    serieCallback(null);
                }
            },
            function(err) {
                setTimeout(function() {
                    if (secondPass === true) {
                        callback();
                    } else {
                        exterminate(callback, true);
                    }
                }, 125);
            }
        );
    } else {
        filterDir = '[' + filterDir.substr(0, 1) + ']' + filterDir.substr(1);
        var filters = [{
                filter: '[w]akanda.*server',
                restricted: true
            }, {
                filter: '[w]akanda.*studio',
                restricted: true
            }, {
                filter: filterDir + '/*/wakanda',
                restricted: false
            }, {
                filter: '[s]urfire',
                restricted: false
            }, {
                filter: '[c]hromedriver',
                restricted: false
            }, {
                filter: filterDir + '/*/',
                restricted: false
            }, {
                filter: '[c]hrome',
                restricted: true
            }, {
                filter: '[s]afari',
                restricted: true
            }, {
                filter: '[t]arget\/temp\/chrome',
                restricted: false
            }, {
                filter: '[f]irefox',
                restricted: true
            }, {
                filter: filterDir + '/*/4d',
                restricted: true
            }, {
                filter: '[^\.][4]d',
                restricted: true
            }, {
                filter: ('[' + config.BUILD_TEMP_DIR.substr(1, 1) + ']' + config.BUILD_TEMP_DIR.substr(2)).toLowerCase(),
                restricted: false
            }
            /*,
			{
				filter: '*',
				restricted: true
			}*/
        ];
        async.eachSeries(
            filters,
            function(filter, serieCallback) {
                if (filter.restricted === true && (typeof config.deepCleaning === 'undefined' || config.deepCleaning === true)) {
                    if (filter.filter === '*') {
                        /*
						if (isMac()) {
							exec('sudo purge && killall Finder', function(error, stdout, stderr) {
								serieCallback(null);
							});
						} else {
							exec('sudo sync && echo 3 | sudo tee /proc/sys/vm/drop_caches', function(error, stdout, stderr) {
								serieCallback(null);
							});
						}
						*/
                    } else {
                        killUnixProcess(filter.filter, serieCallback);
                    }
                } else if (filter.restricted === false && filter.filter !== '*') {
                    killUnixProcess(filter.filter, serieCallback);
                } else {
                    serieCallback(null);
                }
            },
            function(err) {
                setTimeout(function() {
                    if (secondPass === true) {
                        callback();
                    } else {
                        exterminate(callback, true);
                    }
                }, 125);
            }
        );
    }
}

function exterminateLocal(dir, callback, secondPass) {
    if (typeof secondPass === 'undefined') {
        secondPass = false;
    }
    var filterDir = path.basename(dir).toLowerCase();
    if (isWindows()) {
        var filters = [{
            filter: 'CommandLine like "%\\\\' + filterDir + '\\\\%"',
            restricted: false
        }];
        async.eachSeries(
            filters,
            function(filter, serieCallback) {
                if (filter.restricted === true && (typeof config.deepCleaning === 'undefined' || config.deepCleaning === true)) {
                    killWindowsProcess(filter.filter, serieCallback);
                } else if (filter.restricted === false) {
                    killWindowsProcess(filter.filter, serieCallback);
                } else {
                    serieCallback(null);
                }
            },
            function(err) {
                setTimeout(function() {
                    if (secondPass === true) {
                        callback();
                    } else {
                        exterminateLocal(dir, callback, true);
                    }
                }, 125);
            }
        );
    } else {
        filterDir = '[' + filterDir.substr(0, 1) + ']' + filterDir.substr(1);
        var filters = [{
            filter: filterDir + '\/',
            restricted: false
        }];
        async.eachSeries(
            filters,
            function(filter, serieCallback) {
                if (filter.restricted === true && (typeof config.deepCleaning === 'undefined' || config.deepCleaning === true)) {
                    if (filter.filter === '*') {
                        /*
						if (isMac()) {
							exec('sudo purge && killall Finder', function(error, stdout, stderr) {
								serieCallback(null);
							});
						} else {
							exec('sudo sync && echo 3 | sudo tee /proc/sys/vm/drop_caches', function(error, stdout, stderr) {
								serieCallback(null);
							});
						}
						*/
                    } else {
                        killUnixProcess(filter.filter, serieCallback);
                    }
                } else if (filter.restricted === false && filter.filter !== '*') {
                    killUnixProcess(filter.filter, serieCallback);
                } else {
                    serieCallback(null);
                }
            },
            function(err) {
                setTimeout(function() {
                    if (secondPass === true) {
                        callback();
                    } else {
                        exterminateLocal(dir, callback, true);
                    }
                }, 125);
            }
        );
    }
}

function arrayUnique(a) {
    return a.reduce(function(p, c) {
        if (p.indexOf(c) < 0) p.push(c);
        return p;
    }, []);
}

// Get current status
function getStatus() {
    if (Object.keys(state).length === 0) {
        try {
            state = JSON.parse(fs.readFileSync(path.join(config.reportsBasePath, 'state.json')).toString());
            if (forceRelaunch === true) {
                state.relaunch = false;
            }
            state.done = arrayUnique(state.done);
            state.queue = arrayUnique(state.queue);
            fs.writeFileSync(path.join(config.reportsBasePath, 'state.json'), JSON.stringify(state));
        } catch (e) {
            state = {
                currentJob: -1,
                done: [],
                queue: [],
                changelist: getCurrentChangelist()
            };
        }
    }
    return {
        waiting: waiting,
        running: running || runningManual,
        manual: runningManual,
        locked: locked,
        paused: paused,
        done: runningManual ? runningManualDone : state.done,
        queue: runningManual ? runningManualQueue : state.queue,
        currentJob: runningManual ? runningManualCurrentJob : state.currentJob,
        changelist: state.changelist,
        productBranch: config.WAKANDA_BRANCH,
        productBranchCap: capitalize(config.WAKANDA_BRANCH),
        downloads: {
            wakanda: downloadingNewWakandaBuild,
            wakandaLeft: downloadingNewWakandaBuildExpect,
            wakandaDone: downloadingNewWakandaBuildDone,
            wakandaDeploying: deployingNewWakandaBuild,
            installer: downloadingNewWakandaInstaller,
            installerLeft: downloadingNewWakandaInstallerExpect,
            installerDone: downloadingNewWakandaInstallerDone,
            installerDeploying: deployingNewWakandaInstaller,
            fourd: downloadingNew4DBuild,
            fourdLeft: downloadingNew4DBuildExpect,
            fourdDone: downloadingNew4DBuildDone,
            fourdDeploying: deployingNew4DBuild
        },
        testBranch: config.TEST_BRANCH,
        testBranchCap: capitalize(config.TEST_BRANCH),
        subVersion: config.subversion ? config.subversion.toLowerCase() : '',
        uptime: Math.floor(process.uptime())
    };
}

// Get the date of the given changelist (as a Date object)
function getChangelistDate(changelist, callback) {
    if (typeof changelistCache[changelist] !== 'undefined') {
        callback(changelistCache[changelist]);
    } else {
        changelistCache[changelist] = null;
        p4Process = exec(config.p4BaseCmd + ' describe ' + changelist, {
            timeout: 30000,
            maxBuffer: 10 * 1024 * 1024,
            killSignal: 'SIGKILL'
        }, function(error, stdout, stderr) {
            p4Process = null;
            try {
                var date = new Date(/(\d+\/\d+\/\d+\s+\d+:\d+:\d+)/.exec(stdout.split('\n')[0])[1]);
                changelistCache[changelist] = date;
                callback(date);
            } catch (e) {
                changelistCache[changelist] = null;
                callback(null);
            }
        });
    }
}

// Get the actual case-sensitive path from the given case-insensitive or lower-case one
function actualPath(p, failIfNotExist) {
    if (typeof failIfNotExist === "undefined") {
        failIfNotExist = false;
    }
    var expected = p.replace(/\/\//g, '/').replace(/\\\\/g, '\\').split(path.sep);
    var actual = '';
    var next = null;
    var index = 1;
    var failed = false;
    expected.forEach(function(item) {
        if (failed === false) {
            if (next === null) {
                actual += item + path.sep
            } else {
                for (var i = 0; i < next.length; i++) {
                    if (next[i] === item) {
                        if (index === expected.length) {
                            actual += next[i];
                        } else {
                            actual += next[i] + path.sep;
                        }
                        break;
                    } else if (next[i].toLowerCase() === item.toLowerCase()) {
                        if (index === expected.length) {
                            actual += next[i];
                        } else {
                            actual += next[i] + path.sep;
                        }
                        break;
                    }
                }
            }
            try {
                files = fs.readdirSync(actual);
                next = files;
                index++;
            } catch (e) {
                failed = true;
            }
        }
    });
    if (failIfNotExist === true && failed === true && p.toLowerCase() !== actual.toLowerCase()) {
        return null;
    } else {
        return actual;
    }
}

// Synchronous and recursive chmod
function chmodrSync(p, mode) {
    var children;
    try {
        children = fs.readdirSync(p);
    } catch (e) {
        if (e && e.code === "ENOTDIR") {
            return fs.chmodSync(p, mode);
        }
        throw e;
    }
    if (!children.length) {
        return fs.chmodSync(p, dirMode(mode));
    }
    children.forEach(function(child) {
        chmodrSync(path.resolve(p, child), mode);
    });
    return fs.chmodSync(p, dirMode(mode));
}

// Utility func for chmodrSync
function dirMode(mode) {
    if (mode & 0400) {
        mode |= 0100;
    }
    if (mode & 040) {
        mode |= 010;
    }
    if (mode & 04) {
        mode |= 01;
    }
    return mode;
}

// Synchronous file copy
function copyFileSync(srcFile, destFile) {
    var BUF_LENGTH, buff, bytesRead, fdr, fdw, pos;
    BUF_LENGTH = 64 * 1024;
    buff = new Buffer(BUF_LENGTH);
    fdr = fs.openSync(srcFile, 'r');
    fdw = fs.openSync(destFile, 'w');
    bytesRead = 1;
    pos = 0;
    while (bytesRead > 0) {
        bytesRead = fs.readSync(fdr, buff, 0, BUF_LENGTH, pos);
        fs.writeSync(fdw, buff, 0, bytesRead);
        pos += bytesRead;
    }
    fs.closeSync(fdr);
    return fs.closeSync(fdw);
}

// OS and platform stuff
function isMac() {
    return /^darwin/i.test(process.platform);
}

function isWindows() {
    return /^win/i.test(process.platform);
}

function isLinux() {
    return /^linux/i.test(process.platform);
}

function is32() {
    return process.arch === 'ia32';
}

function is64() {
    return process.arch === 'x64';
}

// Find files synchronously using the given (optional) file name, folder name and file content RegExp patterns
function findFiles(dir, fileFilter, dirFilter, contentFilter) {
    var results = [];
    try {
        fs.readdirSync(dir).forEach(function(fileName) {
            var file = dir + path.sep + fileName;
            try {
                var stat = fs.statSync(file);
            } catch (e) {
                var stat = false;
            }
            if (stat && stat.isDirectory()) {
                if (typeof dirFilter === 'undefined' || dirFilter.test(fileName)) {
                    results = results.concat(findFiles(file, fileFilter, dirFilter, contentFilter));
                }
            } else if (stat && stat.isFile() && fileFilter.test(fileName)) {
                if (typeof contentFilter === 'undefined') {
                    results.push(actualPath(file));
                } else {
                    var content = fs.readFileSync(file).toString();
                    if (contentFilter.test(content)) {
                        results.push(actualPath(file));
                    }
                }
            }
        });
    } catch (e) {
        // Doesn't matter
    }
    return results;
}

// Synchronous and recursive rmdir
function rmdir(dir, noRoot) {
    if (isWindows()) {
        if (typeof noRoot === 'undefined' || noRoot === false) {
            exec('rd /s /q "' + dir + '"');
        } else {
            var list = fs.readdirSync(dir);
            for (var i = 0; i < list.length; i++) {
                var filename = path.join(dir, list[i]);
                try {
                    var stat = fs.statSync(filename);
                    if (stat.isDirectory()) {
                        exec('rd /s /q "' + filename + '"');
                    } else {
                        exec('del /f /q "' + filename + '"');
                    }
                } catch (e) {

                }
            }
        }
    } else {
        try {
            var list = fs.readdirSync(dir);
            for (var i = 0; i < list.length; i++) {
                var filename = path.join(dir, list[i]);
                try {
                    var stat = fs.statSync(filename);
                    if (stat.isDirectory()) {
                        try {
                            rmdir(filename);
                        } catch (e) {
                            exec('rm -rf "' + filename + '"');
                        }
                    } else {
                        try {
                            fs.unlinkSync(filename);
                        } catch (e) {
                            exec('rm -f "' + filename + '"');
                        }
                    }
                } catch (e) {
                    // consoleLog('[WARN] cannot delete (2)', e);
                }
            }
            if (typeof noRoot === 'undefined' || noRoot === false) {
                try {
                    fs.rmdirSync(dir);
                } catch (e) {
                    exec('rm -rf "' + dir + '"');
                }
            }
        } catch (e) {
            // consoleLog('[WARN] cannot delete (3)', e);
        }
    }
}

function deployWakandaBuild(srcPath, destPath, callback) {
    callback(null);
}

function deployWakandaInstaller(srcPath, destPath, callback) {
    callback(null);
}

function deploy4DBuild(srcPath, destPath, callback) {
    callback(null);
}

// Get the current changelist to test
function getCurrentChangelist(latest) {
    var found = null;
    if (typeof latest === 'undefined' || latest === false) {
        if (newChangelist !== null) {
            found = newChangelist;
        } else if (typeof state.changelist !== 'undefined') {
            found = parseInt(state.changelist);
        }
    }
    if (found === null || isNaN(found)) {
        var results = [];
        try {
            fs.readdirSync(config.BUILD_TEST_DIR).forEach(function(fileName) {
                var file = config.BUILD_TEST_DIR + path.sep + fileName;
                try {
                    var stat = fs.statSync(file);
                } catch (e) {
                    var stat = false;
                }
                if (stat && stat.isDirectory() && /^\d+$/.test(fileName)) {
                    results.push(parseInt(fileName));
                }
            });
        } catch (e) {
            // Doesn't matter
        }
        if (results.length > 0) {
            results.sort();
            results.reverse();
            found = results[0];
        }
    }
    if (found === null || isNaN(found)) {
        found = 0;
    }
    return found;
}

// Get the available jobs (from Perforce workspace)
function getAvailableJobs(filter) {
    if (getAvailableJobsCache === null) {
        var gonogo = [];
        var others = [];
        var checkDependencies = false;
        if (typeof config.blacklist !== 'undefined' && typeof config.blacklist.dependencies !== 'undefined' && config.blacklist.dependencies.length > 0) {
            checkDependencies = true;
        }
        var jobPaths = [];
        jobPaths.push(path.join(config.P4_WORKSPACE_PATH, 'depot', 'Wakanda', config.WAKANDA_BRANCH, 'Common', 'tests'));
        jobPaths.push(path.join(config.P4_WORKSPACE_PATH, 'depot', 'Wakanda', config.WAKANDA_BRANCH, 'Server', 'tests'));
        if (isLinux() === false) {
            jobPaths.push(path.join(config.P4_WORKSPACE_PATH, 'depot', 'Wakanda', config.WAKANDA_BRANCH, 'Studio', 'tests'));
        }
        jobPaths.forEach(function(_path) {
            _path = actualPath(_path.toLowerCase());
            findFiles(_path, /^(pom|test\.conf)\.(xml|json)$/).forEach(function(pom) {
                var jobBaseName = pom.toLowerCase().replace(config.P4_WORKSPACE_PATH.toLowerCase(), '');
                jobBaseName = jobBaseName.replace(path.join('depot', 'Wakanda', config.WAKANDA_BRANCH).toLowerCase(), '');
                jobBaseName = jobBaseName.replace(path.sep + 'tests' + path.sep, path.sep);
                if (isWindows()) {
                    jobBaseName = path.dirname(jobBaseName).replace(/\\/g, '_').replace(/__/g, '').toLowerCase();
                } else {
                    jobBaseName = path.dirname(jobBaseName).replace(/\//g, '_').replace(/__/g, '').toLowerCase();
                }
                if (/\.xml$/i.test(pom)) {
                    if (typeof config.noJavaTest === 'undefined' || config.noJavaTest === false) {
                        var jobName = jobBaseName + '_core';
                        jobName = jobName.replace(/core/g, 'main').replace(/main_+main/g, 'main').replace(/_+/g, '_');
                        var pomContent = fs.readFileSync(pom);
                        var keepIt = true;
                        if (checkDependencies === true) {
                            config.blacklist.dependencies.forEach(function(artifactid) {
                                var testNameFilter = new RegExp('<artifactid>' + artifactid.replace(/\*/ig, '.*') + '<\/artifactid>', 'ig');
                                if (testNameFilter.test(pomContent) === true) {
                                    keepIt = false;
                                }
                            });
                        }
                        if (isLinux()) {
                            if (/<os>[\s\S]*<name>/ig.test(pomContent) === true && /<os>[\s\S]*<name>linux<\/name>[\s\S]*<\/os>/ig.test(pomContent) === false) {
                                keepIt = false;
                            }
                        } else if (isMac()) {
                            if (/<os>[\s\S]*<name>/ig.test(pomContent) === true && /<os>[\s\S]*<name>mac<\/name>[\s\S]*<\/os>/ig.test(pomContent) === false) {
                                keepIt = false;
                            }
                        } else if (isWindows()) {
                            if (/<os>[\s\S]*<name>/ig.test(pomContent) === true && /<os>[\s\S]*<name>windows<\/name>[\s\S]*<\/os>/ig.test(pomContent) === false) {
                                keepIt = false;
                            }
                        }
                        if (keepIt === true) {
                            if (/<gonogo>\s*true/i.test(pomContent) === true) {
                                gonogo.push(jobName);
                            } else {
                                others.push(jobName);
                            }
                        }
                    }
                } else if (/pom\.json$/i.test(pom)) {
                    var pomContent = fs.readFileSync(pom);
                    var keepIt = true;
                    if (isLinux()) {
                        if (/"os"\s*:\s*\[/ig.test(pomContent) === true && /"os"\s*:\s*\[.*"linux"/ig.test(pomContent) === false) {
                            keepIt = false;
                        }
                    } else if (isMac()) {
                        if (/"os"\s*:\s*\[/ig.test(pomContent) === true && /"os"\s*:\s*\[.*"mac"/ig.test(pomContent) === false) {
                            keepIt = false;
                        }
                    } else if (isWindows()) {
                        if (/"os"\s*:\s*\[/ig.test(pomContent) === true && /"os"\s*:\s*\[.*"windows"/ig.test(pomContent) === false) {
                            keepIt = false;
                        }
                    }
                    if (keepIt === true) {
                        var found = false;
                        fs.readdirSync(path.dirname(pom)).forEach(function(fileName) {
                            if (/^test.*\.js$/i.test(fileName) === true) {
                                var match = /^test(.*)\.js$/i.exec(fileName);
                                if (match === null || match[1] === '') {
                                    var jobName = jobBaseName + '_core';
                                } else {
                                    var jobName = jobBaseName + '_' + match[1].toLowerCase();
                                }
                                jobName = jobName.replace(/core/g, 'main').replace(/main_+main/g, 'main').replace(/_+/g, '_');
                                if (/"gonogo":\s*true/i.test(pomContent) === true) {
                                    gonogo.push(jobName);
                                } else {
                                    others.push(jobName);
                                }
                                found = true;
                            }
                        });
                        if (found === false) {
                            var jobName = jobBaseName + '_core';
                            jobName = jobName.replace(/core/g, 'main').replace(/main_+main/g, 'main').replace(/_+/g, '_');
                            if (/"gonogo":\s*true/i.test(pomContent) === true) {
                                gonogo.push(jobName);
                            } else {
                                others.push(jobName);
                            }
                        }
                    }
                } else if (/test\.conf\.json$/i.test(pom)) { // NEW ARCHI
                    var pomContent = fs.readFileSync(pom);
                    var keepIt = true;
                    if (/"active":\s*true/i.test(pomContent) === false) {
                        keepIt = false;
                    }
                    if (keepIt === true) {
                        if (/"gonogo":\s*true/i.test(pomContent) === true) {
                            gonogo.push(jobBaseName + '_core');
                        } else {
                            others.push(jobBaseName + '_core');
                        }
                    }
                }
            });
        });
        gonogo.sort(function(a, b) {
            if (a.split('_').length < b.split('_').length) {
                return -1;
            } else if (a.split('_').length > b.split('_').length) {
                return 1;
            } else if (a < b) {
                return -1;
            } else if (a > b) {
                return 1;
            } else {
                return 0;
            }
        });
        others.sort(function(a, b) {
            if (a.split('_').length < b.split('_').length) {
                return -1;
            } else if (a.split('_').length > b.split('_').length) {
                return 1;
            } else if (a < b) {
                return -1;
            } else if (a > b) {
                return 1;
            } else {
                return 0;
            }
        });
        getAvailableJobsCache = gonogo.concat(others);
    }
    var availableJobs = JSON.parse(JSON.stringify(getAvailableJobsCache));
    if (typeof filter === "function") {
        availableJobs = availableJobs.filter(function(item) {
            return (filter(item) === true);
        });
    }
    if (typeof config.blacklist !== 'undefined' && typeof config.blacklist.name !== 'undefined' && config.blacklist.name.length > 0) {
        availableJobs = availableJobs.filter(function(item) {
            var blacklisted = false;
            config.blacklist.name.forEach(function(name) {
                var testNameFilter = new RegExp('^' + name.replace(/\*/ig, '.*') + '$', 'i');
                if (testNameFilter.test(item) === true) {
                    blacklisted = true;
                }
            });
            return (blacklisted === false);
        });
    }
    return availableJobs;
}

// Ask a question from command line
function ask(question, callback) {
    var stdin = process.stdin,
        stdout = process.stdout;
    stdin.resume();
    stdout.write(question + ": ");
    stdin.once('data', function(data) {
        data = data.toString().trim();
        callback(data);
    });
}

// Run all available test suites
function runAll(filter, latest) {
    if (typeof latest === 'undefined') {
        latest = false;
    }
    getStatus();
    try {
        runLog = JSON.parse(fs.readFileSync(path.join(config.reportsBasePath, config.WAKANDA_BRANCH, config.TEST_BRANCH, getCurrentChangelist(latest).toString(), 'runlog.json')).toString());
    } catch (e) {
        runLog = [];
    }
    try {
        var statCurrent = fs.statSync(path.join(config.reportsBasePath, 'current.json'));
    } catch (e) {
        var statCurrent = false;
    }
    try {
        var current = JSON.parse(fs.readFileSync(path.join(config.reportsBasePath, 'current.json')).toString());
    } catch (e) {
        statCurrent = false;
    }
    if (firstLaunch === true && state.done.length < state.queue.length) {
        if (statCurrent) {
            if (state.done.indexOf(current.testName) !== -1) {
                state.done = state.done.filter(function(item) {
                    return (item !== current.testName);
                });
            }
            state.currentJob = state.queue.indexOf(current.testName);
        }
        if (typeof config.automatic !== "undefined" && config.automatic === true) {
            initRunAll(filter);
        } else {
            if (statCurrent) {
                initRunAll(filter);
            } else {
                ask('do you want to resume the previous test session (' + state.done.length + ' tests done out of ' + state.queue.length + ')? (y/n)'.white.bold, function(answer) {
                    if (/y/i.test(answer) === false) {
                        state = {
                            currentJob: -1,
                            done: [],
                            queue: [],
                            changelist: getCurrentChangelist(latest)
                        };
                        runLog = [];
                    }
                    initRunAll(filter);
                });
            }
        }
    } else {
        if (state.currentJob == -1 || state.queue.length == 0 || (state.currentJob >= 0 && state.done.length === state.queue.length)) {
            state = {
                currentJob: -1,
                done: [],
                queue: [],
                changelist: getCurrentChangelist(latest)
            };
            runLog = [];
        }
        initRunAll(filter);
    }
}

// Continuation of runAll
function initRunAll(filter, latest) {
    if (typeof latest === 'undefined') {
        latest = false;
    }
    running = true;
    try {
        fs.unlinkSync(path.join(config.reportsBasePath, config.WAKANDA_BRANCH, config.TEST_BRANCH, getCurrentChangelist(latest).toString(), 'runlog.html'));
    } catch (e) {
        // Doesn't matter
    }
    if (state.currentJob === -1) {
        if (typeof config.sync_perforce === 'undefined' || config.sync_perforce === true) {
            globalPerforceSync(function() {
                state.queue = getAvailableJobs(filter);
                state.currentJob = 0;
                runNext();
            });
        } else {
            state.queue = getAvailableJobs(filter);
            state.currentJob = 0;
            runNext();
        }
    } else {
        runNext();
    }
}

// Global P4 Sync
function globalPerforceSync(cb, force) {
    getAvailableJobsCache = null;
    var p4cmd = config.p4BaseCmd + ' -c' + config.P4_WORKSPACE_NAME + ' sync ';
    if (typeof force !== 'undefined' && force === true) {
        p4cmd += '-f ';
    }
    p4cmd += actualPath(path.join(config.P4_WORKSPACE_PATH, 'depot', 'Wakanda', config.WAKANDA_BRANCH)) + '... ';
    p4cmd += actualPath(path.join(config.P4_WORKSPACE_PATH, 'RIA', 'tests', config.TEST_BRANCH)) + '... ';
    p4cmd += actualPath(path.join(config.P4_WORKSPACE_PATH, 'RIA', 'trunk', 'QATools', 'Automation', 'wakbot')) + '...';
    p4Process = exec(p4cmd, {
        timeout: 30 * 60 * 1000,
        maxBuffer: 10 * 10 * 1024 * 1024,
        killSignal: 'SIGKILL'
    }, function(err, stdout, stderr) {
        p4Process = null;
        consoleLog('[WARN] simple update of workspace (1)', p4cmd, err, stderr);
        clearCache();
        if (typeof cb === 'function') cb();
    });
}

// Run next test suite (in "run all" mode)
function runNext(previousResult) {
    hello(true);
    clearTimeout(shutdownTimeout);
    var sendResults = false;
    if (typeof previousResult === 'undefined') {
        if (firstLaunch === true) {
            firstLaunch = false;
            consoleLog('[INFO] tests started at ' + new Date());
        } else if (waiting === true) {
            consoleLog('[INFO] tests resumed at ' + new Date());
        }
    } else {
        stopMonitoring();
        try {
            fs.unlinkSync(path.join(config.reportsBasePath, 'current.json'));
        } catch (e) {
            // Doesn't matter
        }
        runLog.push({
            name: previousResult.testName,
            start: previousResult.start,
            end: previousResult.end,
            duration: previousResult.duration,
            status: previousResult.status,
            dir: previousResult.resultDir
        });
        if (typeof config.dashboard !== "undefined" && typeof config.dashboard.address !== "undefined" && typeof config.dashboard.connect !== "undefined" && typeof config.dashboard.id !== "undefined" && config.dashboard.connect === true) {
            try {
                var report = JSON.parse(fs.readFileSync(path.join(previousResult.resultDir, 'report.json')).toString());
            } catch (e) {
                var report = {
                    name: previousResult.testName,
                    changelist: config.CHANGELIST,
                    start: previousResult.start,
                    duration: previousResult.duration,
                    abstract: {
                        passed: 0,
                        total: 0,
                        failures: 0,
                        skipped: 0
                    },
                    status: previousResult.status
                };
            }
            sendResults = true;
        }
        state.done.push(previousResult.testName);
        doNotOverwriteState = false;
        try {
            fs.writeFileSync(path.join(config.reportsBasePath, 'state.json'), JSON.stringify(state));

        } catch (e) {
            consoleLog('[WARN] cannot write current state (1)', e);
        }
        try {
            fs.writeFileSync(path.join(previousResult.resultDir, 'runlog.json'), JSON.stringify(previousResult));
        } catch (e) {
            consoleLog('[WARN] cannot write job runlog (1)', e);
        }
        if (typeof previousResult.pom !== 'undefined' && previousResult.pom) {
            try {
                fs.writeFileSync(path.join(previousResult.resultDir, 'pom.json'), JSON.stringify(previousResult.pom));
            } catch (e) {
                consoleLog('[WARN] cannot write job pom (1)', e);
            }
        }
        try {
            fs.unlinkSync(path.join(previousResult.resultDir, '.manual'));
        } catch (e) {
            // Doesn't matter
        }
        try {
            fs.writeFileSync(path.join(previousResult.resultDir, '.auto'), 'true');
        } catch (e) {
            consoleLog('[WARN] cannot write job .auto flag (1)', e);
        }
        var status = 'UNKNOWN'.grey;
        if (previousResult.status === null) {
            status = 'FAILURE'.red;
        } else if (previousResult.status === false) {
            status = 'UNSTABLE'.yellow;
        } else if (previousResult.status === true) {
            status = 'SUCCESS'.green;
        }
        consoleLog('[INFO] ' + previousResult.testName.white.bold + ' --> '.grey + status.bold);
        var cleanup = temp.cleanup();
        if (typeof previousResult.tmpDir !== 'undefined') {
            try {
                rmdir(previousResult.tmpDir);
            } catch (e) {
                // Doesn't matter
            }
        }
        state.currentJob++;
    }
    if (shutDown === false) {
        waiting = false;
        killMainProcesses();
        exterminate(function() {
            if (shutDown === false) {
                if (typeof previousResult !== 'undefined') {
                    getCrashlocationContentAfter();
                }
                getProcessListDiffAfter(function(diff) {
                    if (typeof previousResult !== 'undefined' && diff !== null && (diff.less.length > 0 || diff.more.length > 0)) {
                        var diffLog = '';
                        if (diff.less.length > 0) {
                            diffLog += '-- Lost Processes (killed during the test):\n';
                            diff.less.forEach(function(proc) {
                                diffLog += '\t' + proc.pid + '\t' + proc.cmd + '\n';
                            });
                            diffLog += ' \n\n';
                        }
                        if (diff.more.length > 0) {
                            diffLog += '++ Additional Processes (spawned during the test):\n';
                            diff.more.forEach(function(proc) {
                                diffLog += '\t' + proc.pid + '\t' + proc.cmd + '\n';
                            });
                            diffLog += ' \n\n';
                        }
                        try {
                            fs.writeFileSync(path.join(previousResult.resultDir, 'procdiff.txt'), diffLog);
                        } catch (e) {
                            consoleLog('[WARN] cannot archive process diff (1)', e);
                        }
                    }
                    if (typeof previousResult !== 'undefined' && crashes.length > 0) {
                        consoleLog('[WARN] test ' + previousResult.testName + ' produced ' + crashes.length + ' crash(es)');
                        for (var i = 0; i < crashes.length; i++) {
                            if (/server/i.test(crashes[i])) {
                                var crashName = 'server_crash_' + (i + 1) + path.extname(crashes[i]);
                            } else if (/studio/i.test(crashes[i])) {
                                var crashName = 'studio_crash_' + (i + 1) + path.extname(crashes[i]);
                            } else if (/4d/i.test(crashes[i])) {
                                var crashName = '4d_crash_' + (i + 1) + path.extname(crashes[i]);
                            } else {
                                var crashName = 'other_crash_' + (i + 1) + path.extname(crashes[i]);
                            }
                            try {
                                copyFileSync(crashes[i], path.join(previousResult.resultDir, crashName));
                            } catch (e) {
                                consoleLog('[WARN] cannot archive crash log', e);
                            }
                        }
                    }
                    if (typeof previousResult !== 'undefined' && sendResults === true) {
                        if (typeof config.dashboard !== "undefined" && typeof config.dashboard.connect !== "undefined" && typeof config.dashboard.id !== "undefined" && config.dashboard.connect === true) {
                            try {
                                var results = JSON.parse(fs.readFileSync(path.join(previousResult.resultDir, 'report.json')).toString());
                            } catch (e) {
                                var results = {
                                    name: previousResult.testName,
                                    start: previousResult.start,
                                    end: previousResult.end,
                                    duration: previousResult.duration,
                                    abstract: {
                                        passed: 0,
                                        total: 0,
                                        failures: 0,
                                        skipped: 0
                                    },
                                    status: previousResult.status
                                };
                            }
                            var msg = {
                                id: config.dashboard.id,
                                changelist: config.CHANGELIST,
                                productBranch: config.WAKANDA_BRANCH,
                                results: {
                                    name: results.name,
                                    start: results.start,
                                    end: results.end,
                                    duration: results.duration,
                                    abstract: {
                                        passed: results.abstract.passed,
                                        total: results.abstract.total,
                                        failures: results.abstract.failures,
                                        skipped: results.abstract.skipped
                                    },
                                    status: results.status,
                                    crashes: crashes.length
                                }
                            };
                            var pom = getPomForTest(results.name);
                            if (isMac()) {
                                msg.os = 'mac';
                            } else if (isLinux()) {
                                msg.os = 'linux';
                            } else if (isWindows()) {
                                msg.os = 'windows';
                            }
                            if (pom && typeof pom.tester !== 'undefined' && pom.tester && pom.tester != '') {
                                msg.results.tester = pom.tester;
                            }
                            if (pom && typeof pom.developer !== 'undefined' && pom.developer && pom.developer != '') {
                                msg.results.developer = pom.developer;
                            }
                            if (pom && typeof pom.uuid !== 'undefined') {
                                msg.results.uuid = pom.uuid;
                            }
                            if (pom && typeof pom.bench !== 'undefined' && (pom.bench === true || pom.bench === 'true')) {
                                msg.results.isbench = true;
                                var CSVFilePath = path.join(previousResult.resultDir, 'result.csv');
                                try {
                                    var CSVStat = fs.statSync(CSVFilePath);
                                } catch (e) {
                                    var CSVStat = false;
                                }
                                if (CSVStat && CSVStat.isFile()) {
                                    msg.results.benchdata = fs.readFileSync(CSVFilePath).toString();
                                } else {
                                    msg.results.benchdata = null;
                                }
                            }
                            if (typeof config.subversion === 'string') {
                                msg.subVersion = config.subversion.toLowerCase();
                            } else {
                                msg.subVersion = '';
                            }
                            try {
                                socket.emit('results', JSON.stringify(msg));
                                consoleLog('[INFO] just sent "results" to the Hub (1)...');
                            } catch (e) {
                                consoleLog('[ERROR] could not send "results" to the Hub (1): ' + e);
                            }
                        }
                    }
                    if (state.currentJob > -1 && state.queue.length > 0 && state.currentJob < state.queue.length) {
                        clearTimeout(shutdownTimeout);
                        consoleLog('[INFO] next (' + (state.currentJob + 1) + '/' + state.queue.length + ')');
                        setTimeout(function() {
                            runTest(state.queue[state.currentJob], runNext, true);
                        }, 125);
                    } else if (downloadingNewWakandaBuildDone === false && downloadingNewWakandaInstallerDone === true) {
                        clearTimeout(shutdownTimeout);
                        consoleLog('[INFO] tests related to the new Wakanda Installers completed at ' + new Date() + ', now waiting 6 hours max. for the new Wakanda Builds (>' + previousChangelist + ')...');
                        waiting = true;
                        shutdownTimeout = setTimeout(function() {
                            shutdown(true);
                        }, 6 * 60 * 60 * 1000); // 6h
                    } else if (downloadingNewWakandaInstallerDone === false && downloadingNewWakandaBuildDone === true) {
                        clearTimeout(shutdownTimeout);
                        consoleLog('[WARN] tests related to the new Wakanda Builds completed at ' + new Date() + ', but the new Wakanda Installers are not available (>' + previousChangelist + '): waiting 3 hours max. then shutting down!');
                        waiting = true;
                        shutdownTimeout = setTimeout(function() {
                            shutdown(true);
                        }, 4 * 60 * 60 * 1000); // 4h
                    } else if (isLinux() === false && downloadingNew4DBuildDone === false && downloadingNewWakandaBuildDone === true) {
                        clearTimeout(shutdownTimeout);
                        consoleLog('[WARN] tests related to the new Wakanda Builds completed at ' + new Date() + ', but the new 4D Server is not available: will use an old one!');
                        if (isMac()) {
                            var wakApps = findFiles(config.BUILD_TEST_DIR, /^4d.*server$/i);
                            wakApps.forEach(function(wakApp) {
                                current4DServerPath = wakApp;
                            });
                        } else if (isWindows()) {
                            var wakApps = findFiles(config.BUILD_TEST_DIR, /^4d.*\.exe$/i);
                            wakApps.forEach(function(wakApp) {
                                current4DServerPath = wakApp;
                            });
                        }
                        consoleLog('[INFO] old 4D build (' + current4DServerPath + ') will be used');
                        downloadingNew4DBuild = true;
                        downloadingNew4DBuildDone = true;
                        downloadingNew4DBuildExpect = 0;
                        state.queue = state.queue.concat(getAvailableJobs(function(item) {
                            if (/(4d(?!p))/i.test(item)) {
                                return true;
                            } else {
                                return false;
                            }
                        }));
                        shutdownTimeout = setTimeout(function() {
                            runNext();
                        }, 125);
                    } else {
                        consoleLog('[INFO] finishing tests, please wait...');
                        clearTimeout(shutdownTimeout);
                        if (runFromWeb === true || (process.argv.length > 2 && (process.argv[2] === 'run' || process.argv[2] === 'resume'))) {
                            shutdown(true);
                        } else {
                            waiting = true;
                            shutdownTimeout = setTimeout(function() {
                                shutdown(true);
                            }, 125);
                        }
                    }
                });
            }
        });
    }
}

function shutdown(withReport) {
    if (typeof withReport === 'undefined') {
        withReport = false;
    }
    if (withReport === true) {
        if (typeof config.dashboard !== "undefined" && typeof config.dashboard.connect !== "undefined" && typeof config.dashboard.id !== "undefined" && config.dashboard.connect === true) {
            var msg = {
                id: config.dashboard.id,
                changelist: config.CHANGELIST,
                productBranch: config.WAKANDA_BRANCH
            };
            if (isMac()) {
                msg.os = 'mac';
            } else if (isLinux()) {
                msg.os = 'linux';
            } else if (isWindows()) {
                msg.os = 'windows';
            }
            if (typeof config.subversion === 'string') {
                msg.subVersion = config.subversion.toLowerCase();
            } else {
                msg.subVersion = '';
            }
            try {
                socket.emit('end', JSON.stringify(msg));
                consoleLog('[INFO] just sent "end" to the Hub (1)...');
            } catch (e) {
                consoleLog('[ERROR] could not send "end" to the Hub (1): ' + e);
            }
        }
        if (typeof config.dashboard !== "undefined" && typeof config.dashboard.address !== "undefined" && typeof config.dashboard.connect !== "undefined" && typeof config.dashboard.id !== "undefined" && config.dashboard.connect === true) {
            consoleLog('[WARN] launch P4 sync (shutdown)');
            globalPerforceSync(function() {
                consoleLog('[WARN] P4 sync done (shutdown)');
                consoleLog('[WARN] Hub asks to stop all current tests (shutdown)');
                killMainProcesses();
                exterminate(function() {
                    doShutdown();
                });
            });
            /*
			});
			*/
        } else {
            consoleLog('[WARN] launch P4 sync (shutdown)');
            globalPerforceSync(function() {
                consoleLog('[WARN] P4 sync done (shutdown)');
                consoleLog('[WARN] Hub asks to stop all current tests (shutdown)');
                killMainProcesses();
                exterminate(function() {
                    doShutdown();
                });
            });
        }
    } else {
        consoleLog('[WARN] launch P4 sync (shutdown)');
        globalPerforceSync(function() {
            consoleLog('[WARN] P4 sync done (shutdown)');
            consoleLog('[WARN] Hub asks to stop all current tests (shutdown)');
            killMainProcesses();
            exterminate(function() {
                doShutdown();
            });
        });
    }
}

function doShutdown(doNotExit) {
    if (typeof doNotExit === 'undefined') {
        doNotExit = false;
    } else if (doNotExit === true) {
        killMainProcesses();
        cleanDirs();
    }
    try {
        fs.unlinkSync(path.join(config.reportsBasePath, 'current.json'));
    } catch (e) {
        // Doesn't matter
    }
    waiting = false;
    consoleLog('[INFO] all tests ended at ' + new Date());
    if (typeof config.CHANGELIST === 'undefined' || config.CHANGELIST === null) {
        config.CHANGELIST = getCurrentChangelist(true);
    }
    if (runLog.length > 0) {
        try {
            fs.writeFileSync(path.join(config.reportsBasePath, config.WAKANDA_BRANCH, config.TEST_BRANCH, config.CHANGELIST.toString(), 'runlog.json'), JSON.stringify(runLog));
        } catch (e) {
            consoleLog('[WARN] cannot write global log file (1)', e);
        }
    }
    if (newChangelist === null && config.CHANGELIST !== null) {
        newChangelist = config.CHANGELIST;
    }
    state.queue = [];
    state.done = [];
    state.currentJob = -1;
    state.changelist = newChangelist;
    config.CHANGELIST = newChangelist;
    if (doNotOverwriteState === false) {
        try {
            fs.writeFileSync(path.join(config.reportsBasePath, 'state.json'), JSON.stringify(state));

        } catch (e) {
            consoleLog('[WARN] cannot write current state (2)', e);
        }
    }
    if (typeof config.automatic !== "undefined" && config.automatic === true && runFromWeb === false) {
        frontendReady = false;
        var actual = [];
        var expected = [];
        try {
            var availables = JSON.parse(fs.readFileSync(path.join(config.reportsBasePath, 'availableTestRuns.json')).toString());
            availables.forEach(function(available) {
                expected.push(parseInt(available.changelist));
            });
        } catch (e) {

        }
        try {
            var dir = path.join(config.reportsBasePath, config.WAKANDA_BRANCH, config.TEST_BRANCH);
            fs.readdirSync(dir).forEach(function(fileName) {
                if (/^[0-9]+$/.test(fileName) === true) {
                    actual.push(parseInt(fileName));
                }
            });
        } catch (e) {

        }
        actual = arrayUnique(actual);
        actual.sort();
        expected = arrayUnique(expected);
        expected.sort();
        var resultsHaveError = false;
        if (actual.length !== expected.length) {
            consoleLog('[WARN] error in results - expected length: ' + expected.length + ' / actual length: ' + actual.length);
            resultsHaveError = true;
        } else {
            for (var i = 0; i < actual.length; i++) {
                if (actual[i] !== expected[i]) {
                    consoleLog('[WARN] error in results - expected changelist: ' + expected[i] + ' / actual changelist: ' + actual[i]);
                    resultsHaveError = true;
                    break;
                }
            }
        }
        if (resultsHaveError === true && forceRebuild === true) {
            cachedData.availableTestRuns = null;
            try {
                fs.unlinkSync(path.join(config.reportsBasePath, 'availableTestRuns.json'));
            } catch (e) {
                // Doesn't matter
            }
            if (doNotOverwriteState === false) {
                try {
                    consoleLog('[INFO] clear current state (1)');
                    fs.unlinkSync(path.join(config.reportsBasePath, 'state.json'));
                } catch (e) {
                    // Doesn't matter
                }
            }
            try {
                fs.unlinkSync(path.join(config.reportsBasePath, 'current.json'));
            } catch (e) {
                // Doesn't matter
            }
            consoleLog('[WARN] rebuilding data (FORCED), this could take some time...');
            clearCachedData();
            clearCache();
        } else {
            consoleLog('[WARN] rebuilding data, this could take some time...');
            clearCache();
        }
        getListOfAvailableTestRuns(function(listOfAvailableTestRuns) {
            getGraphDataForTestRun(listOfAvailableTestRuns[0], function() {
                if (newChangelist === null) {
                    previousChangelist = getCurrentChangelist(true);
                } else {
                    previousChangelist = parseInt(newChangelist);
                }
                newChangelist = null;
                running = false;
                deployingNewWakandaBuild = false;
                downloadingNewWakandaBuild = false;
                downloadingNewWakandaBuildDone = false;
                downloadingNewWakandaBuildExpect = 0;
                deployingNewWakandaInstaller = false;
                downloadingNewWakandaInstaller = false;
                downloadingNewWakandaInstallerDone = false;
                downloadingNewWakandaInstallerExpect = 0;
                deployingNew4DBuild = false;
                downloadingNew4DBuild = false;
                downloadingNew4DBuildDone = false;
                downloadingNew4DBuildExpect = 0;
                currentServerPath = null;
                currentStudioPath = null;
                currentInstallerPath = null;
                current4DServerPath = null;
                currentShellPath = null;
                if (doNotExit === true) {
                    frontendReady = true;
                    clearTimeout(shutdownTimeout);
                    if (typeof config.hub !== 'undefined' && typeof config.hub.listen !== 'undefined' && config.hub.listen === true) {
                        hello();
                        consoleLog('[INFO] waiting for a new build (>' + previousChangelist + ')...');
                    } else {
                        consoleLog('[WARN] not listening to the Hub and no action given, so there is nothing to do right now...');
                    }
                }
                if (shutDown === false && doNotExit === false) {
                    consoleLog('[INFO] exit');
                    exitGracefully();
                }
            }, true);
        }, true);
    } else {
        if (doNotExit === true) {
            clearTimeout(shutdownTimeout);
            if (typeof config.hub !== 'undefined' && typeof config.hub.listen !== 'undefined' && config.hub.listen === true) {
                hello();
                consoleLog('[INFO] waiting for a new build (>' + previousChangelist + ')...');
            } else {
                consoleLog('[WARN] not listening to the Hub and no action given, so there is nothing to do right now...');
            }
        }
        if (shutDown === false && doNotExit === false) {
            consoleLog('[INFO] exit');
            exitGracefully();
        }
    }
}

// Get current Shell path
function getCurrentShellPath(changelist) {
    if (currentShellPath !== null) {
        return currentShellPath;
    } else {
        var found = null;
        if (isMac()) {
            var shellApp = findFiles(path.join(config.BUILD_TEST_DIR, changelist.toString()), /^wakanda$/);
            if (shellApp && shellApp.length === 1) {
                found = shellApp[0];
            }
        } else if (isLinux()) {
            var shellApp = findFiles(path.join(config.BUILD_TEST_DIR, changelist.toString()), /^wakanda$/);
            if (shellApp && shellApp.length === 1) {
                found = shellApp[0];
            }
        }
        if (found !== null) {
            return found;
        }
        return config.WAKANDA_SHELL_PATH;
    }
}

// Get current Server path
function getCurrentServerPath(changelist) {
    if (currentServerPath !== null) {
        return currentServerPath;
    } else {
        var found = null;
        if (isMac()) {
            var wakApps = findFiles(path.join(config.BUILD_TEST_DIR, changelist.toString()), /^wakanda.*(studio|server)$/i);
            wakApps.forEach(function(wakApp) {
                if (/server/i.test(wakApp)) {
                    found = wakApp;
                }
            });
        } else if (isWindows()) {
            var wakApps = findFiles(path.join(config.BUILD_TEST_DIR, changelist.toString()), /^wakanda.*\.exe$/i);
            wakApps.forEach(function(wakApp) {
                if (/server/i.test(wakApp)) {
                    found = wakApp;
                }
            });
        } else if (isLinux()) {
            var wakApps = findFiles(path.join(config.BUILD_TEST_DIR, changelist.toString()), /^wakanda.*-server$/i);
            wakApps.forEach(function(wakApp) {
                if (/server\/wakanda/i.test(wakApp)) {
                    found = wakApp;
                } else if (/bin\/wakanda/i.test(wakApp)) {
                    found = wakApp;
                }
            });
        }
        if (found !== null) {
            return found;
        }
        return config.WAKANDA_SERVER_PATH;
    }
}

// Get current Studio path
function getCurrentStudioPath(changelist) {
    if (typeof changelist === "undefined") {
        changelist = getCurrentChangelist();
    }
    if (isLinux()) {
        return {
            path: '',
            folder: ''
        };
    }
    if (currentStudioPath !== null) {
        if (isMac()) {
            return {
                path: path.dirname(path.dirname(path.dirname(currentStudioPath))),
                folder: path.dirname(path.dirname(currentStudioPath))
            };
        } else {
            return {
                path: currentStudioPath,
                folder: path.dirname(currentStudioPath)
            };
        }
    } else {
        var found = null;
        if (isMac()) {
            var wakApps = findFiles(path.join(config.BUILD_TEST_DIR, changelist.toString()), /^wakanda.*(studio|server)$/i);
            wakApps.forEach(function(wakApp) {
                if (/studio/i.test(wakApp)) {
                    found = wakApp;
                }
            });
        } else if (isWindows()) {
            var wakApps = findFiles(path.join(config.BUILD_TEST_DIR, changelist.toString()), /^wakanda.*\.exe$/i);
            wakApps.forEach(function(wakApp) {
                if (/studio/i.test(wakApp)) {
                    found = wakApp;
                }
            });
        }
        if (found !== null) {
            if (isMac()) {
                return {
                    path: path.dirname(path.dirname(path.dirname(found))),
                    folder: path.dirname(path.dirname(found))
                };
            } else {
                return {
                    path: found,
                    folder: path.dirname(found)
                };
            }
        }
        return {
            path: config.WAKANDA_STUDIO_PATH,
            folder: config.WAKANDA_STUDIO_FOLDER
        };
    }
}

// Get current installer path
function getCurrentInstallerPath(changelist) {
    if (currentInstallerPath !== null) {
        return currentInstallerPath;
    } else {
        var paths = [];
        if (isMac()) {
            var wakApps = findFiles(path.join(config.BUILD_TEST_DIR, changelist.toString()), /\.dmg$/i);
            wakApps.forEach(function(wakApp) {
                paths.push(wakApp);
            });
        } else if (isWindows()) {
            var wakApps = findFiles(path.join(config.BUILD_TEST_DIR, changelist.toString()), /\.msi$/i);
            wakApps.forEach(function(wakApp) {
                paths.push(wakApp);
            });
        } else if (isLinux()) {
            var wakApps = findFiles(path.join(config.BUILD_TEST_DIR, changelist.toString()), /\.(deb|tgz)$/i);
            wakApps.forEach(function(wakApp) {
                paths.push(wakApp);
            });
        }
        return paths;
    }
}

// Get current 4D Server path
function getCurrent4DServerPath(changelist) {
    if (isLinux()) {
        return '';
    }
    if (current4DServerPath !== null) {
        return current4DServerPath;
    } else {
        var found = null;
        if (isMac()) {
            var wakApps = findFiles(path.join(config.BUILD_TEST_DIR, changelist.toString()), /^4d.*server$/i);
            wakApps.forEach(function(wakApp) {
                found = wakApp;
            });
        } else if (isWindows()) {
            var wakApps = findFiles(path.join(config.BUILD_TEST_DIR, changelist.toString()), /^4d.*\.exe$/i);
            wakApps.forEach(function(wakApp) {
                found = wakApp;
            });
        }
        if (found !== null) {
            return found;
        }
        if (isMac()) {
            var wakApps = findFiles(config.BUILD_TEST_DIR, /^4d.*server$/i);
            wakApps.forEach(function(wakApp) {
                found = wakApp;
            });
        } else if (isWindows()) {
            var wakApps = findFiles(config.BUILD_TEST_DIR, /^4d.*\.exe$/i);
            wakApps.forEach(function(wakApp) {
                found = wakApp;
            });
        }
        return found;
    }
}

// Run the given test
function runTest(testName, callback, inChain) {
    loadConfig(true);
    getCrashlocationContentBefore();
    startMonitoring();
    hello(true);
    if (typeof inChain === 'undefined') {
        inChain = false;
    }
    clearTimeout(softMavenKillTimeout);
    clearTimeout(hardMavenKillTimeout);
    clearTimeout(softCLIKillTimeout);
    clearTimeout(hardCLIKillTimeout);
    clearTimeout(softKillTimeout);
    clearTimeout(hardKillTimeout);
    clearTimeout(serverReadyRequestTimeout);
    clearTimeout(shutdownTimeout);
    clearTimeout(shellProcessKill);
    var calledThatDamnCallbackAlready = false;
    async.series([

            function(mainSerieCallback) {
                killMainProcesses();
                setTimeout(function() {
                    mainSerieCallback(null);
                }, 125);
            },
            function(mainSerieCallback) {
                getProcessListBefore(mainSerieCallback);
            },
            function(mainSerieCallback) {
                calledThatDamnCallbackAlready = false;
                var callbackParams = {
                    testName: testName,
                    start: new Date(),
                    duration: 0,
                    stdout: null,
                    stderr: null,
                    error: null,
                    status: null,
                    result: null
                };
                callbackParams.changelist = getCurrentChangelist();
                config.CHANGELIST = callbackParams.changelist;
                testHasTimeouted = false;
                if (inChain === true) {
                    try {
                        var current = JSON.parse(fs.readFileSync(path.join(config.reportsBasePath, 'current.json')).toString());
                        if (current.testName === testName) {
                            current.tryCount++;
                        } else {
                            current = {
                                testName: testName,
                                tryCount: 1
                            };
                        }
                    } catch (e) {
                        var current = {
                            testName: testName,
                            tryCount: 1
                        };
                    }
                    if (current.tryCount > 2) {
                        consoleLog('[WARN] test ' + testName + ' failed twice, skip it');
                        callbackParams.error = 'test failed twice, skip it';
                        if (calledThatDamnCallbackAlready === false) {
                            calledThatDamnCallbackAlready = true;
                            mainSerieCallback(null);
                        }
                        return wrapVoidTest(callbackParams, callback);
                    } else {
                        try {
                            fs.writeFileSync(path.join(config.reportsBasePath, 'current.json'), JSON.stringify(current));
                        } catch (e) {
                            consoleLog('[WARN] cannot write current info (1)', e);
                        }
                        consoleLog('[INFO] launch test ' + testName.bold.white + ' on changelist '.grey + config.CHANGELIST.toString().white + (' (automatic - try ' + current.tryCount + '/2)').grey);
                    }
                } else {
                    consoleLog('[INFO] launch test ' + testName.bold.white + ' on changelist '.grey + config.CHANGELIST.toString().white + ' (manual)'.grey);
                }
                var testPath = testName.toLowerCase().split('_');
                var parentPath = testPath.slice(0, testPath.length - 1);
                var pom = null;
                parentPath = parentPath.map(function(elt) {
                    if (elt === 'main') {
                        return 'core';
                    }
                    return elt;
                });
                parentPath = actualPath(path.join(config.P4_WORKSPACE_PATH, 'depot', 'Wakanda', config.WAKANDA_BRANCH, parentPath[0], 'tests', parentPath.slice(1).join(path.sep)));
                if (testPath[testPath.length - 1] === 'main') {
                    try {
                        var statMaven = fs.statSync(actualPath(path.join(parentPath, 'pom.xml')));
                    } catch (e) {
                        var statMaven = false;
                    }
                    try {
                        var statOther = fs.statSync(actualPath(path.join(parentPath, 'pom.json')));
                    } catch (e) {
                        var statOther = false;
                    }
                    try {
                        var statMaven2 = fs.statSync(actualPath(path.join(parentPath, 'core', 'pom.xml')));
                    } catch (e) {
                        var statMaven2 = false;
                    }
                    try {
                        var statOther2 = fs.statSync(actualPath(path.join(parentPath, 'core', 'pom.json')));
                    } catch (e) {
                        var statOther2 = false;
                    }
                    try { // NEW ARCHI
                        var statNewArchi = fs.statSync(actualPath(path.join(parentPath, 'test.conf.json')));
                    } catch (e) {
                        var statNewArchi = false;
                    }
                    try { // NEW ARCHI
                        var statNewArchi2 = fs.statSync(actualPath(path.join(parentPath, 'core', 'test.conf.json')));
                    } catch (e) {
                        var statNewArchi2 = false;
                    }
                    if (statNewArchi && statNewArchi.isFile()) { // NEW ARCHI
                        testPath = parentPath;
                        try {
                            pom = JSON.parse(fs.readFileSync(actualPath(path.join(parentPath, 'test.conf.json'))).toString());
                            pom.newArchi = true;
                        } catch (e) {
                            consoleLog('[ERROR] cannot parse test.conf.json file (1)', e);
                            callbackParams.error = e;
                            if (calledThatDamnCallbackAlready === false) {
                                calledThatDamnCallbackAlready = true;
                                mainSerieCallback(null);
                            }
                            return wrapVoidTest(callbackParams, callback);
                        }
                    } else if (statNewArchi2 && statNewArchi2.isFile()) { // NEW ARCHI
                        parentPath = actualPath(path.join(parentPath, 'core'));
                        testPath = parentPath;
                        try {
                            pom = JSON.parse(fs.readFileSync(actualPath(path.join(parentPath, 'test.conf.json'))).toString());
                            pom.newArchi = true;
                        } catch (e) {
                            consoleLog('[ERROR] cannot parse test.conf.json file (2)', e);
                            callbackParams.error = e;
                            if (calledThatDamnCallbackAlready === false) {
                                calledThatDamnCallbackAlready = true;
                                mainSerieCallback(null);
                            }
                            return wrapVoidTest(callbackParams, callback);
                        }
                    } else if (statMaven && statMaven.isFile() && (typeof config.noJavaTest === 'undefined' || config.noJavaTest === false)) {
                        testPath = parentPath;
                        pom = fs.readFileSync(actualPath(path.join(parentPath, 'pom.xml'))).toString();
                        try {
                            // !!!!!
                            parseString(pom, function(err, rawresult) {
                                if (err) {
                                    consoleLog('[ERROR] cannot parse POM file (1)', err);
                                    callbackParams.error = err;
                                    if (calledThatDamnCallbackAlready === false) {
                                        calledThatDamnCallbackAlready = true;
                                        mainSerieCallback(null);
                                    }
                                    return wrapVoidTest(callbackParams, callback);
                                }
                                pom = {};
                                for (var prop in rawresult.project.properties[0]) {
                                    if (/^virtualpath$/i.test(prop) === true) {
                                        if (typeof pom.virtualPath === 'undefined') {
                                            pom.virtualPath = [];
                                        }
                                        pom.virtualPath.push({
                                            name: rawresult.project.properties[0][prop][0].$.name,
                                            path: rawresult.project.properties[0][prop][0].$.path,
                                        });
                                    } else {
                                        if (/^\d+$/.test(rawresult.project.properties[0][prop][0]) === true) {
                                            pom[prop.replace('jenkins.', '').toLowerCase()] = parseInt(rawresult.project.properties[0][prop][0]);
                                        } else {
                                            pom[prop.replace('jenkins.', '').toLowerCase()] = rawresult.project.properties[0][prop][0].toLowerCase();
                                        }
                                    }
                                }
                                pom.kind = 'maven';
                            });
                        } catch (e) {
                            consoleLog('[ERROR] cannot parse POM file (1b)', e);
                            callbackParams.error = e;
                            if (calledThatDamnCallbackAlready === false) {
                                calledThatDamnCallbackAlready = true;
                                mainSerieCallback(null);
                            }
                            return wrapVoidTest(callbackParams, callback);
                        }
                    } else if (statOther && statOther.isFile()) {
                        testPath = actualPath(path.join(parentPath, 'test.js'));
                        try {
                            pom = JSON.parse(fs.readFileSync(actualPath(path.join(parentPath, 'pom.json'))).toString());
                        } catch (e) {
                            consoleLog('[ERROR] cannot parse POM file (2)', e);
                            callbackParams.error = e;
                            if (calledThatDamnCallbackAlready === false) {
                                calledThatDamnCallbackAlready = true;
                                mainSerieCallback(null);
                            }
                            return wrapVoidTest(callbackParams, callback);
                        }
                    } else if (statMaven2 && statMaven2.isFile() && (typeof config.noJavaTest === 'undefined' || config.noJavaTest === false)) {
                        parentPath = actualPath(path.join(parentPath, 'core'));
                        testPath = parentPath;
                        pom = fs.readFileSync(actualPath(path.join(parentPath, 'pom.xml'))).toString();
                        try {
                            // !!!!!
                            parseString(pom, function(err, rawresult) {
                                if (err) {
                                    consoleLog('[ERROR] cannot parse POM file (3)', err);
                                    callbackParams.error = err;
                                    if (calledThatDamnCallbackAlready === false) {
                                        calledThatDamnCallbackAlready = true;
                                        mainSerieCallback(null);
                                    }
                                    return wrapVoidTest(callbackParams, callback);
                                }
                                pom = {};
                                for (var prop in rawresult.project.properties[0]) {
                                    if (/^virtualpath$/i.test(prop) === true) {
                                        if (typeof pom.virtualPath === 'undefined') {
                                            pom.virtualPath = [];
                                        }
                                        pom.virtualPath.push({
                                            name: rawresult.project.properties[0][prop][0].$.name,
                                            path: rawresult.project.properties[0][prop][0].$.path,
                                        });
                                    } else {
                                        if (/^\d+$/.test(rawresult.project.properties[0][prop][0]) === true) {
                                            pom[prop.replace('jenkins.', '').toLowerCase()] = parseInt(rawresult.project.properties[0][prop][0]);
                                        } else {
                                            pom[prop.replace('jenkins.', '').toLowerCase()] = rawresult.project.properties[0][prop][0].toLowerCase();
                                        }
                                    }
                                }
                                pom.kind = 'maven';
                            });
                        } catch (e) {
                            consoleLog('[ERROR] cannot parse POM file (3b)', e);
                            callbackParams.error = e;
                            if (calledThatDamnCallbackAlready === false) {
                                calledThatDamnCallbackAlready = true;
                                mainSerieCallback(null);
                            }
                            return wrapVoidTest(callbackParams, callback);
                        }
                    } else if (statOther2 && statOther2.isFile()) {
                        parentPath = actualPath(path.join(parentPath, 'core'));
                        testPath = actualPath(path.join(parentPath, 'test.js'));
                        try {
                            pom = JSON.parse(fs.readFileSync(actualPath(path.join(parentPath, 'pom.json'))).toString());
                        } catch (e) {
                            consoleLog('[ERROR] cannot parse POM file (4)', e);
                            callbackParams.error = e;
                            if (calledThatDamnCallbackAlready === false) {
                                calledThatDamnCallbackAlready = true;
                                mainSerieCallback(null);
                            }
                            return wrapVoidTest(callbackParams, callback);
                        }
                    } else {
                        consoleLog('[ERROR] POM not found or test disabled (1)');
                        callbackParams.error = 'POM not found or test disabled';
                        if (calledThatDamnCallbackAlready === false) {
                            calledThatDamnCallbackAlready = true;
                            mainSerieCallback(null);
                        }
                        return wrapVoidTest(callbackParams, callback);
                    }
                } else {
                    try {
                        var statOther = fs.statSync(actualPath(path.join(parentPath, 'pom.json')));
                    } catch (e) {
                        var statOther = false;
                    }
                    try { // NEW ARCHI
                        var statNewArchi = fs.statSync(actualPath(path.join(parentPath, 'test.conf.json')));
                    } catch (e) {
                        var statNewArchi = false;
                    }
                    if (statNewArchi && statNewArchi.isFile()) { // NEW ARCHI
                        testPath = parentPath;
                        try {
                            pom = JSON.parse(fs.readFileSync(actualPath(path.join(parentPath, 'test.conf.json'))).toString());
                            pom.newArchi = true;
                        } catch (e) {
                            consoleLog('[ERROR] cannot parse test.conf.json file (3)', e);
                            callbackParams.error = e;
                            if (calledThatDamnCallbackAlready === false) {
                                calledThatDamnCallbackAlready = true;
                                mainSerieCallback(null);
                            }
                            return wrapVoidTest(callbackParams, callback);
                        }
                    } else if (statOther && statOther.isFile()) {
                        try {
                            pom = JSON.parse(fs.readFileSync(actualPath(path.join(parentPath, 'pom.json'))).toString());
                        } catch (e) {
                            consoleLog('[ERROR] cannot parse POM file (5)', e);
                            callbackParams.error = e;
                            if (calledThatDamnCallbackAlready === false) {
                                calledThatDamnCallbackAlready = true;
                                mainSerieCallback(null);
                            }
                            return wrapVoidTest(callbackParams, callback);
                        }
                        try {
                            var statTest = fs.statSync(actualPath(path.join(parentPath, 'test' + testPath[testPath.length - 1] + '.js')));
                            testPath = actualPath(path.join(parentPath, 'test' + testPath[testPath.length - 1] + '.js'));
                        } catch (e) {
                            consoleLog('[ERROR] cannot find test file (1)', e);
                            callbackParams.error = e;
                            if (calledThatDamnCallbackAlready === false) {
                                calledThatDamnCallbackAlready = true;
                                mainSerieCallback(null);
                            }
                            return wrapVoidTest(callbackParams, callback);
                        }
                    } else {
                        consoleLog('[ERROR] POM not found (2)');
                        callbackParams.error = 'POM not found';
                        if (calledThatDamnCallbackAlready === false) {
                            calledThatDamnCallbackAlready = true;
                            mainSerieCallback(null);
                        }
                        return wrapVoidTest(callbackParams, callback);
                    }
                }
                if (typeof pom.newArchi === 'undefined') {
                    pom.newArchi = false;
                }
                var testUUID = null;
                try {
                    var statUUID = fs.statSync(actualPath(path.join(parentPath, 'uuid')));
                } catch (e) {
                    var statUUID = false;
                    consoleLog('[WARN] UUID not found (1)');
                }
                if (statUUID && statUUID.isFile()) {
                    try {
                        testUUID = fs.readFileSync(actualPath(path.join(parentPath, 'uuid'))).toString();
                    } catch (e) {
                        consoleLog('[WARN] cannot read UUID (1)');
                    }
                }
                pom.uuid = testUUID;
                var testSetup = {};
                testSetup.pom = JSON.parse(JSON.stringify(pom));
                testSetup.config = JSON.parse(JSON.stringify(config));
                testSetup.config.CHANGELIST = callbackParams.changelist;
                testSetup.config.UTILS_TESTS_PATH = actualPath(path.join(testSetup.config.P4_WORKSPACE_PATH, 'RIA', 'tests', testSetup.config.TEST_BRANCH, 'utils'));
                testSetup.destBasePath = actualPath(testSetup.config.reportsBasePath);
                callbackParams.pom = testSetup.pom;
                try {
                    fs.mkdirSync(path.join(testSetup.destBasePath, testSetup.config.WAKANDA_BRANCH));
                } catch (e) {
                    if (e.code !== 'EEXIST') {
                        consoleLog('[ERROR] cannot create result folder (1)', e);
                        callbackParams.error = e;
                        if (calledThatDamnCallbackAlready === false) {
                            calledThatDamnCallbackAlready = true;
                            mainSerieCallback(null);
                        }
                        return wrapVoidTest(callbackParams, callback, testSetup);
                    }
                }
                try {
                    fs.mkdirSync(path.join(testSetup.destBasePath, testSetup.config.WAKANDA_BRANCH, testSetup.config.TEST_BRANCH));
                } catch (e) {
                    if (e.code !== 'EEXIST') {
                        consoleLog('[ERROR] cannot create result folder (2)', e);
                        callbackParams.error = e;
                        if (calledThatDamnCallbackAlready === false) {
                            calledThatDamnCallbackAlready = true;
                            mainSerieCallback(null);
                        }
                        return wrapVoidTest(callbackParams, callback, testSetup);
                    }
                }
                try {
                    fs.mkdirSync(path.join(testSetup.destBasePath, testSetup.config.WAKANDA_BRANCH, testSetup.config.TEST_BRANCH, testSetup.config.CHANGELIST.toString()));
                } catch (e) {
                    if (e.code !== 'EEXIST') {
                        consoleLog('[ERROR] cannot create result folder (3)', e);
                        callbackParams.error = e;
                        if (calledThatDamnCallbackAlready === false) {
                            calledThatDamnCallbackAlready = true;
                            mainSerieCallback(null);
                        }
                        return wrapVoidTest(callbackParams, callback, testSetup);
                    }
                }
                try {
                    fs.mkdirSync(path.join(testSetup.destBasePath, testSetup.config.WAKANDA_BRANCH, testSetup.config.TEST_BRANCH, testSetup.config.CHANGELIST.toString(), testName));
                } catch (e) {
                    if (e.code !== 'EEXIST') {
                        consoleLog('[ERROR] cannot create result folder (4)', e);
                        callbackParams.error = e;
                        if (calledThatDamnCallbackAlready === false) {
                            calledThatDamnCallbackAlready = true;
                            mainSerieCallback(null);
                        }
                        return wrapVoidTest(callbackParams, callback, testSetup);
                    }
                }
                var testCount = 0;
                var testCountDone = false;
                while (testCountDone === false) {
                    try {
                        fs.mkdirSync(path.join(testSetup.destBasePath, testSetup.config.WAKANDA_BRANCH, testSetup.config.TEST_BRANCH, testSetup.config.CHANGELIST.toString(), testName, testCount.toString()));
                        testCountDone = true;
                    } catch (e) {
                        if (e.code !== 'EEXIST') {
                            consoleLog('[ERROR] cannot create result folder (5)', e);
                            callbackParams.error = e;
                            if (calledThatDamnCallbackAlready === false) {
                                calledThatDamnCallbackAlready = true;
                                mainSerieCallback(null);
                            }
                            return wrapVoidTest(callbackParams, callback, testSetup);
                        } else {
                            testCount++;
                        }
                    }
                }
                testSetup.destFullPath = actualPath(path.join(testSetup.destBasePath, testSetup.config.WAKANDA_BRANCH, testSetup.config.TEST_BRANCH, testSetup.config.CHANGELIST.toString(), testName, testCount.toString()));
                callbackParams.resultDir = testSetup.destFullPath;
                // !!!!!
                temp.mkdir({
                    dir: testSetup.config.BUILD_TEMP_DIR
                }, function(err, dirPath) {
                    if (err) {
                        consoleLog('[ERROR] cannot create workspace (1)', err);
                        callbackParams.error = err;
                        if (calledThatDamnCallbackAlready === false) {
                            calledThatDamnCallbackAlready = true;
                            mainSerieCallback(null);
                        }
                        return wrapVoidTest(callbackParams, callback, testSetup);
                    }
                    callbackParams.tmpDir = dirPath;
                    testSetup.config.WORKSPACE = dirPath;
                    testSetup.config.JOB_NAME = testName;
                    testSetup.config.WAKANDA_SHELL_PATH = getCurrentShellPath(callbackParams.changelist);
                    testSetup.config.WAKANDA_SERVER_PATH = getCurrentServerPath(callbackParams.changelist);
                    var _studioPaths = getCurrentStudioPath(callbackParams.changelist);
                    testSetup.config.WAKANDA_STUDIO_PATH = _studioPaths.path;
                    testSetup.config.WAKANDA_STUDIO_FOLDER = _studioPaths.folder;
                    testSetup.config.WAKANDA_INSTALLER_PATH = getCurrentInstallerPath(callbackParams.changelist).join(',');
                    testSetup.config.FOURD_SERVER_PATH = getCurrent4DServerPath(callbackParams.changelist);
                    testSetup.config.BUILD_TEST_DIR = path.join(testSetup.config.BUILD_TEST_DIR, callbackParams.changelist.toString());
                    testSetup.config.WAK_TESTING_DIR = testSetup.config.BUILD_TEST_DIR;
                    testSetup.config.PERFORCE_WS = testSetup.config.P4_WORKSPACE_PATH;
                    testSetup.config.PHANTOMJS_SCRIPT = path.join(testSetup.config.P4_WORKSPACE_PATH, 'RIA', 'tests', testSetup.config.TEST_BRANCH, 'utils', 'common', 'csjs', 'run.js');
                    testSetup.config.WAKANDA_DEFAULT_SOLUTION = path.join(testSetup.config.P4_WORKSPACE_PATH, 'RIA', 'tests', testSetup.config.TEST_BRANCH, 'utils', 'common', 'defaultsolution', 'BasicTestProjectSolution', 'BasicTestProject.waSolution');
                    testSetup.config.SERVER_TESTS_PATH = actualPath(path.join(testSetup.config.P4_WORKSPACE_PATH, 'depot', 'Wakanda', testSetup.config.WAKANDA_BRANCH, 'server', 'tests'));
                    testSetup.config.STUDIO_TESTS_PATH = actualPath(path.join(testSetup.config.P4_WORKSPACE_PATH, 'depot', 'Wakanda', testSetup.config.WAKANDA_BRANCH, 'studio', 'tests'));
                    testSetup.config.COMMON_TESTS_PATH = actualPath(path.join(testSetup.config.P4_WORKSPACE_PATH, 'depot', 'Wakanda', testSetup.config.WAKANDA_BRANCH, 'common', 'tests'));
                    testSetup.config.CSJS_HEADLESS_SCRIPT = path.join(__dirname, 'utils', 'csjs-headless.js'); // NEW ARCHI
                    testSetup.config.CSJS_HEADLESS_BIN = testSetup.config.PHANTOMJS_PATH;
                    for (var i in process.env) {
                        if (typeof testSetup.config[i] === 'undefined') {
                            testSetup.config[i] = process.env[i];
                        }
                    }
                    if (typeof config.subversion === 'string') {
                        testSetup.config.subversion = config.subversion;
                    }
                    if (isLinux() === true) {
                        if (typeof testSetup.config.ODBCINI === 'undefined') testSetup.config.ODBCINI = '/etc/odbc.ini';
                        if (typeof testSetup.config.ODBCSYSINI === 'undefined') testSetup.config.ODBCSYSINI = '/etc';
                    }
                    testSetup.testName = testName;
                    testSetup.testPath = testPath;
                    testSetup.callbackParams = callbackParams;
                    FourDBFileToOpen = null;
                    if (isLinux() === false || typeof pom.donotlaunch4d === 'undefined' || pom.donotlaunch4d !== 'true') {
                        if (/4d(?!p)/i.test(testName)) {
                            var fourdbFiles = findFiles(path.dirname(testPath), /\.4db/i);
                            if (fourdbFiles.length > 0) {
                                fourdbFiles.forEach(function(fourdbFile) {
                                    if (/\(/.test(fourdbFile) === false) {
                                        FourDBFileToOpen = actualPath(fourdbFile);
                                    }
                                });
                            }
                        }
                    }
                    switch (pom.kind) {
                        case 'csjs-headless': // NEW ARCHI
                            testSetup.config.TESTBASEPATH = testPath;
                            testSetup.config.SCRIPTPATH = testPath;
                            testSetup.testSolutionPath = actualPath(path.resolve(testPath, pom['solution-path']));
                            testSetup.testURL = pom['page-url'] + '?waktest-path=' + actualPath(path.resolve(testPath, pom['files'][0])).replace(/\\/ig, '/');
                            runJSTest(testSetup, function(res) {
                                return callback(res);
                            });
                            break;
                        case 'maven':
                            if (FourDBFileToOpen !== null) {
                                consoleLog('[WARN] about to launch 4D Server');
                                if (typeof config.no4DTest !== 'undefined' && config.no4DTest === true) {
                                    consoleLog('[ERROR] 4D tests are disabled');
                                    callbackParams.error = '4D tests are disabled';
                                    if (calledThatDamnCallbackAlready === false) {
                                        calledThatDamnCallbackAlready = true;
                                        mainSerieCallback(null);
                                    }
                                    return wrapVoidTest(callbackParams, callback, testSetup);
                                }
                                // TODO: URL 4dwebtest for 4D changelist !!!!! et éviter de lancer le test lui-même si 4D ne s'est pas bien lancé
                                current4DServerPath = getCurrent4DServerPath(callbackParams.changelist);
                                if (FourDServerProcess !== null && FourDServerProcess.pid > 0 && FourDServerProcess.pid != process.pid) {
                                    FourDServerProcess.kill('SIGKILL');
                                }
                                try {
                                    FourDServerProcess = spawn(current4DServerPath, [FourDBFileToOpen], {
                                        cwd: testSetup.config.WORKSPACE,
                                        env: testSetup.config
                                    });
                                } catch (e) {
                                    consoleLog('[ERROR] cannot launch 4D Server (1a):', current4DServerPath, FourDBFileToOpen, e);
                                    callbackParams.error = e;
                                    if (calledThatDamnCallbackAlready === false) {
                                        calledThatDamnCallbackAlready = true;
                                        mainSerieCallback(null);
                                    }
                                    return wrapVoidTest(callbackParams, callback, testSetup);
                                }
                                FourDServerProcess.stdout.on('data', function(data) {
                                    try {
                                        fs.appendFileSync(path.join(opt.destFullPath, 'stdout-4d.txt'), data.toString());
                                    } catch (e) {

                                    }
                                    consoleLog('[STDOUT] [4D] ' + data.toString());
                                });
                                FourDServerProcess.stderr.on('data', function(data) {
                                    try {
                                        fs.appendFileSync(path.join(opt.destFullPath, 'stderr-4d.txt'), data.toString());
                                    } catch (e) {

                                    }
                                    consoleLog('[STDERR] [4D] ' + data.toString());
                                });
                                // !!!!!
                                FourDServerProcess.on('error', function(e) {
                                    FourDServerProcess = null;
                                    consoleLog('[ERROR] cannot launch 4D Server (1b):', current4DServerPath, FourDBFileToOpen, e);
                                    callbackParams.error = e;
                                    if (calledThatDamnCallbackAlready === false) {
                                        calledThatDamnCallbackAlready = true;
                                        mainSerieCallback(null);
                                    }
                                    return wrapVoidTest(callbackParams, callback, testSetup);
                                });
                                FourDServerProcess.on('close', function(code) {
                                    FourDServerProcess = null;
                                });
                            }
                            setTimeout(function() {
                                testSetup.config.TESTBASEPATH = testPath;
                                testSetup.config.SCRIPTPATH = testPath;
                                runMavenTest(testSetup, function(res) {
                                    return callback(res);
                                });
                            }, (FourDBFileToOpen !== null ? 4 * 60 * 1000 : 0));
                            break;
                        case 'cli':
                            if (FourDBFileToOpen !== null) {
                                consoleLog('[WARN] about to launch 4D Server');
                                if (typeof config.no4DTest !== 'undefined' && config.no4DTest === true) {
                                    consoleLog('[ERROR] 4D tests are disabled');
                                    callbackParams.error = '4D tests are disabled';
                                    if (calledThatDamnCallbackAlready === false) {
                                        calledThatDamnCallbackAlready = true;
                                        mainSerieCallback(null);
                                    }
                                    return wrapVoidTest(callbackParams, callback, testSetup);
                                }
                                // TODO: URL 4dwebtest for 4D changelist !!!!! et éviter de lancer le test lui-même si 4D ne s'est pas bien lancé
                                current4DServerPath = getCurrent4DServerPath(callbackParams.changelist);
                                if (FourDServerProcess !== null && FourDServerProcess.pid > 0 && FourDServerProcess.pid != process.pid) {
                                    FourDServerProcess.kill('SIGKILL');
                                }
                                try {
                                    FourDServerProcess = spawn(current4DServerPath, [FourDBFileToOpen], {
                                        cwd: testSetup.config.WORKSPACE,
                                        env: testSetup.config
                                    });
                                } catch (e) {
                                    consoleLog('[ERROR] cannot launch 4D Server (1a):', current4DServerPath, FourDBFileToOpen, e);
                                    callbackParams.error = e;
                                    if (calledThatDamnCallbackAlready === false) {
                                        calledThatDamnCallbackAlready = true;
                                        mainSerieCallback(null);
                                    }
                                    return wrapVoidTest(callbackParams, callback, testSetup);
                                }
                                FourDServerProcess.stdout.on('data', function(data) {
                                    try {
                                        fs.appendFileSync(path.join(opt.destFullPath, 'stdout-4d.txt'), data.toString());
                                    } catch (e) {

                                    }
                                    consoleLog('[STDOUT] [4D] ' + data.toString());
                                });
                                FourDServerProcess.stderr.on('data', function(data) {
                                    try {
                                        fs.appendFileSync(path.join(opt.destFullPath, 'stderr-4d.txt'), data.toString());
                                    } catch (e) {

                                    }
                                    consoleLog('[STDERR] [4D] ' + data.toString());
                                });
                                // !!!!!
                                FourDServerProcess.on('error', function(e) {
                                    FourDServerProcess = null;
                                    consoleLog('[ERROR] cannot launch 4D Server (1b):', current4DServerPath, FourDBFileToOpen, e);
                                    callbackParams.error = e;
                                    if (calledThatDamnCallbackAlready === false) {
                                        calledThatDamnCallbackAlready = true;
                                        mainSerieCallback(null);
                                    }
                                    return wrapVoidTest(callbackParams, callback, testSetup);
                                });
                                FourDServerProcess.on('close', function(code) {
                                    FourDServerProcess = null;
                                });
                            }
                            setTimeout(function() {
                                testSetup.config.TESTBASEPATH = path.dirname(testPath);
                                testSetup.config.SCRIPTPATH = path.dirname(testPath);
                                runCLITest(testSetup, function(res) {
                                    return callback(res);
                                });
                            }, (FourDBFileToOpen !== null ? 4 * 60 * 1000 : 0));
                            break;
                        case 'csjs':
                        case 'ssjs':
                            if (pom.kind === 'ssjs' && pom.newArchi === true) { // NEW ARCHI
                                testSetup.config.TESTBASEPATH = testPath;
                                testSetup.config.SCRIPTPATH = testPath;
                                if (typeof pom['base-url'] !== 'undefined') {
                                    testSetup.testURL = pom['base-url'];
                                } else {
                                    testSetup.testURL = 'http://' + testSetup.config.WAKANDA_URL;
                                }
                                testSetup.testSolutionPath = actualPath(path.resolve(testPath, pom['solution-path']));
                                testSetup.testFilePath = actualPath(path.resolve(testPath, pom['files'][0])).replace(/\\/ig, '/');
                                runJSTest(testSetup, function(res) {
                                    return callback(res);
                                });
                            } else {
                                testSetup.config.TESTBASEPATH = path.dirname(testPath);
                                testSetup.config.SCRIPTPATH = path.dirname(testPath);
                                var testSolutionCandidates = findFiles(testSetup.config.TESTBASEPATH, /test.*\.wasolution$/i, /test/i);
                                if (testSolutionCandidates.length === 0) {
                                    testSolutionCandidates = findFiles(testSetup.config.TESTBASEPATH, /.*\.wasolution$/i);
                                    if (testSolutionCandidates.length === 0) {
                                        testSetup.testSolutionPath = actualPath(testSetup.config.WAKANDA_DEFAULT_SOLUTION);
                                        testSetup.config.TESTBASEPATH = path.dirname(testSetup.testSolutionPath);
                                    } else if (testSolutionCandidates.length === 1) {
                                        testSetup.testSolutionPath = actualPath(testSolutionCandidates[0]);
                                    } else {
                                        testSetup.testSolutionPath = actualPath(testSolutionCandidates[0]);
                                        testSolutionCandidates.forEach(function(candidate) {
                                            if (path.basename(testPath).replace(/\.js/i, '').replace(/test/i, '').toLowerCase() === path.basename(candidate).replace(/\.wasolution/i, '').replace(/test/i, '').toLowerCase()) {
                                                testSetup.testSolutionPath = actualPath(candidate);
                                            }
                                        });
                                    }
                                } else if (testSolutionCandidates.length === 1) {
                                    testSetup.testSolutionPath = actualPath(testSolutionCandidates[0]);
                                } else {
                                    testSetup.testSolutionPath = actualPath(testSolutionCandidates[0]);
                                    testSolutionCandidates.forEach(function(candidate) {
                                        if (path.basename(testPath).replace(/\.js/i, '').toLowerCase() === path.basename(candidate).replace(/\.wasolution/i, '').toLowerCase()) {
                                            testSetup.testSolutionPath = actualPath(candidate);
                                        }
                                    });
                                }
                                if (pom.kind === 'csjs') {
                                    var foundThePage = false;
                                    var testPageCandidates = findFiles(testSetup.config.TESTBASEPATH, /^index\.html$/i, /.*/);
                                    for (var testPageCandidatesIter = 0; testPageCandidatesIter < testPageCandidates.length; testPageCandidatesIter++) {
                                        if (/\.wapage/i.test(testPageCandidates[testPageCandidatesIter]) === true) {
                                            foundThePage = true;
                                            break;
                                        }
                                    }
                                    if (foundThePage === false) {
                                        testPageCandidates = findFiles(testSetup.config.TESTBASEPATH, /^test\.html$/i, /.*/, /onunittestready/ig);
                                        if (testPageCandidates.length === 0) {
                                            testPageCandidates = findFiles(testSetup.config.TESTBASEPATH, /^index\.html$/i, /.*/, /onunittestready/ig);
                                            if (testPageCandidates.length === 0) {
                                                testSetup.testURL = null;
                                            } else {
                                                testSetup.testURL = '/index.html';
                                            }
                                        } else {
                                            testSetup.testURL = '/test.html';
                                        }
                                    } else {
                                        testSetup.testURL = '/index.waPage/index.html';
                                    }
                                }
                                if (typeof testSetup.config.sync_perforce === 'undefined' || testSetup.config.sync_perforce === true || testSetup.config.sync_perforce === 'true') {
                                    var pathToUpdate = [];
                                    if (FourDBFileToOpen !== null) {
                                        consoleLog('[WARN] about to launch 4D Server');
                                        if (typeof config.no4DTest !== 'undefined' && config.no4DTest === true) {
                                            consoleLog('[ERROR] 4D tests are disabled');
                                            callbackParams.error = '4D tests are disabled';
                                            if (calledThatDamnCallbackAlready === false) {
                                                calledThatDamnCallbackAlready = true;
                                                mainSerieCallback(null);
                                            }
                                            return wrapVoidTest(callbackParams, callback, testSetup);
                                        }
                                        // TODO: URL 4dwebtest for 4D changelist !!!!! et éviter de lancer le test lui-même si 4D ne s'est pas bien lancé
                                        current4DServerPath = getCurrent4DServerPath(callbackParams.changelist);
                                        if (FourDServerProcess !== null && FourDServerProcess.pid > 0 && FourDServerProcess.pid != process.pid) {
                                            FourDServerProcess.kill('SIGKILL');
                                        }
                                        try {
                                            FourDServerProcess = spawn(current4DServerPath, [FourDBFileToOpen], {
                                                cwd: testSetup.config.WORKSPACE,
                                                env: testSetup.config
                                            });
                                        } catch (e) {
                                            consoleLog('[ERROR] cannot launch 4D Server (1a):', current4DServerPath, FourDBFileToOpen, e);
                                            callbackParams.error = e;
                                            if (calledThatDamnCallbackAlready === false) {
                                                calledThatDamnCallbackAlready = true;
                                                mainSerieCallback(null);
                                            }
                                            return wrapVoidTest(callbackParams, callback, testSetup);
                                        }
                                        FourDServerProcess.stdout.on('data', function(data) {
                                            try {
                                                fs.appendFileSync(path.join(opt.destFullPath, 'stdout-4d.txt'), data.toString());
                                            } catch (e) {

                                            }
                                            consoleLog('[STDOUT] [4D] ' + data.toString());
                                        });
                                        FourDServerProcess.stderr.on('data', function(data) {
                                            try {
                                                fs.appendFileSync(path.join(opt.destFullPath, 'stderr-4d.txt'), data.toString());
                                            } catch (e) {

                                            }
                                            consoleLog('[STDERR] [4D] ' + data.toString());
                                        });
                                        // !!!!!
                                        FourDServerProcess.on('error', function(e) {
                                            FourDServerProcess = null;
                                            consoleLog('[ERROR] cannot launch 4D Server (1b):', current4DServerPath, FourDBFileToOpen, e);
                                            callbackParams.error = e;
                                            if (calledThatDamnCallbackAlready === false) {
                                                calledThatDamnCallbackAlready = true;
                                                mainSerieCallback(null);
                                            }
                                            return wrapVoidTest(callbackParams, callback, testSetup);
                                        });
                                        FourDServerProcess.on('close', function(code) {
                                            FourDServerProcess = null;
                                        });
                                    }
                                    setTimeout(function() {
                                        runJSTest(testSetup, function(res) {
                                            return callback(res);
                                        });
                                    }, (FourDBFileToOpen !== null ? 4 * 60 * 1000 : 0));
                                } else {
                                    if (FourDBFileToOpen !== null) {
                                        consoleLog('[WARN] about to launch 4D Server');
                                        if (typeof config.no4DTest !== 'undefined' && config.no4DTest === true) {
                                            consoleLog('[ERROR] 4D tests are disabled');
                                            callbackParams.error = '4D tests are disabled';
                                            if (calledThatDamnCallbackAlready === false) {
                                                calledThatDamnCallbackAlready = true;
                                                mainSerieCallback(null);
                                            }
                                            return wrapVoidTest(callbackParams, callback, testSetup);
                                        }
                                        // TODO: URL 4dwebtest for 4D changelist !!!!! et éviter de lancer le test lui-même si 4D ne s'est pas bien lancé
                                        current4DServerPath = getCurrent4DServerPath(callbackParams.changelist);
                                        if (FourDServerProcess !== null && FourDServerProcess.pid > 0 && FourDServerProcess.pid != process.pid) {
                                            FourDServerProcess.kill('SIGKILL');
                                        }
                                        try {
                                            FourDServerProcess = spawn(current4DServerPath, [FourDBFileToOpen], {
                                                cwd: testSetup.config.WORKSPACE,
                                                env: testSetup.config
                                            });
                                        } catch (e) {
                                            consoleLog('[ERROR] cannot launch 4D Server (1a):', current4DServerPath, FourDBFileToOpen, e);
                                            callbackParams.error = e;
                                            if (calledThatDamnCallbackAlready === false) {
                                                calledThatDamnCallbackAlready = true;
                                                mainSerieCallback(null);
                                            }
                                            return wrapVoidTest(callbackParams, callback, testSetup);
                                        }
                                        FourDServerProcess.stdout.on('data', function(data) {
                                            try {
                                                fs.appendFileSync(path.join(opt.destFullPath, 'stdout-4d.txt'), data.toString());
                                            } catch (e) {

                                            }
                                            consoleLog('[STDOUT] [4D] ' + data.toString());
                                        });
                                        FourDServerProcess.stderr.on('data', function(data) {
                                            try {
                                                fs.appendFileSync(path.join(opt.destFullPath, 'stderr-4d.txt'), data.toString());
                                            } catch (e) {

                                            }
                                            consoleLog('[STDERR] [4D] ' + data.toString());
                                        });
                                        // !!!!!
                                        FourDServerProcess.on('error', function(e) {
                                            FourDServerProcess = null;
                                            consoleLog('[ERROR] cannot launch 4D Server (1b):', current4DServerPath, FourDBFileToOpen, e);
                                            callbackParams.error = e;
                                            if (calledThatDamnCallbackAlready === false) {
                                                calledThatDamnCallbackAlready = true;
                                                mainSerieCallback(null);
                                            }
                                            return wrapVoidTest(callbackParams, callback, testSetup);
                                        });
                                        FourDServerProcess.on('close', function(code) {
                                            FourDServerProcess = null;
                                        });
                                    }
                                    setTimeout(function() {
                                        runJSTest(testSetup, function(res) {
                                            return callback(res);
                                        });
                                    }, (FourDBFileToOpen !== null ? 4 * 60 * 1000 : 0));
                                }
                            }
                            break;
                        case 'shell':
                            testSetup.config.TESTBASEPATH = actualPath(parentPath);
                            testSetup.config.SCRIPTPATH = actualPath(parentPath);
                            var buildSteps = [];
                            try {
                                if (isMac()) {
                                    buildSteps = pom.builders.Mac.build;
                                } else if (isWindows()) {
                                    buildSteps = pom.builders.Windows.build;
                                } else if (isLinux()) {
                                    buildSteps = pom.builders.Linux.build;
                                }
                            } catch (e) {

                            }
                            if (buildSteps.length > 0) {
                                var UTILS_TESTS_PATH = actualPath(path.join(testSetup.config.P4_WORKSPACE_PATH, 'RIA', 'tests', testSetup.config.TEST_BRANCH, 'utils'));
                                var SERVER_TESTS_PATH = actualPath(path.join(testSetup.config.P4_WORKSPACE_PATH, 'depot', 'Wakanda', testSetup.config.WAKANDA_BRANCH, 'server', 'tests'));
                                var globalStdout = '';
                                var globalSdterr = '';
                                async.eachSeries(
                                    buildSteps,
                                    function(buildStep, serieCallback) {
                                        clearTimeout(shellProcessKill);
                                        shellProcessKilled = false;
                                        testHasTimeouted = false;
                                        var commands = buildStep.command.split(' ');
                                        for (var i = 0; i < commands.length; i++) {
                                            commands[i] = commands[i].replace(/&quot;/gi, '"');
                                            commands[i] = commands[i].replace(/%UTILS_TESTS_PATH%/gi, UTILS_TESTS_PATH);
                                            commands[i] = commands[i].replace(/\$UTILS_TESTS_PATH/gi, UTILS_TESTS_PATH);
                                            commands[i] = commands[i].replace(/%WORKSPACE%/gi, testSetup.config.WORKSPACE);
                                            commands[i] = commands[i].replace(/\$WORKSPACE/gi, testSetup.config.WORKSPACE);
                                            commands[i] = commands[i].replace(/%SERVER_TESTS_PATH%/gi, SERVER_TESTS_PATH);
                                            commands[i] = commands[i].replace(/\$SERVER_TESTS_PATH/gi, SERVER_TESTS_PATH);
                                            commands[i] = commands[i].replace(/%WAKANDA_SERVER_PATH%/gi, testSetup.config.WAKANDA_SERVER_PATH);
                                            commands[i] = commands[i].replace(/\$WAKANDA_SERVER_PATH/gi, testSetup.config.WAKANDA_SERVER_PATH);
                                            commands[i] = commands[i].replace(/%BUILD_TEST_DIR%/gi, testSetup.config.BUILD_TEST_DIR);
                                            commands[i] = commands[i].replace(/\$BUILD_TEST_DIR/gi, testSetup.config.BUILD_TEST_DIR);
                                        }
                                        try {
                                            shellProcess = spawn(commands[0], commands.slice(1), {
                                                cwd: testSetup.config.WORKSPACE,
                                                env: testSetup.config,
                                                detached: (isWindows() === false)
                                            });
                                        } catch (e) {
                                            shellProcess = null;
                                            consoleLog('[ERROR] cannot launch Shell script (1a)', e);
                                            return serieCallback(e);
                                        }
                                        shellProcess.on('error', function(e) {
                                            shellProcess = null;
                                            consoleLog('[ERROR] cannot launch Shell script (1b)', e);
                                            return serieCallback(e);
                                        });
                                        shellProcess.stdout.on('data', function(data) {
                                            if (globalStdout === null) globalStdout = '';
                                            globalStdout += data.toString();
                                            consoleLog('[STDOUT] ' + data.toString());
                                            timeoutShell(testSetup.testName);
                                        });
                                        shellProcess.stderr.on('data', function(data) {
                                            if (globalSdterr === null) globalSdterr = '';
                                            globalSdterr += data.toString();
                                            consoleLog('[STDERR] ' + data.toString());
                                            timeoutShell(testSetup.testName);
                                        });
                                        shellProcess.on('close', function(code) {
                                            shellProcess = null;
                                            if (testHasTimeouted === true) {
                                                testHasTimeouted = false;
                                                consoleLog('[ERROR] Shell killed after TIMEOUT');
                                                callbackParams.err = 'Shell killed after TIMEOUT';
                                            }
                                            return serieCallback(null);
                                        });
                                        timeoutShell(testSetup.testName);
                                    },
                                    function(err) {
                                        wrapShellTest(globalStdout, globalSdterr, err, testSetup, callbackParams, callback);
                                    }
                                );
                            } else {
                                consoleLog('[ERROR] no shell command specified in POM file for this test');
                                callbackParams.error = 'no shell command specified in POM file for this test';
                                wrapShellTest('', '', null, testSetup, callbackParams, callback);
                            }
                            break;
                        default:
                            consoleLog('[ERROR] unknown kind of test: ' + pom.kind);
                            callbackParams.error = 'Unknown kind of test: ' + pom.kind;
                            if (calledThatDamnCallbackAlready === false) {
                                calledThatDamnCallbackAlready = true;
                                mainSerieCallback(null);
                            }
                            return wrapVoidTest(callbackParams, callback, testSetup);
                            break;
                    }
                });
                if (calledThatDamnCallbackAlready === false) {
                    calledThatDamnCallbackAlready = true;
                    mainSerieCallback(null);
                }
            }
        ],
        function(err, results) {
            // nop	
        });
}

function wrapVoidTest(callbackParams, callback, testSetup) {
    callbackParams.end = new Date();
    callbackParams.duration = callbackParams.end.getTime() - callbackParams.start.getTime();
    callbackParams.status = null;
    if (typeof testSetup !== 'undefined') {
        callbackParams.result = {
            name: testSetup.testName,
            pom: testSetup.pom,
            path: testSetup.testPath,
            changelist: testSetup.config.CHANGELIST,
            start: callbackParams.start,
            end: callbackParams.end,
            duration: callbackParams.end.getTime() - callbackParams.start.getTime(),
            bench: false,
            abstract: {
                total: 0,
                failures: 0,
                skipped: 0,
                passed: 0,
                success: 0
            },
            passed: [],
            failed: [],
            skipped: [],
            status: null
        };
        try {
            fs.writeFileSync(path.join(testSetup.destFullPath, 'report.json'), JSON.stringify(callbackParams.result));
        } catch (e) {
            consoleLog('[ERROR] cannot write JSON report (empty)', e);
        }
    }
    clearCache(true);
    return callback(callbackParams);
}

function wrapShellTest(globalStdout, globalSdterr, err, testSetup, callbackParams, callback) {
    clearTimeout(shellProcessKill);
    callbackParams.end = new Date();
    callbackParams.duration = callbackParams.end.getTime() - callbackParams.start.getTime();
    callbackParams.result = {
        name: testSetup.testName,
        pom: testSetup.pom,
        path: testSetup.testPath,
        changelist: testSetup.config.CHANGELIST,
        start: callbackParams.start,
        end: callbackParams.end,
        duration: callbackParams.end.getTime() - callbackParams.start.getTime(),
        bench: false,
        abstract: {
            total: 0,
            failures: 0,
            skipped: 0,
            passed: 0,
            success: 0
        },
        passed: [],
        failed: [],
        skipped: [],
        status: null
    };
    try {
        fs.writeFileSync(path.join(testSetup.destFullPath, 'report.json'), JSON.stringify(callbackParams.result));
    } catch (e) {
        consoleLog('[ERROR] cannot write JSON report (empty)', e);
    }
    if (globalStdout) {
        try {
            fs.writeFileSync(path.join(testSetup.destFullPath, 'stdout.txt'), globalStdout.toString());
        } catch (e) {
            consoleLog('[ERROR] cannot write stdout (4)', e);
        }
    }
    if (globalSdterr) {
        try {
            fs.writeFileSync(path.join(testSetup.destFullPath, 'stderr.txt'), globalSdterr.toString());
        } catch (e) {
            consoleLog('[ERROR] cannot write stderr (4)', e);
        }
    }
    if (err) {
        consoleLog('[ERROR] Shell command failed:', err);
        callbackParams.status = null;
        if (!callbackParams.error) callbackParams.error = 'Shell command failed: ' + err;
        clearCache(true);
        return callback(callbackParams);
    } else {
        var file = findFiles(testSetup.config.WORKSPACE, /\.xml$/i);
        try {
            var stat = fs.statSync(file[0]);
        } catch (e) {
            var stat = false;
        }
        if (stat && stat.isFile()) {
            var resultString = fs.readFileSync(file[0]).toString();
            try {
                fs.writeFileSync(path.join(testSetup.destFullPath, 'report.xml'), resultString);
            } catch (e) {
                consoleLog('[ERROR] cannot write XML report (4)', e);
                if (!callbackParams.error) callbackParams.error = e;
            }
            try {
                parseString(resultString, function(err, rawresult) {
                    if (err) {
                        consoleLog('[ERROR] cannot parse XML report (4)', err);
                        callbackParams.status = null;
                        if (!callbackParams.error) callbackParams.error = err;
                        clearCache(true);
                        return callback(callbackParams);
                    }
                    if (typeof rawresult.testsuite !== 'undefined' && typeof rawresult.testsuite.$ !== 'undefined' && typeof rawresult.testsuite.$.tests !== 'undefined' && typeof rawresult.testsuite.$.errors !== 'undefined' && typeof rawresult.testsuite.$.failures !== 'undefined') {
                        var result = {
                            name: testSetup.testName,
                            pom: testSetup.pom,
                            path: testSetup.testPath,
                            changelist: testSetup.config.CHANGELIST,
                            start: callbackParams.start,
                            end: callbackParams.end,
                            duration: callbackParams.end.getTime() - callbackParams.start.getTime(),
                            bench: false,
                            abstract: {
                                passed: 0,
                                total: 0,
                                failures: 0,
                                skipped: 0
                            },
                            passed: [],
                            failed: [],
                            skipped: []
                        };
                        rawresult.testsuite.testcase.forEach(function(testcase) {
                            if (typeof testcase.failure !== 'undefined') {
                                result.failed.push({
                                    name: testcase.$.name,
                                    failure: testcase.failure[0].$.message,
                                    time: -1
                                });
                            } else if (typeof testcase.error !== 'undefined') {
                                result.failed.push({
                                    name: testcase.$.name,
                                    failure: testcase.error[0].$.message,
                                    time: -1
                                });
                            } else if (typeof testcase.skipped !== 'undefined') {
                                result.skipped.push({
                                    name: testcase.$.name
                                });
                            } else {
                                result.passed.push({
                                    name: testcase.$.name,
                                    time: -1
                                });
                            }
                        });
                        result.abstract.passed = result.passed.length;
                        result.abstract.failures = result.failed.length;
                        result.abstract.skipped = result.skipped.length;
                        result.abstract.total = result.abstract.passed + result.abstract.failures + result.abstract.skipped;
                        result.abstract.success = (result.abstract.passed / result.abstract.total) * 100;
                        if (result.abstract.total === 0 || result.abstract.total === result.abstract.failures || result.abstract.failures > 0 || result.abstract.total === result.abstract.errors || result.abstract.errors > 0) {
                            result.status = false;
                        } else {
                            result.status = true;
                        }
                        callbackParams.result = result;
                        callbackParams.status = result.status;
                        callbackParams.error = null;
                        try {
                            fs.writeFileSync(path.join(testSetup.destFullPath, 'report.json'), JSON.stringify(result));
                        } catch (e) {
                            consoleLog('[ERROR] cannot write JSON report (4)', e);
                            callbackParams.status = null;
                            if (!callbackParams.error) callbackParams.error = e;
                        }
                        clearCache(true);
                        return callback(callbackParams);
                    } else {
                        consoleLog('[ERROR] XML report incomplete or malformed (4)');
                        callbackParams.status = null;
                        if (!callbackParams.error) callbackParams.error = 'XML report incomplete or malformed';
                        clearCache(true);
                        return callback(callbackParams);
                    }
                });
            } catch (e) {
                consoleLog('[ERROR] cannot parse XML report (4b)', e);
                callbackParams.status = null;
                if (!callbackParams.error) callbackParams.error = e;
                clearCache(true);
                return callback(callbackParams);
            }
        } else {
            consoleLog('[ERROR] XML report not found (4)');
            callbackParams.status = null;
            if (!callbackParams.error) callbackParams.err = 'XML report not found';
            clearCache(true);
            return callback(callbackParams);
        }
    }
}

function timeoutShell(testName, now) {
    if (typeof now === 'undefined') {
        now = false;
    }
    clearTimeout(shellProcessKill);
    testHasTimeouted = false;
    if (shellProcess !== null && shellProcess.pid > 0 && shellProcess.pid != process.pid) {
        if (now === false) {
            shellProcessKill = setTimeout(function() {
                if (shellProcess !== null && shellProcess.pid > 0 && shellProcess.pid != process.pid) {
                    shellProcessKilled = true;
                    testHasTimeouted = true;
                    consoleLog('[ERROR] TIMEOUT - SIGKILL (Shell) from ' + testName);
                    if (isWindows()) {
                        exec('taskkill /pid ' + shellProcess.pid + ' /T /F');
                    } else {
                        spawn('kill', ['-9', -shellProcess.pid]);
                        spawn('kill', ['-9', shellProcess.pid]);
                    }
                }
            }, dynamicTimeout * 2);
        } else {
            shellProcessKilled = true;
            testHasTimeouted = false;
            consoleLog('[INFO] SIGKILL (Shell) from ' + testName);
            if (isWindows()) {
                exec('taskkill /pid ' + shellProcess.pid + ' /T /F');
            } else {
                spawn('kill', ['-9', -shellProcess.pid]);
                spawn('kill', ['-9', shellProcess.pid]);
            }
        }
    }
}

// Run CLI test
function runCLITest(opt, callback) {
    clearTimeout(softCLIKillTimeout);
    clearTimeout(hardCLIKillTimeout);
    softKilled = false;
    hardKilled = false;
    testHasTimeouted = false;
    opt.config.CLIWORKSPACE = opt.config.WORKSPACE;
    try {
        if (/_cli_/i.test(opt.testName) === false) {
            if (isInDebugMode() === false) {
                CLIProcess = spawn(opt.config.CLI_PATH, ['--debug-off', opt.testPath], {
                    cwd: opt.config.WORKSPACE,
                    env: opt.config
                });
            } else {
                CLIProcess = spawn(opt.config.CLI_PATH, [opt.testPath], {
                    cwd: opt.config.WORKSPACE,
                    env: opt.config
                });
            }
        } else {
            if (isInDebugMode() === false) {
                CLIProcess = spawn(opt.config.WAKANDA_SERVER_PATH, ['--debug-off', opt.testPath], {
                    cwd: opt.config.WORKSPACE,
                    env: opt.config
                });
            } else {
                CLIProcess = spawn(opt.config.WAKANDA_SERVER_PATH, [opt.testPath], {
                    cwd: opt.config.WORKSPACE,
                    env: opt.config
                });
            }
        }
    } catch (e) {
        consoleLog('[ERROR] cannot launch Server (2a)', e);
        opt.callbackParams.error = e;
        return wrapCLITest(opt, callback);
    }
    CLIProcess.on('error', function(e) {
        CLIProcess = null;
        consoleLog('[ERROR] cannot launch Server (2b)', e);
        opt.callbackParams.error = e;
        wrapCLITest(opt, callback);
    });
    CLIProcess.stdout.on('data', function(data) {
        if (opt.callbackParams.stdout === null) opt.callbackParams.stdout = '';
        opt.callbackParams.stdout += data.toString();
        consoleLog('[STDOUT] ' + data.toString());
        if (isInDebugMode() === false) timeoutCLIServer(opt.testName, false, ((typeof opt.pom.bench !== 'undefined' && opt.pom.bench === true) ? 10 : 2));
    });
    CLIProcess.stderr.on('data', function(data) {
        if (opt.callbackParams.stderr === null) opt.callbackParams.stderr = '';
        opt.callbackParams.stderr += data.toString();
        consoleLog('[STDERR] ' + data.toString());
        if (isInDebugMode() === false) timeoutCLIServer(opt.testName, false, ((typeof opt.pom.bench !== 'undefined' && opt.pom.bench === true) ? 10 : 2));
    });
    CLIProcess.on('close', function(code) {
        CLIProcess = null;
        if (testHasTimeouted === true) {
            testHasTimeouted = false;
            consoleLog('[WARN] CLI killed after TIMEOUT');
        }
        consoleLog('[INFO] Wakanda Server exited with code ' + code);
        opt.callbackParams.exitCode = code;
        wrapCLITest(opt, callback);
    });
    if (isInDebugMode() === false) timeoutCLIServer(opt.testName, false, ((typeof opt.pom.bench !== 'undefined' && opt.pom.bench === true) ? 10 : 2));
}

function wrapCLITest(opt, callback) {
    opt.callbackParams.end = new Date();
    opt.callbackParams.duration = opt.callbackParams.end.getTime() - opt.callbackParams.start.getTime();
    emptyReport(opt);
    if (opt.callbackParams.error) {
        consoleLog('[ERROR] cannot complete CLI test', opt.callbackParams.error);
        opt.callbackParams.status = null;
        if (opt.callbackParams.stderr) {
            opt.callbackParams.stderr = opt.callbackParams.stderr.toString() + '\n' + opt.callbackParams.error.toString();
        } else {
            opt.callbackParams.stderr = opt.callbackParams.error.toString();
        }
    }
    if (opt.callbackParams.stdout) {
        try {
            fs.writeFileSync(path.join(opt.destFullPath, 'stdout.txt'), opt.callbackParams.stdout.toString());
        } catch (e) {
            consoleLog('[WARN] cannot write stdout (1)', e);
            if (!opt.callbackParams.error) opt.callbackParams.error = e;
        }
    }
    if (opt.callbackParams.stderr) {
        try {
            fs.writeFileSync(path.join(opt.destFullPath, 'stderr.txt'), opt.callbackParams.stderr.toString());
        } catch (e) {
            consoleLog('[WARN] cannot write stderr (1)', e);
            if (!opt.callbackParams.error) opt.callbackParams.error = e;
        }
    }
    var file = path.join(opt.config.WORKSPACE, 'report.xml');
    try {
        var stat = fs.statSync(file);
    } catch (e) {
        var stat = false;
    }
    if (stat && stat.isFile()) {
        var resultString = fs.readFileSync(file).toString();
        try {
            fs.writeFileSync(path.join(opt.destFullPath, 'report.xml'), resultString);
        } catch (e) {
            consoleLog('[ERROR] cannot write XML report (1)', e);
            opt.callbackParams.status = null;
            if (!opt.callbackParams.error) opt.callbackParams.error = e;
            clearCache(true);
            return callback(opt.callbackParams);
        }
        try {
            parseString(resultString, function(err, rawresult) {
                if (err) {
                    consoleLog('[ERROR] cannot parse XML report (1)', err);
                    opt.callbackParams.status = null;
                    if (!opt.callbackParams.error) opt.callbackParams.error = err;
                    clearCache(true);
                    return callback(opt.callbackParams);
                }
                if (typeof rawresult.testsuites !== 'undefined' && typeof rawresult.testsuites.$ !== 'undefined' && typeof rawresult.testsuites.$.tests !== 'undefined' && typeof rawresult.testsuites.$.passed !== 'undefined' && typeof rawresult.testsuites.$.failures !== 'undefined') {
                    var result = {
                        name: opt.testName,
                        pom: opt.pom,
                        path: opt.testPath,
                        changelist: opt.config.CHANGELIST,
                        start: opt.callbackParams.start,
                        end: opt.callbackParams.end,
                        duration: opt.callbackParams.end.getTime() - opt.callbackParams.start.getTime(),
                        bench: false,
                        abstract: {
                            total: parseInt(rawresult.testsuites.$.tests),
                            failures: parseInt(rawresult.testsuites.$.failures),
                            skipped: parseInt(rawresult.testsuites.$.skipped),
                            passed: parseInt(rawresult.testsuites.$.passed)
                        },
                        passed: [],
                        failed: [],
                        skipped: []
                    };
                    result.abstract.success = (result.abstract.passed / result.abstract.total) * 100;
                    if (result.abstract.total === 0 || result.abstract.total === result.abstract.failures || result.abstract.failures > 0 || result.abstract.total === result.abstract.errors || result.abstract.errors > 0) {
                        result.status = false;
                    } else {
                        result.status = true;
                    }
                    rawresult.testsuites.testsuite[0].testcase.forEach(function(testcase) {
                        if (typeof testcase.failure !== 'undefined') {
                            result.failed.push({
                                name: testcase.$.name,
                                failure: testcase.failure[0].$.message,
                                time: parseInt(testcase.$.time)
                            });
                        } else if (typeof testcase.error !== 'undefined') {
                            result.failed.push({
                                name: testcase.$.name,
                                failure: testcase.error[0].$.message,
                                time: parseInt(testcase.$.time)
                            });
                        } else if (typeof testcase.skipped !== 'undefined') {
                            result.skipped.push({
                                name: testcase.$.name
                            });
                        } else {
                            result.passed.push({
                                name: testcase.$.name,
                                time: parseInt(testcase.$.time)
                            });
                        }
                    });
                    opt.callbackParams.result = result;
                    opt.callbackParams.status = result.status;
                    if (!opt.callbackParams.error) opt.callbackParams.error = null;
                    try {
                        fs.writeFileSync(path.join(opt.destFullPath, 'report.json'), JSON.stringify(result));
                    } catch (e) {
                        consoleLog('[ERROR] cannot write JSON report (1)', e);
                        opt.callbackParams.status = null;
                        if (!opt.callbackParams.error) opt.callbackParams.error = e;
                    }
                    clearCache(true);
                    return callback(opt.callbackParams);
                } else {
                    consoleLog('[ERROR] XML report incomplete or malformed (1)');
                    opt.callbackParams.status = null;
                    if (!opt.callbackParams.error) opt.callbackParams.error = 'XML report incomplete or malformed';
                    clearCache(true);
                    return callback(opt.callbackParams);
                }
            });
        } catch (e) {
            consoleLog('[ERROR] cannot parse XML report (1b)', e);
            opt.callbackParams.status = null;
            if (!opt.callbackParams.error) opt.callbackParams.error = e;
            clearCache(true);
            return callback(opt.callbackParams);
        }
    } else if (typeof opt.pom.bench !== 'undefined' && opt.pom.bench === true) {
        opt.callbackParams.result.bench = true;
        var file = path.join(opt.config.WORKSPACE, 'result.csv');
        try {
            var stat = fs.statSync(file);
        } catch (e) {
            var stat = false;
        }
        if (stat && stat.isFile()) {
            var dest = path.join(opt.destFullPath, 'result.csv');
            try {
                copyFileSync(file, dest);
            } catch (e) {
                consoleLog('[WARN] cannot copy artifact', e);
            }
            var result = {
                name: opt.testName,
                bench: true,
                pom: opt.pom,
                path: opt.testPath,
                changelist: opt.config.CHANGELIST,
                start: opt.callbackParams.start,
                end: opt.callbackParams.end,
                duration: opt.callbackParams.end.getTime() - opt.callbackParams.start.getTime(),
                abstract: {
                    total: 1,
                    failures: 0,
                    skipped: 0,
                    passed: 1
                },
                passed: [{
                    name: opt.testName + ' (bench)',
                    time: opt.callbackParams.end.getTime() - opt.callbackParams.start.getTime()
                }],
                failed: [],
                skipped: [],
                status: true
            };
            opt.callbackParams.result = result;
            opt.callbackParams.status = true;
            opt.callbackParams.error = null;
            try {
                fs.writeFileSync(path.join(opt.destFullPath, 'report.json'), JSON.stringify(result));
            } catch (e) {
                consoleLog('[ERROR] cannot write JSON report for bench (1)', e);
                opt.callbackParams.status = null;
                if (!opt.callbackParams.error) opt.callbackParams.error = e;
            }
            clearCache(true);
            return callback(opt.callbackParams);
        } else {
            consoleLog('[ERROR] CSV result not found for bench (1)');
            opt.callbackParams.status = null;
            if (!opt.callbackParams.error) opt.callbackParams.error = 'CSV result not found for bench';
            clearCache(true);
            return callback(opt.callbackParams);
        }
    } else {
        consoleLog('[ERROR] XML report not found (1)');
        opt.callbackParams.status = null;
        if (!opt.callbackParams.error) opt.callbackParams.error = 'XML report not found';
        clearCache(true);
        return callback(opt.callbackParams);
    }
}

function timeoutCLIServer(testName, now, factor) {
    if (typeof now === 'undefined') {
        now = false;
    }
    if (typeof factor === 'undefined') {
        factor = 1;
    }
    clearTimeout(softCLIKillTimeout);
    clearTimeout(hardCLIKillTimeout);
    softCLIKillTimeoutTestname = testName;
    hardCLIKillTimeoutTestname = testName;
    testHasTimeouted = false;
    if (CLIProcess !== null && CLIProcess.pid > 0 && CLIProcess.pid != process.pid) {
        if (now === false) {
            softCLIKillTimeout = setTimeout(function() {
                if (CLIProcess !== null && CLIProcess.pid > 0 && CLIProcess.pid != process.pid) {
                    if (softCLIKillTimeoutTestname === testName) {
                        softKilled = true;
                        testHasTimeouted = true;
                        consoleLog('[ERROR] TIMEOUT - SIGTERM (CLI) from ' + testName);
                        CLIProcess.kill('SIGTERM');
                    } else {
                        consoleLog('[INFO] TIMEOUT - SIGTERM (CLI) skipped in ' + testName + ' from ' + softCLIKillTimeoutTestname);
                    }
                }
            }, dynamicTimeout * factor);
            hardCLIKillTimeout = setTimeout(function() {
                softKilled = false;
                if (CLIProcess !== null && CLIProcess.pid > 0 && CLIProcess.pid != process.pid) {
                    if (hardCLIKillTimeoutTestname === testName) {
                        hardKilled = true;
                        testHasTimeouted = true;
                        consoleLog('[ERROR] TIMEOUT - SIGKILL (CLI - SIGTERM failed) from ' + testName);
                        CLIProcess.kill('SIGKILL');
                    } else {
                        consoleLog('[INFO] TIMEOUT - SIGKILL (CLI) skipped in ' + testName + ' from ' + hardCLIKillTimeoutTestname);
                    }
                }
            }, (dynamicTimeout * factor) + (10 * 1000));
        } else {
            hardCLIKillTimeout = setTimeout(function() {
                softKilled = false;
                if (CLIProcess !== null && CLIProcess.pid > 0 && CLIProcess.pid != process.pid) {
                    if (hardCLIKillTimeoutTestname === testName) {
                        hardKilled = true;
                        testHasTimeouted = false;
                        consoleLog('[WARN] SIGKILL (CLI - SIGTERM failed) from ' + testName);
                        CLIProcess.kill('SIGKILL');
                    } else {
                        consoleLog('[INFO] SIGKILL (CLI) skipped in ' + testName + ' from ' + hardCLIKillTimeoutTestname);
                    }
                }
            }, 10 * 1000);
            if (softCLIKillTimeoutTestname === testName) {
                softKilled = false;
                testHasTimeouted = false;
                consoleLog('[INFO] SIGTERM (CLI) from ' + testName);
                CLIProcess.kill('SIGTERM');
            } else {
                consoleLog('[INFO] SIGTERM (CLI) skipped in ' + testName + ' from ' + softCLIKillTimeoutTestname);
            }
        }
    }
}

// Run JS test (SSJS or CSJS)
// TODO: clean solution (.waData, etc.) unless some stuff are required
function runJSTest(opt, callback) {
    clearTimeout(softKillTimeout);
    clearTimeout(hardKillTimeout);
    clearTimeout(serverReadyRequestTimeout);
    softKilled = false;
    hardKilled = false;
    testHasTimeouted = false;
    if (/(studio|waf)/i.test(opt.testName) && opt.pom.kind === 'csjs') {
        setUpSeleniumProxy(opt.config.WAKANDA_STUDIO_FOLDER);
    }
    try {
        findFiles(opt.config.TESTBASEPATH, /_log_.*\.txt$/i).forEach(function(logFile) {
            fs.unlinkSync(logFile);
        });
    } catch (e) {
        // Doesn't matter
    }
    try {
        findFiles(opt.config.TESTBASEPATH, /\.walog$/i).forEach(function(logFile) {
            fs.unlinkSync(logFile);
        });
    } catch (e) {
        // Doesn't matter
    }
    try {
        if (isInDebugMode() === false) {
            serverProcess = spawn(opt.config.WAKANDA_SERVER_PATH, ['--debug-off', opt.testSolutionPath], {
                cwd: opt.config.WORKSPACE,
                env: opt.config
            });
        } else {
            serverProcess = spawn(opt.config.WAKANDA_SERVER_PATH, [opt.testSolutionPath], {
                cwd: opt.config.WORKSPACE,
                env: opt.config
            });
        }
    } catch (e) {
        serverProcess = null;
        clearTimeout(serverReadyRequestTimeout);
        consoleLog('[ERROR] cannot launch Server (1a)', e);
        if (!opt.callbackParams.error) opt.callbackParams.error = e;
        return wrapJSTest(opt, callback);
    }
    serverProcess.on('error', function(e) {
        serverProcess = null;
        clearTimeout(serverReadyRequestTimeout);
        consoleLog('[ERROR] cannot launch Server (1b)', e);
        if (!opt.callbackParams.error) opt.callbackParams.error = e;
        wrapJSTest(opt, callback);
    });
    serverProcess.stdout.on('data', function(data) {
        if (opt.callbackParams.stdout === null) opt.callbackParams.stdout = '';
        opt.callbackParams.stdout += data.toString();
        consoleLog('[STDOUT] ' + data.toString());
        if (isInDebugMode() === false) timeoutServer(opt.testName, false, false, ((typeof opt.pom.bench !== 'undefined' && opt.pom.bench === true) ? 10 : 1));
    });
    serverProcess.stderr.on('data', function(data) {
        if (opt.callbackParams.stderr === null) opt.callbackParams.stderr = '';
        opt.callbackParams.stderr += data.toString();
        consoleLog('[STDERR] ' + data.toString());
        if (isInDebugMode() === false) timeoutServer(opt.testName, false, false, ((typeof opt.pom.bench !== 'undefined' && opt.pom.bench === true) ? 10 : 1));
    });
    serverProcess.on('exit', function(code) {
        serverProcess = null;
        clearTimeout(serverReadyRequestTimeout);
        if (testHasTimeouted === true) {
            testHasTimeouted = false;
            consoleLog('[WARN] Server killed after TIMEOUT');
        }
        consoleLog('[INFO] Wakanda Server exited with code ' + code);
        opt.callbackParams.exitCode = code;
        wrapJSTest(opt, callback);
    });
    serverReadyRequestTimeout = setTimeout(function() {
        bag.request('get', 'http://' + opt.config.WAKANDA_URL + '/unitTest.js', {
                retry: {
                    errorCodes: true,
                    statusCodes: [404, 500, 503],
                    scale: 0.5,
                    delay: 1000,
                    maxRetries: 2
                },
                timeout: 1000,
                // TODO: 404 --> mail to the tester - SOLUTION BADLY CONFIGURED
                handlers: {
                    '2xx': function(result) {
                        if (state.done.indexOf(opt.testName) === -1) {
                            if (opt.pom.kind === 'csjs-headless') { // NEW ARCHI
                                var runUrl = opt.testURL + '&waktest-format=' + opt.pom.reporter + '&rnd=' + opt.callbackParams.start.getTime();
                                if (typeof opt.config.debugWAF !== 'undefined' && (opt.config.debugWAF === true || opt.config.debugWAF === 'true')) {
                                    runUrl += '&debug=1';
                                }
                                var phantomCmd = [opt.config.CSJS_HEADLESS_BIN, opt.config.CSJS_HEADLESS_SCRIPT, runUrl, opt.config.WORKSPACE.replace(/\\/ig, '/') + '/'];
                                if (isLinux()) {
                                    opt.config.DISPLAY = ':0';
                                }
                                try {
                                    phantomProcess = spawn(phantomCmd[0], phantomCmd.slice(1), {
                                        cwd: opt.config.WORKSPACE,
                                        env: opt.config
                                    });
                                } catch (e) {
                                    consoleLog('[ERROR] cannot launch PhantomJS (1n)', e);
                                    phantomProcess = null;
                                    if (!opt.callbackParams.error) opt.callbackParams.error = e;
                                    if (isInDebugMode() === false) timeoutServer(opt.testName, true, false, ((typeof opt.pom.bench !== 'undefined' && opt.pom.bench === true) ? 10 : 1));
                                }
                                phantomProcess.on('error', function(e) {
                                    consoleLog('[ERROR] cannot launch PhantomJS (2n)', e);
                                    phantomProcess = null;
                                    if (!opt.callbackParams.error) opt.callbackParams.error = e;
                                    if (isInDebugMode() === false) timeoutServer(opt.testName, true, false, ((typeof opt.pom.bench !== 'undefined' && opt.pom.bench === true) ? 10 : 1));
                                });
                                phantomProcess.stdout.on('data', function(data) {
                                    if (opt.callbackParams.stdout === null) opt.callbackParams.stdout = '';
                                    opt.callbackParams.stdout += data.toString();
                                    consoleLog('[STDOUT] ' + data.toString());
                                    if (isInDebugMode() === false) timeoutServer(opt.testName, false, true, ((typeof opt.pom.bench !== 'undefined' && opt.pom.bench === true) ? 10 : 1));
                                });
                                phantomProcess.stderr.on('data', function(data) {
                                    if (opt.callbackParams.stderr === null) opt.callbackParams.stderr = '';
                                    opt.callbackParams.stderr += data.toString();
                                    consoleLog('[STDERR] ' + data.toString());
                                    if (isInDebugMode() === false) timeoutServer(opt.testName, false, true, ((typeof opt.pom.bench !== 'undefined' && opt.pom.bench === true) ? 10 : 1));
                                });
                                phantomProcess.on('exit', function(code) {
                                    consoleLog('[PhantomJS] exit with code ' + code);
                                    phantomProcess = null;
                                    opt.callbackParams.result = null;
                                    try {
                                        fs.readdirSync(opt.config.WORKSPACE).forEach(function(fileName) {
                                            var file = path.join(opt.config.WORKSPACE, fileName);
                                            try {
                                                var stat = fs.statSync(file);
                                            } catch (e) {
                                                var stat = false;
                                            }
                                            if (stat && stat.isFile() && /report\.xml$/i.test(fileName)) {
                                                opt.callbackParams.result = fs.readFileSync(file).toString();
                                            } else if (stat && stat.isFile() && /screenshot\.png$/i.test(fileName)) {
                                                var dest = path.join(opt.destFullPath, 'screenshot.png');
                                                try {
                                                    copyFileSync(file, dest);
                                                } catch (e) {
                                                    consoleLog('[WARN] cannot copy artifact (1n)', e);
                                                }
                                            }
                                        });
                                    } catch (e) {
                                        if (!opt.callbackParams.error) opt.callbackParams.error = e;
                                    }
                                    if (isInDebugMode() === false) timeoutServer(opt.testName, true, false, ((typeof opt.pom.bench !== 'undefined' && opt.pom.bench === true) ? 10 : 1));
                                });
                                if (isInDebugMode() === false) timeoutServer(opt.testName, false, true, ((typeof opt.pom.bench !== 'undefined' && opt.pom.bench === true) ? 10 : 1));
                            } else if (opt.pom.kind === 'csjs') {
                                var urlPath = opt.config.WORKSPACE.replace(/\\/ig, '/') + '/';
                                if (opt.testURL !== null && /\.wapage/i.test(opt.testURL) === true) {
                                    var runUrl = 'http://' + opt.config.WAKANDA_URL + opt.testURL + '?path=' + opt.testPath + '&jobLocation=' + urlPath + '&jobId=' + opt.testName + '-' + opt.config.CHANGELIST;
                                } else {
                                    var runUrl = 'http://' + opt.config.WAKANDA_URL + '/testClient?path=' + opt.testPath + '&jobLocation=' + urlPath + '&jobId=' + opt.testName + '-' + opt.config.CHANGELIST;
                                    if (opt.testURL !== null) {
                                        runUrl += '&page=' + opt.testURL;
                                    }
                                }
                                runUrl += '&rnd=' + opt.callbackParams.start.getTime();
                                if (typeof opt.config.debugWAF !== 'undefined' && (opt.config.debugWAF === true || opt.config.debugWAF === 'true')) {
                                    runUrl += '&debug=1';
                                }
                                var phantomCmd = [opt.config.PHANTOMJS_PATH, opt.config.PHANTOMJS_SCRIPT, runUrl, opt.config.WORKSPACE + path.sep + 'screenshot-' + opt.testName + '-' + opt.config.CHANGELIST + '.png'];
                                if (isLinux()) {
                                    opt.config.DISPLAY = ':0';
                                }
                                try {
                                    phantomProcess = spawn(phantomCmd[0], phantomCmd.slice(1), {
                                        cwd: opt.config.WORKSPACE,
                                        env: opt.config
                                    });
                                } catch (e) {
                                    consoleLog('[ERROR] cannot launch PhantomJS (1a)', e);
                                    phantomProcess = null;
                                    if (!opt.callbackParams.error) opt.callbackParams.error = e;
                                    if (isInDebugMode() === false) timeoutServer(opt.testName, true, false, ((typeof opt.pom.bench !== 'undefined' && opt.pom.bench === true) ? 10 : 1));
                                }
                                phantomProcess.on('error', function(e) {
                                    consoleLog('[ERROR] cannot launch PhantomJS (1b)', e);
                                    phantomProcess = null;
                                    if (!opt.callbackParams.error) opt.callbackParams.error = e;
                                    if (isInDebugMode() === false) timeoutServer(opt.testName, true, false, ((typeof opt.pom.bench !== 'undefined' && opt.pom.bench === true) ? 10 : 1));
                                });
                                phantomProcess.stdout.on('data', function(data) {
                                    if (opt.callbackParams.stdout === null) opt.callbackParams.stdout = '';
                                    opt.callbackParams.stdout += data.toString();
                                    consoleLog('[STDOUT] ' + data.toString());
                                    if (isInDebugMode() === false) timeoutServer(opt.testName, false, true, ((typeof opt.pom.bench !== 'undefined' && opt.pom.bench === true) ? 10 : 1));
                                });
                                phantomProcess.stderr.on('data', function(data) {
                                    if (opt.callbackParams.stderr === null) opt.callbackParams.stderr = '';
                                    opt.callbackParams.stderr += data.toString();
                                    consoleLog('[STDERR] ' + data.toString());
                                    if (isInDebugMode() === false) timeoutServer(opt.testName, false, true, ((typeof opt.pom.bench !== 'undefined' && opt.pom.bench === true) ? 10 : 1));
                                });
                                phantomProcess.on('exit', function(code) {
                                    phantomProcess = null;
                                    opt.callbackParams.result = null;
                                    try {
                                        fs.readdirSync(opt.config.WORKSPACE).forEach(function(fileName) {
                                            var file = path.join(opt.config.WORKSPACE, fileName);
                                            try {
                                                var stat = fs.statSync(file);
                                            } catch (e) {
                                                var stat = false;
                                            }
                                            if (stat && stat.isFile() && /\.xml$/i.test(fileName)) {
                                                opt.callbackParams.result = fs.readFileSync(file).toString();
                                            } else if (stat && stat.isFile() && /\.png$/i.test(fileName)) {
                                                var dest = path.join(opt.destFullPath, 'screenshot.png');
                                                try {
                                                    copyFileSync(file, dest);
                                                } catch (e) {
                                                    consoleLog('[WARN] cannot copy artifact (1)', e);
                                                }
                                            }
                                        });
                                    } catch (e) {
                                        if (!opt.callbackParams.error) opt.callbackParams.error = e;
                                    }
                                    if (isInDebugMode() === false) timeoutServer(opt.testName, true, false, ((typeof opt.pom.bench !== 'undefined' && opt.pom.bench === true) ? 10 : 1));
                                });
                                if (isInDebugMode() === false) timeoutServer(opt.testName, false, true, ((typeof opt.pom.bench !== 'undefined' && opt.pom.bench === true) ? 10 : 1));
                            } else {
                                if (opt.pom.newArchi === true) {
                                    if (isInDebugMode() === false) timeoutServer(opt.testName, false, false, ((typeof opt.pom.bench !== 'undefined' && opt.pom.bench === true) ? 10 : 1));
                                    request.get(opt.testURL + 'waktest-ssjs?path=' + opt.testFilePath + '&format=' + opt.pom.reporter + '&rnd=' + opt.callbackParams.start.getTime(), function(error, response, body) {
                                        if (/<testsuite/ig.test(body) === false) {
                                            if (!opt.callbackParams.error) opt.callbackParams.error = 'XML report empty, incomplete or malformed';
                                            opt.callbackParams.result = null;
                                        } else {
                                            opt.callbackParams.result = body;
                                        }
                                        if (isInDebugMode() === false) timeoutServer(opt.testName, true, false, ((typeof opt.pom.bench !== 'undefined' && opt.pom.bench === true) ? 10 : 1));
                                    });
                                } else {
                                    if (isInDebugMode() === false) timeoutServer(opt.testName, false, false, ((typeof opt.pom.bench !== 'undefined' && opt.pom.bench === true) ? 10 : 1));
                                    request.get('http://' + opt.config.WAKANDA_URL + '/testServer?path=' + opt.testPath + '&format=xml&rnd=' + opt.callbackParams.start.getTime(), function(error, response, body) {
                                        if (/<testsuite/ig.test(body) === false) {
                                            if (!opt.callbackParams.error) opt.callbackParams.error = 'XML report empty, incomplete or malformed';
                                            opt.callbackParams.result = null;
                                        } else {
                                            var secondaryResult = path.join(opt.config.WORKSPACE, 'secondary-report.xml');
                                            try {
                                                var secondaryResultStat = fs.statSync(secondaryResult);
                                            } catch (e) {
                                                var secondaryResultStat = false;
                                            }
                                            if (secondaryResultStat && secondaryResultStat.isFile()) {
                                                var secondaryResultDest = path.join(opt.config.WORKSPACE, 'report.xml');
                                                try {
                                                    opt.callbackParams.result = fs.readFileSync(secondaryResult).toString();
                                                    copyFileSync(secondaryResult, secondaryResultDest);
                                                } catch (e) {
                                                    consoleLog('[WARN] cannot copy secondary result artifact', e);
                                                }
                                            } else {
                                                opt.callbackParams.result = body;
                                            }
                                        }
                                        if (isInDebugMode() === false) timeoutServer(opt.testName, true, false, ((typeof opt.pom.bench !== 'undefined' && opt.pom.bench === true) ? 10 : 1));
                                    });
                                }
                            }
                        }
                    }
                }
            },
            function(err, result) {
                consoleLog('[ERROR] request error for test ' + opt.testName, err);
                opt.callbackParams.error = err + '\n' + result;
                if (isInDebugMode() === false) timeoutServer(opt.testName, true, false, ((typeof opt.pom.bench !== 'undefined' && opt.pom.bench === true) ? 10 : 1));
            }
        );
        if (isInDebugMode() === false) timeoutServer(opt.testName, false, true, ((typeof opt.pom.bench !== 'undefined' && opt.pom.bench === true) ? 10 : 2));
    }, (isInDebugMode() ? 60 * 1000 : 10 * 1000)); // 10s
}

function wrapJSTest(opt, callback) {
    opt.callbackParams.end = new Date();
    opt.callbackParams.duration = opt.callbackParams.end.getTime() - opt.callbackParams.start.getTime();
    try {
        var resultString = opt.callbackParams.result.toString();
    } catch (e) {
        var resultString = null;
    }
    emptyReport(opt);
    var artifacts = [];
    try {
        findFiles(opt.config.TESTBASEPATH, /_log_.*\.txt$/i).forEach(function(logFile) {
            artifacts.push(logFile);
        });
    } catch (e) {
        // Doesn't matter
    }
    try {
        findFiles(opt.config.TESTBASEPATH, /\.walog$/i).forEach(function(logFile) {
            artifacts.push(logFile);
        });
    } catch (e) {
        // Doesn't matter
    }
    artifacts.forEach(function(artifact) {
        if (/\.walog$/i.test(path.basename(artifact))) {
            var baseName = 'http.txt';
        } else {
            var baseName = 'application.txt';
        }
        var dest = path.join(opt.destFullPath, baseName);
        try {
            copyFileSync(artifact, dest);
        } catch (e) {
            consoleLog('[WARN] cannot copy artifact', e);
        }
    });
    var isBench = false;
    var CSVfile = path.join(opt.config.WORKSPACE, 'result.csv');
    try {
        var CSVstat = fs.statSync(CSVfile);
    } catch (e) {
        var CSVstat = false;
    }
    if (CSVstat && CSVstat.isFile()) {
        isBench = true;
        var CSVdest = path.join(opt.destFullPath, 'result.csv');
        try {
            copyFileSync(CSVfile, CSVdest);
        } catch (e) {
            consoleLog('[WARN] cannot copy CSV artifact', e);
        }
    }
    if (opt.callbackParams.error) {
        consoleLog('[ERROR] cannot complete JS test', opt.callbackParams.error);
        opt.callbackParams.status = null;
        if (opt.callbackParams.stderr) {
            opt.callbackParams.stderr = opt.callbackParams.stderr.toString() + '\n' + opt.callbackParams.error.toString();
        } else {
            opt.callbackParams.stderr = opt.callbackParams.error.toString();
        }
    }
    if (opt.callbackParams.stdout) {
        try {
            fs.writeFileSync(path.join(opt.destFullPath, 'stdout.txt'), opt.callbackParams.stdout.toString());
        } catch (e) {
            consoleLog('[WARN] cannot write stdout (2)', e);
        }
    }
    if (opt.callbackParams.stderr) {
        try {
            fs.writeFileSync(path.join(opt.destFullPath, 'stderr.txt'), opt.callbackParams.stderr.toString());
        } catch (e) {
            consoleLog('[ERROR] cannot write stderr (2)', e);
        }
    }
    if (resultString !== null && resultString) {
        try {
            fs.writeFileSync(path.join(opt.destFullPath, 'report.xml'), resultString);
        } catch (e) {
            consoleLog('[ERROR] cannot write XML report (2)', e);
        }
        try {
            parseString(resultString, function(err, rawresult) {
                if (err) {
                    consoleLog('[ERROR] cannot parse XML report (2)', err);
                    opt.callbackParams.status = null;
                    if (!opt.callbackParams.error) opt.callbackParams.error = err;
                    clearCache(true);
                    return callback(opt.callbackParams);
                }
                if (typeof rawresult.testsuites !== 'undefined' && typeof rawresult.testsuites.$ !== 'undefined' && typeof rawresult.testsuites.$.tests !== 'undefined' && typeof rawresult.testsuites.$.passed !== 'undefined' && typeof rawresult.testsuites.$.failures !== 'undefined') {
                    var result = {
                        name: opt.testName,
                        pom: opt.pom,
                        path: opt.testPath,
                        changelist: opt.config.CHANGELIST,
                        start: opt.callbackParams.start,
                        end: opt.callbackParams.end,
                        duration: opt.callbackParams.end.getTime() - opt.callbackParams.start.getTime(),
                        bench: isBench,
                        abstract: {
                            total: parseInt(rawresult.testsuites.$.tests),
                            failures: parseInt(rawresult.testsuites.$.failures),
                            skipped: parseInt(rawresult.testsuites.$.skipped),
                            passed: parseInt(rawresult.testsuites.$.passed)
                        },
                        passed: [],
                        failed: [],
                        skipped: []
                    };
                    result.abstract.success = (result.abstract.passed / result.abstract.total) * 100;
                    if (result.abstract.total === 0 || result.abstract.total === result.abstract.failures || result.abstract.failures > 0 || result.abstract.total === result.abstract.errors || result.abstract.errors > 0) {
                        result.status = false;
                    } else {
                        result.status = true;
                    }
                    rawresult.testsuites.testsuite[0].testcase.forEach(function(testcase) {
                        if (typeof testcase.failure !== 'undefined') {
                            result.failed.push({
                                name: testcase.$.name,
                                failure: testcase.failure[0].$.message,
                                time: parseInt(testcase.$.time)
                            });
                        } else if (typeof testcase.error !== 'undefined') {
                            result.failed.push({
                                name: testcase.$.name,
                                failure: testcase.error[0].$.message,
                                time: parseInt(testcase.$.time)
                            });
                        } else if (typeof testcase.skipped !== 'undefined') {
                            result.skipped.push({
                                name: testcase.$.name
                            });
                        } else {
                            result.passed.push({
                                name: testcase.$.name,
                                time: parseInt(testcase.$.time)
                            });
                        }
                    });
                    opt.callbackParams.result = result;
                    opt.callbackParams.status = result.status;
                    if (!opt.callbackParams.error) opt.callbackParams.error = null;
                    try {
                        fs.writeFileSync(path.join(opt.destFullPath, 'report.json'), JSON.stringify(result));
                    } catch (e) {
                        consoleLog('[ERROR] cannot write JSON report (2)', err);
                        opt.callbackParams.status = null;
                        if (!opt.callbackParams.error) opt.callbackParams.error = e;
                    }
                    clearCache(true);
                    return callback(opt.callbackParams);
                } else {
                    consoleLog('[ERROR] XML report incomplete or malformed (2)');
                    opt.callbackParams.status = null;
                    if (!opt.callbackParams.error) opt.callbackParams.error = 'XML report incomplete or malformed';
                    clearCache(true);
                    return callback(opt.callbackParams);
                }
            });
        } catch (e) {
            consoleLog('[ERROR] cannot parse XML report (2)', e);
            opt.callbackParams.status = null;
            if (!opt.callbackParams.error) opt.callbackParams.error = e;
            clearCache(true);
            return callback(opt.callbackParams);
        }
    } else {
        consoleLog('[ERROR] XML report not found (2)', resultString);
        opt.callbackParams.status = null;
        if (!opt.callbackParams.error) opt.callbackParams.error = 'XML report not found';
        clearCache(true);
        return callback(opt.callbackParams);
    }
}

function timeoutServer(testName, now, killPhantom, factor) {
    if (typeof now === 'undefined') {
        now = false;
    }
    if (typeof killPhantom === 'undefined') {
        killPhantom = false;
    }
    if (typeof factor === 'undefined') {
        factor = 1;
    }
    clearTimeout(softKillTimeout);
    clearTimeout(hardKillTimeout);
    softKillTimeoutTestname = testName;
    hardKillTimeoutTestname = testName;
    testHasTimeouted = false;
    if (serverProcess !== null && serverProcess.pid > 0 && serverProcess.pid != process.pid) {
        if (now === false) {
            softKillTimeout = setTimeout(function() {
                if (serverProcess !== null && serverProcess.pid > 0 && serverProcess.pid != process.pid) {
                    if (softKillTimeoutTestname === testName) {
                        softKilled = true;
                        testHasTimeouted = true;
                        consoleLog('[ERROR] TIMEOUT - SIGTERM (Server) from ' + testName);
                        serverProcess.kill('SIGTERM');
                        if (killPhantom && phantomProcess !== null && phantomProcess.pid > 0 && phantomProcess.pid != process.pid) {
                            consoleLog('[INFO] SIGKILL (PhantomJS) from ' + testName);
                            phantomProcess.kill('SIGKILL');
                        }
                    } else {
                        consoleLog('[INFO] TIMEOUT - SIGTERM (Server) skipped in ' + testName + ' from ' + hardKillTimeoutTestname);
                    }
                }
            }, dynamicTimeout * factor);
            hardKillTimeout = setTimeout(function() {
                softKilled = false;
                if (serverProcess !== null && serverProcess.pid > 0 && serverProcess.pid != process.pid) {
                    if (hardKillTimeoutTestname === testName) {
                        hardKilled = true;
                        testHasTimeouted = true;
                        consoleLog('[ERROR] TIMEOUT - SIGKILL (Server - SIGTERM failed)  from ' + testName);
                        serverProcess.kill('SIGKILL');
                        if (killPhantom && phantomProcess !== null && phantomProcess.pid > 0 && phantomProcess.pid != process.pid) {
                            consoleLog('[INFO] SIGKILL (PhantomJS) from ' + testName);
                            phantomProcess.kill('SIGKILL');
                        }
                    } else {
                        consoleLog('[INFO] TIMEOUT - SIGKILL (Server) skipped in ' + testName + ' from ' + hardKillTimeoutTestname);
                    }
                }
            }, (dynamicTimeout * factor) + (10 * 1000));
        } else {
            if (softKillTimeoutTestname === testName) {
                softKilled = false;
                testHasTimeouted = false;
                consoleLog('[INFO] SIGTERM (Server) from ' + testName);
                serverProcess.kill('SIGTERM');
                if (killPhantom && phantomProcess !== null && phantomProcess.pid > 0 && phantomProcess.pid != process.pid) {
                    consoleLog('[INFO] SIGKILL (PhantomJS) from ' + testName);
                    phantomProcess.kill('SIGKILL');
                }
            } else {
                consoleLog('[INFO] SIGTERM (Server) skipped in ' + testName + ' from ' + softKillTimeoutTestname);
            }
            hardKillTimeout = setTimeout(function() {
                softKilled = false;
                if (serverProcess !== null && serverProcess.pid > 0 && serverProcess.pid != process.pid) {
                    if (hardKillTimeoutTestname === testName) {
                        hardKilled = true;
                        testHasTimeouted = false;
                        consoleLog('[WARN] SIGKILL (Server - SIGTERM failed) from ' + testName);
                        serverProcess.kill('SIGKILL');
                        if (killPhantom && phantomProcess !== null && phantomProcess.pid > 0 && phantomProcess.pid != process.pid) {
                            consoleLog('[INFO] SIGKILL (PhantomJS) from ' + testName);
                            phantomProcess.kill('SIGKILL');
                        }
                    } else {
                        consoleLog('[INFO] SIGKILL (Server) skipped in ' + testName + ' from ' + hardKillTimeoutTestname);
                    }
                }
            }, 10 * 1000);
        }
    }
}

// Run Maven test
function runMavenTest(opt, callback) {
    if (typeof config.noJavaTest !== 'undefined' && config.noJavaTest === true) {
        mavenProcess = null;
        consoleLog('[ERROR] Java tests are disabled');
        opt.callbackParams.error = 'Java tests are disabled';
        return wrapMavenTest(opt, callback);
    }
    ncp(opt.testPath, opt.config.WORKSPACE + path.sep, function(err) {
        clearTimeout(softMavenKillTimeout);
        clearTimeout(hardMavenKillTimeout);
        softKilled = false;
        hardKilled = false;
        testHasTimeouted = false;
        if (err) {
            mavenProcess = null;
            consoleLog('[ERROR] cannot copy project files to workspace', err);
            opt.callbackParams.error = err;
            return wrapMavenTest(opt, callback);
        }
        try {
            chmodrSync(opt.config.WORKSPACE, 0644);
        } catch (e) {
            consoleLog('[WARN] cannot chmod workspace', e);
        }
        if (/(studio|waf)/i.test(opt.testName)) {
            setUpSeleniumProxy(opt.config.WAKANDA_STUDIO_FOLDER, opt.pom, opt.config.WORKSPACE);
        }
        // setTimeout(function () {
        if (config.TEST_BRANCH === 'stable') {
            var pom = fs.readFileSync(actualPath(path.join(opt.config.WORKSPACE, 'pom.xml'))).toString();
            pom = pom.replace(/<repositories>\s*<repository>\s*<id>snapshots<\/id>\s*<url>http:\/\/192\.168\.7\.50:9000\/nexus\/content\/repositories\/snapshots\/?<\/url>/gim, '<repositories><repository><id>releases</id><url>http://192.168.7.50:9000/nexus/content/repositories/releases</url>');
            try {
                fs.writeFileSync(actualPath(path.join(opt.config.WORKSPACE, 'pom.xml')), pom.toString());
            } catch (e) {
                consoleLog('[WARN] cannot modify POM file for stable test branch (1)', e);
            }
        }
        var pom = fs.readFileSync(actualPath(path.join(opt.config.WORKSPACE, 'pom.xml'))).toString();
        if (pom.indexOf("maven-compiler-plugin") < 0) {
            if (pom.indexOf("plugins") < 0) {
                if (pom.indexOf("build") < 0) {
                    pom = pom.replace('</project>', '<build><plugins><plugin><artifactId>maven-compiler-plugin</artifactId><version>3.1</version><configuration><source>1.6</source><target>1.6</target><compilerArgument></compilerArgument></configuration></plugin></plugins></build></project>');
                } else {
                    pom = pom.replace('</build>', '<plugins><plugin><artifactId>maven-compiler-plugin</artifactId><version>3.1</version><configuration><source>1.6</source><target>1.6</target><compilerArgument></compilerArgument></configuration></plugin></plugins></build>');
                }
            } else {
                pom = pom.replace('</plugins>', '<plugin><artifactId>maven-compiler-plugin</artifactId><version>3.1</version><configuration><source>1.6</source><target>1.6</target><compilerArgument></compilerArgument></configuration></plugin></plugins>');
            }
            try {
                fs.writeFileSync(actualPath(path.join(opt.config.WORKSPACE, 'pom.xml')), pom.toString());
            } catch (e) {
                consoleLog('[WARN] cannot tweak POM file (maven-compiler-plugin)', e);
            }
        }
        if (typeof opt.config.use_proxy !== 'undefined' && opt.config.use_proxy === false) {
            try {
                var settings = fs.readFileSync(actualPath(path.join(opt.config.WORKSPACE, 'settings.xml'))).toString();
                settings = settings.replace(/<active>\s*true\s*<\/active>/gim, '<active>false</active>');
                fs.writeFileSync(actualPath(path.join(opt.config.WORKSPACE, 'settings.xml')), settings.toString());
            } catch (e) {
                consoleLog('[WARN] cannot disable proxy in settings.xml file (1)', e);
            }
        }
        if (config.TEST_BRANCH === 'stable') {
            opt.config.DEPENDENCY_VERSION = 'LATEST';
            opt.config.REPOSITORY_ID = 'releases';
            opt.config.REPOSITORY_URL = 'http://192.168.7.50:9000/nexus/content/repositories/releases/';
        } else {
            opt.config.DEPENDENCY_VERSION = 'LATEST';
            opt.config.REPOSITORY_ID = 'snapshots';
            opt.config.REPOSITORY_URL = 'http://192.168.7.50:9000/nexus/content/repositories/snapshots/';
        }
        if (typeof opt.config.mavenCmd !== 'string') {
            try {
                mavenProcess = spawn(opt.config.mavenCmd[0], opt.config.mavenCmd.slice(1), {
                    cwd: opt.config.WORKSPACE,
                    env: opt.config
                });
            } catch (e) {
                mavenProcess = null;
                consoleLog('[ERROR] cannot launch Maven project (1)', e);
                opt.callbackParams.error = e;
                return wrapMavenTest(opt, callback);
            }
        } else {
            var mavenCmd = opt.config.mavenCmd.split(' ');
            try {
                mavenProcess = spawn(mavenCmd[0], mavenCmd.slice(1), {
                    cwd: opt.config.WORKSPACE,
                    env: opt.config
                });
            } catch (e) {
                mavenProcess = null;
                consoleLog('[ERROR] cannot launch Maven project (2a)', e);
                opt.callbackParams.error = e;
                return wrapMavenTest(opt, callback);
            }
        }
        mavenProcess.on('error', function(e) {
            mavenProcess = null;
            consoleLog('[ERROR] cannot launch Maven project (2b)', e);
            opt.callbackParams.error = e;
            wrapMavenTest(opt, callback)
        });
        mavenProcess.stdout.on('data', function(data) {
            if (opt.callbackParams.stdout === null) opt.callbackParams.stdout = '';
            opt.callbackParams.stdout += data.toString();
            consoleLog('[STDOUT] ' + data.toString());
            if (isInDebugMode() === false) timeoutMaven(opt.testName);
        });
        mavenProcess.stderr.on('data', function(data) {
            if (opt.callbackParams.stderr === null) opt.callbackParams.stderr = '';
            opt.callbackParams.stderr += data.toString();
            consoleLog('[STDERR] ' + data.toString());
            if (isInDebugMode() === false) timeoutMaven(opt.testName);
        });
        mavenProcess.on('exit', function(code) {
            mavenProcess = null;
            if (testHasTimeouted === true) {
                testHasTimeouted = false;
                consoleLog('[WARN] Maven killed after TIMEOUT');
            }
            consoleLog('[INFO] Maven exited with code', code);
            opt.callbackParams.exitCode = code;
            wrapMavenTest(opt, callback);
        });
        if (isInDebugMode() === false) timeoutMaven(opt.testName);
    });
}

function wrapMavenTest(opt, callback) {
    opt.callbackParams.end = new Date();
    opt.callbackParams.duration = opt.callbackParams.end.getTime() - opt.callbackParams.start.getTime();
    emptyReport(opt);
    exterminateLocal(opt.config.WORKSPACE, function() {
        if (opt.callbackParams.error) {
            consoleLog('[ERROR] cannot run Maven test', opt.callbackParams.error);
            opt.callbackParams.status = null;
            if (opt.callbackParams.stderr) {
                opt.callbackParams.stderr = opt.callbackParams.stderr.toString() + '\n' + opt.callbackParams.error.toString();
            } else {
                opt.callbackParams.stderr = opt.callbackParams.error.toString();
            }
        }
        if (opt.callbackParams.stdout) {
            try {
                fs.writeFileSync(path.join(opt.destFullPath, 'stdout.txt'), opt.callbackParams.stdout.toString());
            } catch (e) {
                consoleLog('[WARN] cannot write stdout (3)', e);
            }
        }
        if (opt.callbackParams.stderr) {
            try {
                fs.writeFileSync(path.join(opt.destFullPath, 'stderr.txt'), opt.callbackParams.stderr.toString());
            } catch (e) {
                consoleLog('[WARN] cannot write stderr (2)', e);
            }
        }
        var artifacts = [];
        try {
            fs.readdirSync(opt.config.WORKSPACE).forEach(function(artifact) {
                if (/^(pom|settings)\./i.test(artifact) === false) {
                    if (/\.log$/i.test(artifact) || /\.xml$/i.test(artifact)) {
                        artifacts.push(path.join(opt.config.WORKSPACE, artifact));
                    }
                }
            });
        } catch (e) {
            // Doesn't matter
        }
        try {
            fs.readdirSync(path.join(opt.config.WORKSPACE, 'Errors')).forEach(function(artifact) {
                if (/\.png$/i.test(artifact)) {
                    artifacts.push(path.join(opt.config.WORKSPACE, 'Errors', artifact));
                }
            });
        } catch (e) {
            // Doesn't matter
        }
        try {
            fs.readdirSync(path.join(opt.config.WORKSPACE, 'target')).forEach(function(artifact) {
                if (/^(pom|settings)\./i.test(artifact) === false) {
                    if (/\.xml$/i.test(artifact)) {
                        artifacts.push(path.join(opt.config.WORKSPACE, 'target', artifact));
                    }
                }
            });
        } catch (e) {
            // Doesn't matter
        }
        try {
            fs.readdirSync(path.join(opt.config.WORKSPACE, 'target', 'surefire-reports')).forEach(function(artifact) {
                if (/^(pom|settings)\./i.test(artifact) === false) {
                    if (/\.xml$/i.test(artifact)) {
                        artifacts.push(path.join(opt.config.WORKSPACE, 'target', 'surefire-reports', artifact));
                    }
                }
            });
        } catch (e) {
            // Doesn't matter
        }
        try {
            findFiles(opt.config.WORKSPACE, /_log_.*\.txt$/i).forEach(function(logFile) {
                artifacts.push(logFile);
            });
        } catch (e) {
            // Doesn't matter
        }
        try {
            findFiles(opt.config.WORKSPACE, /\.walog$/i).forEach(function(logFile) {
                artifacts.push(logFile);
            });
        } catch (e) {
            // Doesn't matter
        }
        var report = null;
        artifacts.forEach(function(artifact) {
            if (/\.walog$/i.test(path.basename(artifact))) {
                var baseName = 'http.txt';
            } else if (/_log_.*\.txt$/i.test(path.basename(artifact))) {
                var baseName = 'application.txt';
            } else {
                var baseName = path.basename(artifact);
            }
            var dest = path.join(opt.destFullPath, baseName);
            if (report === null && /\.xml$/i.test(artifact)) {
                var content = fs.readFileSync(artifact).toString();
                if (/<testsuite/ig.test(content)) {
                    report = content;
                    dest = path.join(opt.destFullPath, 'report.xml');
                }
            }
            try {
                copyFileSync(artifact, dest);
            } catch (e) {
                consoleLog('[WARN] cannot copy artifact', e);
            }
        });
        if (report === null) {
            consoleLog('[ERROR] XML report not found (3)');
            opt.callbackParams.status = null;
            if (!opt.callbackParams.error) opt.callbackParams.error = 'XML report not found';
            clearCache(true);
            return callback(opt.callbackParams);
        }
        try {
            parseString(report, function(err, rawresult) {
                if (err) {
                    consoleLog('[ERROR] cannot parse XML report (3)', err);
                    opt.callbackParams.status = null;
                    if (!opt.callbackParams.error) opt.callbackParams.error = err;
                    clearCache(true);
                    return callback(opt.callbackParams);
                }
                if (typeof rawresult.testsuite !== 'undefined' && typeof rawresult.testsuite.$ !== 'undefined' && typeof rawresult.testsuite.$.tests !== 'undefined' && typeof rawresult.testsuite.$.errors !== 'undefined' && typeof rawresult.testsuite.$.failures !== 'undefined') {
                    var result = {
                        name: opt.testName,
                        pom: opt.pom,
                        path: opt.testPath,
                        changelist: opt.config.CHANGELIST,
                        start: opt.callbackParams.start,
                        end: opt.callbackParams.end,
                        duration: opt.callbackParams.end.getTime() - opt.callbackParams.start.getTime(),
                        bench: false,
                        abstract: {
                            total: parseInt(rawresult.testsuite.$.tests),
                            failures: parseInt(rawresult.testsuite.$.failures) + parseInt(rawresult.testsuite.$.errors),
                            skipped: parseInt(rawresult.testsuite.$.skipped)
                        },
                        passed: [],
                        failed: [],
                        skipped: []
                    };
                    result.abstract.passed = result.abstract.total - result.abstract.failures - result.abstract.skipped;
                    result.abstract.success = (result.abstract.passed / result.abstract.total) * 100;
                    if (result.abstract.total === 0 || result.abstract.total === result.abstract.failures || result.abstract.failures > 0 || result.abstract.total === result.abstract.errors || result.abstract.errors > 0) {
                        result.status = false;
                    } else {
                        result.status = true;
                    }
                    var commonTrunkMap = null;
                    rawresult.testsuite.testcase.forEach(function(testcase) {
                        if (typeof testcase.$.classname !== 'undefined' && testcase.$.classname !== '') {
                            var _classname = testcase.$.classname.split('.');
                            if (commonTrunkMap === null) {
                                commonTrunkMap = _classname;
                            } else {
                                var commonTrunk = [];
                                for (var mi = 0; mi < commonTrunkMap.length; mi++) {
                                    if (mi === _classname.length || commonTrunkMap[mi] !== _classname[mi]) {
                                        break;
                                    } else {
                                        commonTrunk.push(commonTrunkMap[mi]);
                                    }
                                }
                                commonTrunkMap = commonTrunk;
                            }
                        }
                    });
                    var stacktraces = [];
                    rawresult.testsuite.testcase.forEach(function(testcase) {
                        if (typeof testcase.$.classname === 'undefined' || testcase.$.classname === '') {
                            var _name = testcase.$.name;
                        } else {
                            if (commonTrunkMap.length === 0) {
                                var _name = testcase.$.classname + '.' + testcase.$.name;
                            } else {
                                var _className = testcase.$.classname.replace(commonTrunkMap.join('.'), '');
                                if (_className !== '') {
                                    var _name = _className.replace(/^\./, '') + '.' + testcase.$.name;
                                } else {
                                    var _name = testcase.$.name;
                                }
                            }
                        }
                        if (typeof testcase.failure !== 'undefined') {
                            result.failed.push({
                                name: _name,
                                failure: testcase.failure[0].$.message,
                                time: (parseFloat(testcase.$.time) * 1000).toFixed()
                            });
                        } else if (typeof testcase.error !== 'undefined') {
                            result.failed.push({
                                name: _name,
                                failure: testcase.error[0].$.message,
                                time: (parseFloat(testcase.$.time) * 1000).toFixed()
                            });
                            var stacktrace = {
                                name: _name,
                                failure: testcase.error[0]._.toString()
                            };
                            if (typeof testcase['system-out'] !== 'undefined') {
                                stacktrace.out = testcase['system-out'][0].toString();
                            }
                            if (typeof testcase['system-err'] !== 'undefined') {
                                stacktrace.err = testcase['system-err'][0].toString();
                            }
                            stacktraces.push(stacktrace);
                        } else if (typeof testcase.skipped !== 'undefined') {
                            result.skipped.push({
                                name: _name
                            });
                        } else {
                            result.passed.push({
                                name: _name,
                                time: (parseFloat(testcase.$.time) * 1000).toFixed()
                            });
                        }
                    });
                    stacktraces.forEach(function(stacktrace) {
                        try {
                            fs.writeFileSync(path.join(opt.destFullPath, stacktrace.name + '.stack'), JSON.stringify(stacktrace));
                        } catch (e) {
                            consoleLog('[WARN] cannot write stacktrace (1)', e);
                        }
                    });
                    opt.callbackParams.result = result;
                    opt.callbackParams.status = result.status;
                    if (!opt.callbackParams.error) opt.callbackParams.error = null;
                    try {
                        fs.writeFileSync(path.join(opt.destFullPath, 'report.json'), JSON.stringify(result));
                    } catch (e) {
                        consoleLog('[ERROR] cannot write JSON report (3)', e);
                        opt.callbackParams.status = null;
                        if (!opt.callbackParams.error) opt.callbackParams.error = e;
                    }
                    clearCache(true);
                    return callback(opt.callbackParams);
                } else {
                    consoleLog('[ERROR] XML report incomplete or malformed (3)');
                    opt.callbackParams.status = null;
                    if (!opt.callbackParams.error) opt.callbackParams.error = 'XML report incomplete or malformed';
                    clearCache(true);
                    return callback(opt.callbackParams);
                }
            });
        } catch (e) {
            consoleLog('[ERROR] cannot parse XML report (3)', e);
            opt.callbackParams.status = null;
            if (!opt.callbackParams.error) opt.callbackParams.error = e;
            clearCache(true);
            return callback(opt.callbackParams);
        }
    });
}

function timeoutMaven(testName, now) {
    if (typeof now === 'undefined') {
        now = false;
    }
    clearTimeout(softMavenKillTimeout);
    clearTimeout(hardMavenKillTimeout);
    softMavenKillTimeoutTestname = testName;
    hardMavenKillTimeoutTestname = testName;
    testHasTimeouted = false;
    if (mavenProcess !== null && mavenProcess.pid > 0 && mavenProcess.pid != process.pid) {
        if (now === false) {
            softMavenKillTimeout = setTimeout(function() {
                if (mavenProcess !== null && mavenProcess.pid > 0 && mavenProcess.pid != process.pid) {
                    if (softMavenKillTimeoutTestname === testName) {
                        softKilled = true;
                        testHasTimeouted = true;
                        consoleLog('[ERROR] TIMEOUT - SIGTERM (Maven) from ' + testName);
                        mavenProcess.kill('SIGTERM');
                    } else {
                        consoleLog('[INFO] TIMEOUT - SIGTERM (Maven) skipped in ' + testName + ' from ' + softMavenKillTimeoutTestname);
                    }
                }
            }, dynamicTimeout);
            hardMavenKillTimeout = setTimeout(function() {
                softKilled = false;
                if (mavenProcess !== null && mavenProcess.pid > 0 && mavenProcess.pid != process.pid) {
                    if (hardMavenKillTimeoutTestname === testName) {
                        hardKilled = true;
                        testHasTimeouted = true;
                        consoleLog('[ERROR] TIMEOUT - SIGKILL (Maven - SIGTERM failed) from ' + testName);
                        mavenProcess.kill('SIGKILL');
                    } else {
                        consoleLog('[INFO] TIMEOUT - SIGKILL (Maven) skipped in ' + testName + ' from ' + hardMavenKillTimeoutTestname);
                    }
                }
            }, dynamicTimeout + (10 * 1000));
        } else {
            hardMavenKillTimeout = setTimeout(function() {
                softKilled = false;
                if (mavenProcess !== null && mavenProcess.pid > 0 && mavenProcess.pid != process.pid) {
                    if (hardMavenKillTimeoutTestname === testName) {
                        hardKilled = true;
                        testHasTimeouted = false;
                        consoleLog('[WARN] SIGKILL (Maven - SIGTERM failed) from ' + testName);
                        mavenProcess.kill('SIGKILL');
                    } else {
                        consoleLog('[INFO] SIGKILL (Maven) skipped in ' + testName + ' from ' + hardMavenKillTimeoutTestname);
                    }
                }
            }, 10 * 1000);
            if (softMavenKillTimeoutTestname === testName) {
                softKilled = false;
                testHasTimeouted = false;
                consoleLog('[INFO] SIGTERM (Maven) from ' + testName);
                mavenProcess.kill('SIGTERM');
            } else {
                consoleLog('[INFO] SIGTERM (Maven) skipped in ' + testName + ' from ' + softMavenKillTimeoutTestname);
            }
        }
    }
}

function emptyReport(opt) {
    opt.callbackParams.result = {
        name: opt.testName,
        pom: opt.pom,
        path: opt.testPath,
        changelist: opt.config.CHANGELIST,
        start: opt.callbackParams.start,
        end: opt.callbackParams.end,
        duration: opt.callbackParams.end.getTime() - opt.callbackParams.start.getTime(),
        bench: false,
        abstract: {
            total: 0,
            failures: 0,
            skipped: 0,
            passed: 0,
            success: 0
        },
        passed: [],
        failed: [],
        skipped: [],
        status: null
    };
    try {
        fs.writeFileSync(path.join(opt.destFullPath, 'report.json'), JSON.stringify(opt.callbackParams.result));
    } catch (e) {
        consoleLog('[ERROR] cannot write JSON report (empty)', e);
    }
}