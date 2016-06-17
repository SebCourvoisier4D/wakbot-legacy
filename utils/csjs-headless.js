var page = require('webpage').create(),
system = require('system'),
fs = require('fs'),
url,
destinationFolder,
trifleCheckInterval;

if (system.args.length !== 3) {
	console.log('[csjs-headless][error] missing args.');
	phantom.exit(1);
}

url = system.args[1];
destinationFolder = system.args[2];
page.viewportSize = {
	width: 1280,
	height: 1024
};

page.onConsoleMessage = function(msg) {
	console.log('[csjs-headless][runtime log] ' + msg);
};

page.onCallback = function(data) {
	finalize(data);
};

function finalize(data) {
	var report = data.report, 
		formatted = data.formatted, 
		format = data.format;
  	fs.write(destinationFolder + 'report.json', JSON.stringify(report), 'w');
  	if (formatted && format) {
  		switch (format.toLowerCase()) {
  			case 'junit':
  				fs.write(destinationFolder + 'report.xml', formatted.toString(), 'w');
  				break;
  			case 'html':
  				fs.write(destinationFolder + 'report.html', formatted.toString(), 'w');
  				break;
  		}
  	}
  	console.log('[csjs-headless][done] completion: ' + report.completion + '% - passes: ' + report.passes + ' - failures: ' + report.failures + ' - skipped: ' + report.skipped + ' - duration: ' + report.duration);
  	if (typeof trifle === 'undefined') page.render(destinationFolder + 'screenshot.png');
	phantom.exit(0);
}

phantom.onError = function(msg, trace) {
	var msgStack = ['[csjs-headless][fatal] ' + msg];
	if (trace && trace.length) {
		trace.forEach(function(t) {
			msgStack.push(' -> ' + (t.file || t.sourceURL) + ': ' + t.line + (t.function ? ' (in function ' + t.function +')' : ''));
		});
	}
	console.log(msgStack.join('\n'));
	if (typeof trifle === 'undefined') page.render(destinationFolder + 'screenshot.png');
	phantom.exit(1);
};

page.onError = function(msg, trace) {
	var msgStack = ['[csjs-headless][runtime error] ' + msg];
	if (trace && trace.length) {
		trace.forEach(function(t) {
			msgStack.push(' -> ' + t.file + ': ' + t.line + (t.function ? ' (in function "' + t.function +'")' : ''));
		});
	}
	console.log(msgStack.join('\n'));
	if (typeof trifle === 'undefined') page.render(destinationFolder + 'screenshot.png');
	phantom.exit(1);
};

page.onAlert = function(msg) {
	console.log('[csjs-headless][alert] ' + msg);
}

page.onResourceRequested = function(request) {
	if (/^data:/.test(request.url) === false) {
		console.log('[csjs-headless][request] ' + request.url);
	}
};

page.onResourceReceived = function(response) {
	if (/^data:/.test(response.url) === false) {
		console.log('[csjs-headless][response] ' + response.status + ' (' + response.url + ')');
	}
};

console.log('[csjs-headless][start]');

page.open(url, function(status) {
	if (status !== 'success') {
		console.log('[csjs-headless][error] unable to load the page ' + url);
		phantom.exit(1);
	} else {
		if (typeof trifle === 'undefined') {
			console.log(page.evaluate(function() {
				window.waktest_ended = function (report, formatted, format) {
					window.callPhantom({report: report, formatted: formatted, format: format});
				}
				return '[csjs-headless][loaded]';
			}));
		} else {
			console.log('[csjs-headless][loaded]');
			if (/format=(junit|html)/i.test(url) === true) {
				trifleCheckInterval = window.setInterval(function() {
					var reportStatus = page.evaluate(function() {
						return typeof mocha._wakanda_formatted_report;
					});
					if (reportStatus == 'string') {
						window.clearInterval(trifleCheckInterval);
						var report = page.evaluate(function() {
							return JSON.stringify({report: mocha._wakanda_report, formatted: mocha._wakanda_formatted_report, format: mocha.queryParams.format});
						});
						finalize(JSON.parse(report));
					}
				}, 5);
			} else {
				trifleCheckInterval = window.setInterval(function() {
					var reportStatus = page.evaluate(function() {
						return typeof mocha._wakanda_report;
					});
					if (reportStatus == 'object') {
						window.clearInterval(trifleCheckInterval);
						var report = page.evaluate(function() {
							return JSON.stringify(mocha._wakanda_report);
						});
						finalize({report: JSON.parse(report)});
					}
				}, 5);
			}			
		}		
		window.setTimeout(function() {
			if (typeof trifle === 'undefined') page.render(destinationFolder + 'screenshot.png');
			console.log('[csjs-headless][error] test failed after timeout');
			phantom.exit(1);
		}, 5 * 60 * 1000);
	}
});