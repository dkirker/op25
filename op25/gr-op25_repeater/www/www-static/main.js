
// Copyright 2017, 2018 Max H. Parke KA1RBI
// Copyright 2018, 2019, 2020, 2021 gnorbury@bondcar.com
// 
// This file is part of OP25
// 
// OP25 is free software; you can redistribute it and/or modify it
// under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 3, or (at your option)
// any later version.
// 
// OP25 is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
// or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public
// License for more details.
// 
// You should have received a copy of the GNU General Public License
// along with OP25; see the file COPYING. If not, write to the Free
// Software Foundation, Inc., 51 Franklin Street, Boston, MA
// 02110-1301, USA.

var d_debug = 1;

var http_req = new XMLHttpRequest();
var terminal_config = {};
var full_config = {};
var counter1 = 0;
var error_val = null;
var auto_tracking = null;
var fine_tune = null;
var current_tgid = null;
var capture_active = false;
var send_busy = 0;
var send_qfull = 0;
var send_queue = [];
var req_cb_count = 0;
var request_count = 0;
var nfinal_count = 0;
var n200_count = 0;
var r200_count = 0;
var SEND_QLIMIT = 5;
var c_freq = 0;
var c_ppm = null;
var c_system = null;
var c_tag = null;
var c_stream_url = null;
var c_srctag = "";
var c_srcaddr = 0;
var c_grpaddr = 0;
var c_encrypted = 0;
var c_nac = 0;
var c_name = "";
var channel_list = [];
var channel_index = 0;

var last_tgid = null;
var tg_list = [];
var talkgroup_lists = [];

function find_parent(ele, tagname) {
    while (ele) {
        if (ele.nodeName == tagname)
            return (ele);
        else if (ele.nodeName == "HTML")
            return null;
        ele = ele.parentNode;
    }
    return null;
}

function f_command(ele, command) {
    var myrow = find_parent(ele, "TR");
    if (command == "delete") {
        var ok = confirm ("Confirm delete");
        if (ok)
            myrow.parentNode.removeChild(myrow);
    } else if (command == "clone") {
        var newrow = myrow.cloneNode(true);
        if (myrow.nextSibling)
            myrow.parentNode.insertBefore(newrow, myrow.nextSibling);
        else
            myrow.parentNode.appendChild(newrow);
    } else if (command == "new") {
        var mytbl = find_parent(ele, "TABLE");
        var newrow = null;
        if (mytbl.id == "chtable")
            newrow = document.getElementById("chrow").cloneNode(true);
        else if (mytbl.id == "devtable")
            newrow = document.getElementById("devrow").cloneNode(true);
        else
            return;
        mytbl.appendChild(newrow);
    }
}

function nav_update(command) {
	var names = ["b1", "b2", "b3"];
	var bmap = { "status": "b1", "plot": "b2", "about": "b3" };
	var id = bmap[command];
	for (var id1 in names) {
		b = document.getElementById(names[id1]);
		if (names[id1] == id) {
			b.className = "nav-button-active";
		} else {
			b.className = "nav-button";
		}
	}
}

function f_select(command) {
    var div_status = document.getElementById("div_status")
    var div_plot   = document.getElementById("div_plot")
    var div_about  = document.getElementById("div_about")
    var div_s1     = document.getElementById("div_s1")
    var div_s2     = document.getElementById("div_s2")
    var div_s3     = document.getElementById("div_s3")
    var ctl1 = document.getElementById("controls1");
    var ctl2 = document.getElementById("controls2");
    if (command == "status") {
        div_status.style['display'] = "";
        div_plot.style['display'] = "none";
        div_about.style['display'] = "none";
        div_s1.style['display'] = "";
        div_s2.style['display'] = "";
        div_s3.style['display'] = "";
        ctl1.style['display'] = "";
        ctl2.style['display'] = "none";
    }
    else if (command == "plot") {
        div_status.style['display'] = "";
        div_plot.style['display'] = "";
        div_about.style['display'] = "none";
        div_s1.style['display'] = "none";
        div_s2.style['display'] = "";
        div_s3.style['display'] = "none";
        ctl1.style['display'] = "none";
        ctl2.style['display'] = "";
    }
    else if (command == "about") {
        div_status.style['display'] = "none";
        div_plot.style['display'] = "none";
        div_about.style['display'] = "";
        ctl1.style['display'] = "none";
        ctl2.style['display'] = "none";
    }
    nav_update(command);
}

function is_digit(s) {
    if (s >= "0" && s <= "9")
        return true;
    else
        return false;
}

function term_config(d) {
    var lg_step = 1200;
    var sm_step = 100;
    var updated = 0;

    terminal_config = d;

    if ((d["tuning_step_large"] != undefined) && (d["tuning_step_large"] != lg_step)) {
        lg_step = d["tuning_step_large"];
        updated++;
    }
    if ((d["tuning_step_small"] != undefined) && (d["tuning_step_small"] != sm_step)) {
        sm_step = d["tuning_step_small"];
        updated++;
    }
    if (updated) {
        set_tuning_step_sizes(lg_step, sm_step);
    }
}

function do_update_config() {
    send_command("get_full_config", 0, 0);
}

function full_config_handler(d) {
    talkgroup_lists = d['talkgroup_lists'];

    full_config = d;

    term_config(d['terminal']);
}

function set_tuning_step_sizes(lg_step=1200, sm_step=100) {
    var title_str = "Adjust tune ";

    var bn_t1_U = document.getElementById("t1_U");
    var bn_t2_U = document.getElementById("t2_U");
    var bn_t1_D = document.getElementById("t1_D");
    var bn_t2_D = document.getElementById("t2_D");
    var bn_t1_u = document.getElementById("t1_u");
    var bn_t2_u = document.getElementById("t2_u");
    var bn_t1_d = document.getElementById("t1_d");
    var bn_t2_d = document.getElementById("t2_d");

    if ((bn_t1_U != null) && (bn_t2_U != null)) {
        bn_t1_U.setAttribute("title", title_str + "+" + lg_step);
        bn_t2_U.setAttribute("title", title_str + "+" + lg_step);
        bn_t1_U.setAttribute("onclick", "javascript:f_tune_button(" + lg_step + ");");
        bn_t2_U.setAttribute("onclick", "javascript:f_tune_button(" + lg_step + ");");
    }
    if ((bn_t1_D != null) && (bn_t2_D != null)) {
        bn_t1_D.setAttribute("title", title_str + "-" + lg_step);
        bn_t2_D.setAttribute("title", title_str + "-" + lg_step);
        bn_t1_D.setAttribute("onclick", "javascript:f_tune_button(-" + lg_step + ");");
        bn_t2_D.setAttribute("onclick", "javascript:f_tune_button(-" + lg_step + ");");
    }
    if ((bn_t1_u != null) && (bn_t2_u != null)) {
        bn_t1_u.setAttribute("title", title_str + "+" + sm_step);
        bn_t2_u.setAttribute("title", title_str + "+" + sm_step);
        bn_t1_u.setAttribute("onclick", "javascript:f_tune_button(" + sm_step + ");");
        bn_t2_u.setAttribute("onclick", "javascript:f_tune_button(" + sm_step + ");");
    }
    if ((bn_t1_d != null) && (bn_t2_d != null)) {
        bn_t1_d.setAttribute("title", title_str + "-" + sm_step);
        bn_t2_d.setAttribute("title", title_str + "-" + sm_step);
        bn_t1_d.setAttribute("onclick", "javascript:f_tune_button(-" + sm_step + ");");
        bn_t2_d.setAttribute("onclick", "javascript:f_tune_button(-" + sm_step + ");");
    }
}

function rx_update(d) {
    plotfiles = [];
    if ((d["files"] != undefined) && (d["files"].length > 0)) {
        for (var i=0; i < d["files"].length; i++) {
            if (channel_list.length > 0) {
                expr = new RegExp("plot\-" + channel_list[channel_index] + "\-");
            }
            else {
                expr = new RegExp("plot\-0\-");
            }

            if (expr.test(d["files"][i])) {
                plotfiles.push(d["files"][i]);
            }
        }

        for (var i=0; i < 5; i++) {
            var img = document.getElementById("img" + i);
            if (i < plotfiles.length) {
                if (img['src'] != plotfiles[i]) {
                    img['src'] = plotfiles[i];
                    img.style["display"] = "";
                }
            }
            else {
                img.style["display"] = "none";
            }
        }
    }
    else {
        var img = document.getElementById("img0");
        img.style["display"] = "none";
    }
    if (d["error"] != undefined)
        error_val = d["error"];
    else
        error_val = null;
    if (d["fine_tune"] != undefined)
        fine_tune = d["fine_tune"];
}

// frequency, system, and talkgroup display

function change_freq(d) {
    c_freq = d['freq'];
    c_system = d['system'];
    current_tgid = d['tgid'];
    c_tag = d['tag'];
    c_stream_url = d['stream_url'];
    channel_status();
}

function format_talkgroup_lists() {
    var html = "";

    for (system in talkgroup_lists) {
        var added = false;
        var title = "<b>" + system + ":</b><br/>";
        var allowed = "";
        var blocked = "";

        if (talkgroup_lists[system].allowed && talkgroup_lists[system].allowed.length > 0) {
            added = true;
            allowed = "<tr><td style=\"border-style: none\">Allowed:</td><td style=\"border-style: none\">" + talkgroup_lists[system].allowed.join(", ") + "</td></tr>";
        }
        if (talkgroup_lists[system].blocked && talkgroup_lists[system].blocked.length > 0) {
            added = true;
            blocked = "<tr><td style=\"border-style: none\">Blocked:</td><td style=\"border-style: none\">" + talkgroup_lists[system].blocked.join(", ") + "</td></tr>";
        }

        if (added) {
            if (html != "") {
                html += "<br/>";
            }
            html += title;
            html += "<table border=\"0\" borderwidth=\"0\" cellpadding=\"0\" cellspacing=\"0\" style=\"background: none\">" + allowed + blocked + "</table>";
        }
    }

    if (html != "") {
        html = "<tr style=\"background-color: #c0c0c0\"><td colspan=99 style=\"align: center\">" + html + "</td></tr>";
    }

    return html;
}

function channel_update(d) {
    var s2_c  = document.getElementById("s2_ch_lbl");
    var s2_d  = document.getElementById("s2_ch_txt");
    var s2_e  = document.getElementById("s2_ch_dn");
    var s2_f  = document.getElementById("s2_ch_dmp");
    var s2_g  = document.getElementById("s2_ch_up");
    var s2_hc = document.getElementById("s2_ch_cap");
    var s2_ht = document.getElementById("s2_ch_trk");

    if (d['channels'] != undefined) {
        channel_list = d['channels'];    

        if (channel_list.length > 0) {
            var c_id = channel_list[channel_index];
            c_system = d[c_id]['system'];
            if (c_id > -1) {
                c_name = "[" + c_id + "] ";
            } else {
                c_name = "";
            }
            if ((d[c_id]['name'] != undefined) && (d[c_id]['name'] != "")) {
                c_name += d[c_id]['name'];
            }
            else {
                c_name += c_system;
            }
            s2_d.innerHTML = "<span class=\"value\">" + c_name + "</span>";

            c_freq = d[c_id]['freq'];
            c_ppm = d[c_id]['ppm'];
            if (d[c_id]['error'] != undefined)
                error_val = d[c_id]['error'];
            else
                error_val = null;
            if (d[c_id]['auto_tracking'] != undefined)
                auto_tracking = d[c_id]['auto_tracking'];
            current_tgid = d[c_id]['tgid'];
            c_tag = d[c_id]['tag'];
            c_srcaddr = d[c_id]['srcaddr'];
            c_srctag = d[c_id]['srctag'];
            c_stream_url = d[c_id]['stream_url'];
            capture_active = d[c_id]['capture'];
            s2_c.style['display'] = "";
            s2_d.style['display'] = "";
            s2_e.style['display'] = "";
            s2_f.style['display'] = "";
            s2_g.style['display'] = "";
            s2_hc.style['display'] = "";
            s2_ht.style['display'] = "";

            if (current_tgid != null && last_tgid != null && (current_tgid != last_tgid.id || d[c_id]['srcaddr'] != last_tgid.srcaddr)) {
                var tgdata = {
                        date: Date.now(),
                        system: c_system,
                        tgid: current_tgid,
                        tag: c_tag,
                        srcaddr: c_srcaddr,
                        srctag: c_srctag
                    };

                tg_list.unshift(tgdata);
            }
            last_tgid = {id: current_tgid, srcaddr: c_srcaddr};

            if (tg_list.length > 0) {
                var tg_history = document.getElementById("tg_history");
                var tghtml = "<table border=\"1\" borderwidth=\"0\" cellpadding=\"0\" cellspacing=\"0\" width=\"860px\">" +
                            "<tr><th colspan=99 style=\"align: center\">Talkgroup History</th></tr>" +
                            format_talkgroup_lists() +
                            "<tr><th width=\"20%\">Time</th><th>System</th><th>Src ID</th><th>Source</th><th>TG ID</th><th>Tag</th></tr>";

                for (var i = 0; i < tg_list.length; i++) {
                    var itg = tg_list[i];
                    var color = "#d0d0d0";

                    if ((i & 1) == 0)
                        color = "#c0c0c0";

                    var getLocale = function() {
                        return (navigator.languages && navigator.languages.length) ? navigator.languages[0] : navigator.language;
                    };


                    var locale = getLocale();
                    var dateFmt = new Intl.DateTimeFormat(
                            locale,
                            {month: "numeric", day: "numeric", hour: "numeric", minute: "numeric", second: "numeric"}
                        );
                    var dateStr = dateFmt.format(new Date(itg.date));

                    tghtml += "<tr style=\"background-color: " + color + "; vertical-align: top;\">" +
                            "<td>" + dateStr + "</td>" +
                            "<td>" + itg.system + "</td>" +
                            "<td>" + itg.srcaddr + "</td>" +
                            "<td>" + itg.srctag + "</td>" +
                            "<td>" + (itg.tgid != null ? itg.tgid : "0") + "</td>" +
                            "<td>" + itg.tag + "</td></tr>";

                }
                tghtml += "</table>";
		tg_history.innerHTML = tghtml;
            }
        }
        else {
            s2_c.style['display'] = "none";
            s2_d.style['display'] = "none";
            s2_e.style['display'] = "none";
            s2_f.style['display'] = "none";
            s2_g.style['display'] = "none";
            s2_hc.style['display'] = "none";
            s2_ht.style['display'] = "none";
            c_name = "";
            c_freq = 0.0;
            c_system = "";
            current_tgid = 0;
            c_tag = "";
            c_srcaddr = 0;
            c_srctag = "";
            c_stream_url = "";
        }
        channel_status();
    }
}

function channel_status() {
    var html;
    var s2_freq = document.getElementById("s2_freq");
    var s2_tg = document.getElementById("s2_tg");
    var s2_grp = document.getElementById("s2_grp");
    var s2_src = document.getElementById("s2_src");
    var s2_ch_txt = document.getElementById("s2_ch_txt");
    var s2_cap = document.getElementById("cap_bn");
    var s2_trk = document.getElementById("trk_bn");

    html = "";
    if (c_stream_url != "") {
        html += "<a href=\"" + c_stream_url + "\">";
    }
    html += "<span class=\"value\">" + (c_freq / 1000000.0).toFixed(6) + "</span>";
    if (c_stream_url != "") {
        html += "</a>"
    }
    if (c_ppm != null) {
        html += "<span class=\"value\"> (" + c_ppm.toFixed(3) + ")</span>";
    }
    s2_freq.innerHTML = html
    if ((c_system != null) && (channel_list.length == 0))
    {
        s2_ch_txt.innerHTML = "<span class=\"value\"> &nbsp;" + c_system + "</span>";
        s2_ch_txt.style['display'] = "";
    }

    html = "";
    if (c_tag != null) {
        html += "<span class=\"value\">" + c_tag + "</span>";
        if ((current_tgid != null) && (c_encrypted)) {
            html += "<span class=\"label\">[ENCRYPTED]</span>";
        }
    }
    else
    {
        html += "<span class=\"value\">&nbsp;</span>";
    }
    s2_tg.innerHTML = html;

    html = "";
    if (current_tgid != null) {
        html += "<span class=\"value\">" + current_tgid + "</span>";
    }
    else if (c_grpaddr != 0) {
        html += "<span class=\"value\">" + c_grpaddr + "</span>";
    }
    else
    {
        html += "<span class=\"value\">&nbsp;</span>";
    }
    s2_grp.innerHTML = html;

    html = "";
    if ((c_srcaddr != 0) && (c_srcaddr != 0xffffff)) 
        if (c_srctag != "")
            html += "<span class=\"value\">" + c_srcaddr + "&nbsp;&ndash;&nbsp;" + c_srctag + "</span>";
        else
            html += "<span class=\"value\">" + c_srcaddr + "</span>";
    s2_src.innerHTML = html;

    if (capture_active)
        s2_cap.value = "stop capture";
    else
        s2_cap.value = "start capture";

    if (auto_tracking)
        s2_trk.value = "tracking off";
    else
        s2_trk.value = "tracking on";
}

// adjacent sites table

function adjacent_data(d) {
    if (Object.keys(d).length < 1) {
        var html = "</div>";
        return html;
    }
    var html = "<div class=\"adjacent\">";
    html += "<table border=1 borderwidth=0 cellpadding=0 cellspacing=0 width=100%>";
    html += "<tr><th colspan=99 style=\"align: center\">Adjacent Sites</th></tr>";
    html += "<tr><th>Frequency</th><th>RFSS</th><th>Site</th><th>Uplink</th></tr>";
    var ct = 0;
    for (var freq in d) {
        var color = "#d0d0d0";
        if ((ct & 1) == 0)
            color = "#c0c0c0";
        ct += 1;
        html += "<tr style=\"background-color: " + color + ";\"><td>" + (freq / 1000000.0).toFixed(6) + "</td><td>" + d[freq]["rfid"] + "</td><td>" + d[freq]["stid"] + "</td><td>" + (d[freq]["uplink"] / 1000000.0).toFixed(6) + "</td></tr>";
    }
    html += "</table></div></div><br><br>";

// end adjacent sites table

    return html;
}

// additional system info: wacn, sysID, rfss, site id, secondary control channels, freq error

function trunk_update(d) {
    var do_hex = {"syid":0, "sysid":0, "wacn": 0};
    var do_float = {"rxchan":0, "txchan":0};
    var srcaddr = 0;
    var encrypted = 0;
    var html = "";

    if (d['nac'] != undefined)
        c_nac = d['nac']

    for (var nac in d) {
        if (!is_digit(nac.charAt(0)))
            continue;

        // If 'system' name is defined, use it to correlate system info with channel currently selected
        // used by multi_rx.py trunking
        if (d[nac]['system'] != undefined) {
            if (d[nac]['system'] != c_system) {
                continue;
            }
            else {
                c_nac = d['nac'];
            }
        }
        // Otherwise use c_nac which is derived from "current_nac" parameter in 'change_freq' message
        // used by legacy rx.py trunking
        else if (nac != c_nac) {
            continue;
        }

        html += "<span class=\"nac\">";
        html += d[nac]['top_line'];
        html += "</span><br>";

        if (d[nac]['rfid'] != undefined)
            html += "<span class=\"label\">RFSS ID: </span><span class=\"value\">" + d[nac]['rfid'] + " </span>";
        if (d[nac]['stid'] != undefined)
            html += "<span class=\"label\">Site ID: </span><span class=\"value\">" + d[nac]['stid'] + "</span><br>";
        if (d[nac]['secondary'] != undefined && d[nac]["secondary"].length) {
            html += "<span class=\"label\">Secondary control channel(s): </span><span class=\"value\"> ";
            for (i=0; i<d[nac]["secondary"].length; i++) {
                html += (d[nac]["secondary"][i] / 1000000.0).toFixed(6);
                html += " ";
            }
            html += "</span><br>";
        }
        if (error_val != null) {
            if (auto_tracking != null) {
                html += "<span class=\"label\">Frequency error: </span><span class=\"value\">" + error_val + " Hz. (approx)</span><span class=\"label\"> auto tracking: </span><span class=\"value\">" + (auto_tracking ? "on" : "off") + " </span><br>";
            }
            else {
                html += "<span class=\"label\">Frequency error: </span><span class=\"value\">" + error_val + " Hz. (approx)</span><br>";
            }
        }
        if (fine_tune != null) {
            html += "<span class=\"label\">Fine tune offset: </span><span class=\"value\">" + fine_tune + "</span>";
        }
        var div_s1     = document.getElementById("div_s1")
        div_s1.innerHTML = html;

// system frequencies table
        html = ""
        html += "<div class=\"info\"><div class=\"system\">";
        html += "<table border=1 borderwidth=0 cellpadding=0 cellspacing=0 width=100%>"; // was width=350
        html += "<colgroup>";
        html += "<col span=\"1\" style=\"width:25%;\">";
        html += "<col span=\"1\" style=\"width:15%;\">";
        html += "<col span=\"1\" style=\"width:24%;\">";
        html += "<col span=\"1\" style=\"width:24%;\">";
        html += "<col span=\"1\" style=\"width:12%;\">";
        html += "</colgroup>";
        html += "<tr><th colspan=99 style=\"align: center\">System Frequencies</th></tr>";
        html += "<tr><th>Voice Frequency</th><th>Last Used</th><th colspan=2>Active Talkgoup&nbspId</th><th>Count</th></tr>";
        var ct = 0;
        for (var freq in d[nac]['frequency_data']) {
            tg1 = d[nac]['frequency_data'][freq]['tgids'][0];
            tg2 = d[nac]['frequency_data'][freq]['tgids'][1];
            if (tg1 == null)
                tg1 = "&nbsp&nbsp-&nbsp&nbsp";
            if (tg2 == null)
                tg2 = "&nbsp&nbsp-&nbsp&nbsp";
            if (tg1 == tg2) {
                tg_str = "<td style=\"text-align:center;\" colspan=2>" + tg1 + "</td>";
            }
            else {
                tg_str = "<td style=\"text-align:center;\">" + tg2 + "</td><td style=\"text-align:center;\">" + tg1 + "</td>";
            }
            var color = "#d0d0d0";
            if ((ct & 1) == 0)
                color = "#c0c0c0";
            ct += 1;
            html += "<tr style=\"background-color: " + color + ";\"><td>" + (parseInt(freq) / 1000000.0).toFixed(6) + "</td><td style=\"text-align:right;\">" + d[nac]['frequency_data'][freq]['last_activity'] + "</td>" + tg_str + "<td style=\"text-align:right;\">" + d[nac]['frequency_data'][freq]['counter'] + "</td></tr>";
        }
        html += "</table></div>";

// end system freqencies table

        html += adjacent_data(d[nac]['adjacent_data']);
    }

    if (d['srcaddr'] != undefined)
        c_srcaddr = d['srcaddr']
    if (d['grpaddr'] != undefined)
        c_grpaddr = d['grpaddr']
    if (d['encrypted'] != undefined)
        c_encrypted = d['encrypted']

    var div_s3 = document.getElementById("div_s3");
    div_s3.innerHTML = html;

    channel_status();
}

function plot(d) {
    var mode_handler = {"fft": plot_fft, "constellation": plot_constellation, "symbol": plot_symbol, "eye": plot_eye, "mixer": plot_mixer, "tuner": plot_tuner};

    if (d.mode in mode_handler) {
        mode_handler[d.mode](d);
    } else {
        console.log("No handler for mode " + d.mode);
    }
}

function get_tuned_freq(chan) {
    var chan_i = (chan < 0) ? 0 : chan;
    var freq = undefined;

    if (full_config.channels && full_config.channels.length > 0) {
        freq = full_config.channels[chan_i].frequency;
    }

    return freq;
}

function get_squelch(chan) {
    var chan_i = (chan < 0) ? 0 : chan;
    var squelch = undefined;

    if (full_config.channels && full_config.channels.length > 0) {
        squelch = full_config.channels[chan_i].nbfm_squelch_threshold;
    }

    return squelch;
}

function plot_fft(d) {
    var xArray = [];
    var yArray = [];

    for (var i = 0; i < d.data.length; i++) {
        xArray.push(d.data[i][0])
        yArray.push(d.data[i][1])
    }

    var data = [{
        type: "scatter",
        mode: "lines",
        x: xArray,
        y: yArray,
        line: {
            color: '#17BECF',
            width: 1
        }
    }];

    // TODO: Get actual frequency...
    //var center = (d.xrange[1] - d.xrange[0]) / 2 + d.xrange[0];

    var center = get_tuned_freq(d.chan);
    var squelch = get_squelch(d.chan);

    if (center == undefined) {
        center = (d.xrange[1] - d.xrange[0]) / 2 + d.xrange[0];
    } else {
        center /= 1000000; // TODO: Verify that this is between xrange values
    }

    var squelch_str = "";
    if (squelch != undefined) {
        squelch_str = ", Squelch: " + squelch + "dB";
    }

    var layout = {
        title: d.title.replace(" Spectrum:", "<br>Spectrum:") + squelch_str + "<br>" + Date().toString(),
        xaxis: {
            title: {
                text: "Frequency"
            },
            range: d.xrange,
            type: 'linear',
            dtick: 0.1
        },
        yaxis: {
            title: {
                text: "Power (dB)"
            },
            range: d.yrange,
            type: 'linear'
        },
        shapes: [{
            type: 'line',
            x0: center,
            y0: d.yrange[0],
            x1: center,
            y1: d.yrange[1],
            line: {
                color: 'grey',
                width: 1.5,
                opacity: 0.2
            }
        },
	{
            type: 'line',
            x0: d.xrange[0],
            y0: d.yrange[0],
            x1: d.xrange[0],
            y1: d.yrange[1],
            line: {
                color: 'black',
                width: 1
            }
        }, {
            type: 'line',
            x0: d.xrange[1],
            y0: d.yrange[0],
            x1: d.xrange[1],
            y1: d.yrange[1],
            line: {
                color: 'black',
                width: 1
            }
        }, {
            type: 'line',
            x0: d.xrange[0],
            y0: d.yrange[0],
            x1: d.xrange[1],
            y1: d.yrange[0],
            line: {
                color: 'black',
                width: 1
            }
        }, {
            type: 'line',
            x0: d.xrange[0],
            y0: d.yrange[1],
            x1: d.xrange[1],
            y1: d.yrange[1],
            line: {
                color: 'black',
                width: 1
            }
        }]
    };

    if (squelch != undefined) {
        layout.shapes.push({
            type: 'line',
            x0: d.xrange[0],
            y0: squelch,
            x1: d.xrange[1],
            y1: squelch,
            line: {
                color: 'red',
                width: 1.5,
                opacity: 0.2
            }
        });
    }

    var plot_div = document.getElementById('js_plot_fft');
    if (plot_div.style['display'] != 'none') {
        Plotly.react(plot_div, data, layout);
    } else {
        Plotly.newPlot(plot_div, data, layout);
    }
}

function plot_constellation(d) {
    var xArray = [];
    var yArray = [];

    for (var i = 0; i < d.data.length; i++) {
        xArray.push(d.data[i][0])
        yArray.push(d.data[i][1])
    }

    var data = [{
        type: "scatter",
        mode: "markers",
        x: xArray,
        y: yArray,
        line: {
            color: '#17BECF',
            width: 1
        }
    }];


    var layout = {
        title: d.title + "<br>" + Date().toString(),
        xaxis: {
            title: {
                text: ""
            },
            range: d.xrange,
            type: 'linear',
            dtick: 500
        },
        yaxis: {
            title: {
                text: ""
            },
            range: d.yrange,
            type: 'linear'
        },
        shapes: [{
            type: 'line',
            x0: d.xrange[0],
            y0: d.yrange[0],
            x1: d.xrange[0],
            y1: d.yrange[1],
            line: {
                color: 'black',
                width: 1
            }
        }, {
            type: 'line',
            x0: d.xrange[1],
            y0: d.yrange[0],
            x1: d.xrange[1],
            y1: d.yrange[1],
            line: {
                color: 'black',
                width: 1
            }
        }, {
            type: 'line',
            x0: d.xrange[0],
            y0: d.yrange[0],
            x1: d.xrange[1],
            y1: d.yrange[0],
            line: {
                color: 'black',
                width: 1
            }
        }, {
            type: 'line',
            x0: d.xrange[0],
            y0: d.yrange[1],
            x1: d.xrange[1],
            y1: d.yrange[1],
            line: {
                color: 'black',
                width: 1
            }
        }]
    };

    var plot_div = document.getElementById('js_plot_constellation');
    if (plot_div.style['display'] != 'none') {
        Plotly.react(plot_div, data, layout);
    } else {
        Plotly.newPlot(plot_div, data, layout);
    }

}

function plot_symbol(d) {
    var xArray = [];
    var yArray = [];

    for (var i = 0; i < d.data.length; i++) {
        xArray.push(d.data[i][0])
        yArray.push(d.data[i][1])
    }

    var data = [{
        type: "scatter",
        mode: "markers",
        x: xArray,
        y: yArray,
        line: {
            color: '#17BECF',
            width: 1
        }
    }];


    var layout = {
        title: d.title + "<br>" + Date().toString(),
        xaxis: {
            title: {
                text: ""
            },
            range: d.xrange,
            type: 'linear',
            dtick: 500
        },
        yaxis: {
            title: {
                text: ""
            },
            range: d.yrange,
            type: 'linear'
        },
        shapes: [{
            type: 'line',
            x0: d.xrange[0],
            y0: d.yrange[0],
            x1: d.xrange[0],
            y1: d.yrange[1],
            line: {
                color: 'black',
                width: 1
            }
        }, {
            type: 'line',
            x0: d.xrange[1],
            y0: d.yrange[0],
            x1: d.xrange[1],
            y1: d.yrange[1],
            line: {
                color: 'black',
                width: 1
            }
        }, {
            type: 'line',
            x0: d.xrange[0],
            y0: d.yrange[0],
            x1: d.xrange[1],
            y1: d.yrange[0],
            line: {
                color: 'black',
                width: 1
            }
        }, {
            type: 'line',
            x0: d.xrange[0],
            y0: d.yrange[1],
            x1: d.xrange[1],
            y1: d.yrange[1],
            line: {
                color: 'black',
                width: 1
            }
        }]
    };

    var plot_div = document.getElementById('js_plot_symbol');
    if (plot_div.style['display'] != 'none') {
        Plotly.react(plot_div, data, layout);
    } else {
        Plotly.newPlot(plot_div, data, layout);
    }
}

function plot_eye(d) {
    var xArray = [];
    var yArray = [];

    var lines = -1;

    for (var i = 0; i < d.data.length; i++) {
        if (d.data[i][0] == 0) {
            lines++;
            xArray[lines] = [];
            yArray[lines] = [];
        }
	xArray[lines].push(d.data[i][0] * 100)
        yArray[lines].push(d.data[i][1])
    }

    var data = [];

    for (var i = 0; i <= lines; i++) {
        data.push({
            type: "scatter",
            mode: "lines",
            x: xArray[i],
            y: yArray[i],
            line: {
                //color: '#17BECF',
                width: 1
            }
        });
    }


    var layout = {
        title: d.title + "<br>" + Date().toString(),
        xaxis: {
            title: {
                text: ""
            },
            range: d.xrange,
            type: 'linear',
            //dtick: 500
        },
        yaxis: {
            title: {
                text: ""
            },
            range: d.yrange,
            type: 'linear'
        },
        shapes: [{
            type: 'line',
            x0: d.xrange[0],
            y0: d.yrange[0],
            x1: d.xrange[0],
            y1: d.yrange[1],
            line: {
                color: 'black',
                width: 1
            }
        }, {
            type: 'line',
            x0: d.xrange[1],
            y0: d.yrange[0],
            x1: d.xrange[1],
            y1: d.yrange[1],
            line: {
                color: 'black',
                width: 1
            }
        }, {
            type: 'line',
            x0: d.xrange[0],
            y0: d.yrange[0],
            x1: d.xrange[1],
            y1: d.yrange[0],
            line: {
                color: 'black',
                width: 1
            }
        }, {
            type: 'line',
            x0: d.xrange[0],
            y0: d.yrange[1],
            x1: d.xrange[1],
            y1: d.yrange[1],
            line: {
                color: 'black',
                width: 1
            }
        }]
    };

    var plot_div = document.getElementById('js_plot_eye');
    if (plot_div.style['display'] != 'none') {
        Plotly.react(plot_div, data, layout);
    } else {
        Plotly.newPlot(plot_div, data, layout);
    }

}

function plot_mixer(d) {
    var xArray = [];
    var yArray = [];

    for (var i = 0; i < d.data.length; i++) {
        xArray.push(d.data[i][0])
        yArray.push(d.data[i][1])
    }

    var data = [{
        type: "scatter",
        mode: "lines",
        x: xArray,
        y: yArray,
        line: {
            color: '#17BECF',
            width: 1
        }
    }];


    var layout = {
        title: d.title.replace(" Mixer:","<br>Mixer:") + "<br>" + Date().toString(),
        xaxis: {
            title: {
                text: "Frequency"
            },
            range: d.xrange,
            type: 'linear',
            dtick: 5000
        },
        yaxis: {
            title: {
                text: "Power (dB)"
            },
            range: d.yrange,
            type: 'linear'
        },
        shapes: [{
            type: 'line',
            x0: d.xrange[0],
            y0: d.yrange[0],
            x1: d.xrange[0],
            y1: d.yrange[1],
            line: {
                color: 'black',
                width: 1
            }
        }, {
            type: 'line',
            x0: d.xrange[1],
            y0: d.yrange[0],
            x1: d.xrange[1],
            y1: d.yrange[1],
            line: {
                color: 'black',
                width: 1
            }
        }, {
            type: 'line',
            x0: d.xrange[0],
            y0: d.yrange[0],
            x1: d.xrange[1],
            y1: d.yrange[0],
            line: {
                color: 'black',
                width: 1
            }
        }, {
            type: 'line',
            x0: d.xrange[0],
            y0: d.yrange[1],
            x1: d.xrange[1],
            y1: d.yrange[1],
            line: {
                color: 'black',
                width: 1
            }
        }]
    };

    var plot_div = document.getElementById('js_plot_mixer');
    if (plot_div.style['display'] != 'none') {
        Plotly.react(plot_div, data, layout);
    } else {
        Plotly.newPlot(plot_div, data, layout);
    }
}

function plot_tuner(d) {
    var xArray = [];
    var yArray = [];

    for (var i = 0; i < d.data.length; i++) {
        xArray.push(d.data[i][0])
        yArray.push(d.data[i][1])
    }

    var data = [{
        type: "bar",
        //mode: "lines",
        x: xArray,
        y: yArray,
        /*line: {
            color: '#17BECF',
            width: 1
        }*/
    }];


    var layout = {
        title: d.title + "<br>" + Date().toString(),
        xaxis: {
            title: {
                text: ""
            },
            range: d.xrange,
            type: 'linear',
            dtick: 0.5
        },
        yaxis: {
            title: {
                text: ""
            },
            range: d.yrange,
            type: 'linear',
            dtick: 0.5
        },
        shapes: [{
            type: 'line',
            x0: d.xrange[0],
            y0: d.yrange[0],
            x1: d.xrange[0],
            y1: d.yrange[1],
            line: {
                color: 'black',
                width: 1
            }
        }, {
            type: 'line',
            x0: d.xrange[1],
            y0: d.yrange[0],
            x1: d.xrange[1],
            y1: d.yrange[1],
            line: {
                color: 'black',
                width: 1
            }
        }, {
            type: 'line',
            x0: d.xrange[0],
            y0: d.yrange[0],
            x1: d.xrange[1],
            y1: d.yrange[0],
            line: {
                color: 'black',
                width: 1
            }
        }, {
            type: 'line',
            x0: d.xrange[0],
            y0: d.yrange[1],
            x1: d.xrange[1],
            y1: d.yrange[1],
            line: {
                color: 'black',
                width: 1
            }
        }]
    };

    var plot_div = document.getElementById('js_plot_tuner');
    if (plot_div.style['display'] != 'none') {
        Plotly.react(plot_div, data, layout);
    } else {
        Plotly.newPlot(plot_div, data, layout);
    }
}

function http_req_cb() {
    req_cb_count += 1;
    s = http_req.readyState;
    if (s != 4) {
        nfinal_count += 1;
        return;
    }
    if (http_req.status != 200) {
        n200_count += 1;
        return;
    }
    r200_count += 1;
    var dl = JSON.parse(http_req.responseText);
    var dispatch = {
            'trunk_update': trunk_update,
            'change_freq': change_freq,
            'channel_update': channel_update,
            'rx_update': rx_update,
            'terminal_config': term_config,
            'full_config': full_config_handler,
            'plot': plot
        };
    for (var i=0; i<dl.length; i++) {
        var d = dl[i];
        if (!("json_type" in d))
            continue;
        if (!(d["json_type"] in dispatch))
            continue;
        dispatch[d["json_type"]](d);
    }
}

function do_onload() {
    var ele = document.getElementById("div_status");
    ele.style["display"] = "";
    set_tuning_step_sizes();
    //send_command("get_terminal_config", 0, 0);
    send_command("get_full_config", 0, 0);
    setInterval(do_update, 1000);
    b = document.getElementById("b1");
    b.className = "nav-button-active";
}

function do_update() {
    if (channel_list.length == 0) {
        send_command("update", 0, 0);
    }
    else {
        send_command("update", 0, Number(channel_list[channel_index]));
    }
    f_debug();
}

function send_command(command, arg1 = 0, arg2 = 0) {
    request_count += 1;
    if (send_queue.length >= SEND_QLIMIT) {
        send_qfull += 1;
        send_queue.unshift();
    }
    send_queue.push( {"command": command, "arg1": arg1, "arg2": arg2} );
    send_process();
}

function send_process() {
    s = http_req.readyState;
    if (s != 0 && s != 4) {
        send_busy += 1;
        return;
    }
    http_req.open("POST", "/");
    http_req.onreadystatechange = http_req_cb;
    http_req.setRequestHeader("Content-type", "application/json");
    cmd = JSON.stringify( send_queue );
    send_queue = [];
    http_req.send(cmd);
}

function f_chan_button(command) {
    channel_index += command;
    if (channel_index < 0) {
        channel_index = channel_list.length - 1;
    }
    else if (channel_index >= channel_list.length) {
        channel_index = 0;
    }
    // TODO: reset channel talkgroup history
    var tg_history = document.getElementById("tg_history");
    tg_history.innerHTML = "";
    tg_list = [];
}

function f_dump_button(command) {
    send_command('dump_tgids', 0, Number(channel_list[channel_index]));
    send_command('dump_tracking', 0, Number(channel_list[channel_index]));
}

function f_cap_button(command) {
    send_command('capture', 0, Number(channel_list[channel_index]));
}

function f_trk_button(command) {
    send_command('set_tracking', command, Number(channel_list[channel_index]));
}

function f_tune_button(command) {
    if (channel_list.length == 0) {
        send_command('adj_tune', command, 0);
    }
    else {
        send_command('adj_tune', command, Number(channel_list[channel_index]));
    }
}

function toggle_js_plot_display(command) {
    var plot_list = [
        "js_plot_fft",
        "js_plot_constellation",
        "js_plot_symbol",
        "js_plot_eye",
        "js_plot_mixer",
        "js_plot_tuner"
    ];

    if (terminal_config.http_plot_type == "raw" && command >= 1 && command <= 6) {
        var plot_div = document.getElementById(plot_list[command-1]);

        if (plot_div.style['display'] != 'none') {
            plot_div.style['display'] = 'none';
        } else {
            plot_div.style['display'] = 'block';
        }
    }
}

function f_plot_button(command) {
    if (channel_list.length == 0) {
        send_command('toggle_plot', command, 0);
    }
    else {
        send_command('toggle_plot', command, Number(channel_list[channel_index]));
    }
    toggle_js_plot_display(command);
}

function f_scan_button(command) {
    var _tgid = 0;
    var update_config = false;

    if (command == "goto") {
        command = "hold"
        if (current_tgid != null)
           _tgid = current_tgid;
        _tgid = parseInt(prompt("Enter tgid to hold", _tgid));
        if (isNaN(_tgid) || (_tgid < 0) || (_tgid > 65535))
            _tgid = 0;
    }
    else if ((command == "lockout") && (current_tgid == null)) {
        _tgid = parseInt(prompt("Enter tgid to blacklist", _tgid));
        if (isNaN(_tgid) || (_tgid <= 0) || (_tgid > 65534))
            return;
        update_config = true;
    }
    else if (command == "whitelist") {
        _tgid = parseInt(prompt("Enter tgid to whitelist", _tgid));
        if (isNaN(_tgid) || (_tgid <= 0) || (_tgid > 65534))
            return;
        update_config = true;
    }
    else if (command == "set_debug") {
        _tgid = parseInt(prompt("Enter logging level", _tgid));
        if (isNaN(_tgid) || (_tgid < 0) )
            return;
    }

    if (channel_list.length == 0) {
        send_command(command, _tgid);
    }
    else {
        send_command(command, _tgid, Number(channel_list[channel_index]));
    }
    if (update_config) {
        //setInterval(do_update_config, 1000);
        send_command("get_full_config", 0, 0);
    }
}

function f_debug() {
	if (!d_debug) return;
	var html = "busy " + send_busy;
	html += " qfull " + send_qfull;
	html += " sendq size " + send_queue.length;
	html += " requests " + request_count;
	html += "<br>callbacks:";
	html += " total=" + req_cb_count;
	html += " incomplete=" + nfinal_count;
	html += " error=" + n200_count;
	html += " OK=" + r200_count;
	html += "<br>";
	var div_debug = document.getElementById("div_debug");
	div_debug.innerHTML = html;
}
