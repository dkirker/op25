// P25 Decoder (C) Copyright 2013, 2014, 2015, 2016, 2017 Max H. Parke KA1RBI
//             (C) Copyright 2019, 2020, 2021, 2022 Graham J. Norbury (DMR & P25 additions)
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

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <string>
#include <iostream>
#include <deque>
#include <assert.h>
#include <errno.h>
#include <unistd.h>

#include "rx_sync.h"

#include "bit_utils.h"

#include "check_frame_sync.h"

#include "p25p2_vf.h"
#include "mbelib.h"
#include "ambe.h"
#include "rs.h"
#include "crc16.h"

#include "ysf_const.h"
#include "dmr_const.h"
#include "p25_frame.h"
#include "op25_imbe_frame.h"
#include "software_imbe_decoder.h"
#include "op25_audio.h"
#include "op25_msg_types.h"

namespace gr{
    namespace op25_repeater{

void rx_sync::cbuf_insert(const uint8_t c) {
	d_cbuf[d_cbuf_idx] = c;
	d_cbuf[d_cbuf_idx + CBUF_SIZE] = c;
	d_cbuf_idx = (d_cbuf_idx + 1) % CBUF_SIZE;
}

void rx_sync::reset_timer(void) {
	sync_timer.reset();
	p25fdma.reset_timer();
}

void rx_sync::sync_reset(void) {
	if (d_debug >= 10) {
		fprintf(stderr, "%s rx_sync::sync_reset:\n", logts.get(d_msgq_id));
	}

	// Sync counters and registers reset
	d_symbol_count = 0;
    d_cbuf_idx = 0;
	d_rx_count = 0;
	d_threshold = 0;
	d_shift_reg = 0;
	d_sync_reg = 0;
	d_fs = 0;
	d_expires = 0;
	d_current_type = RX_TYPE_NONE;
	d_fragment_len = MODE_DATA[d_current_type].fragment_len;

	// Audio reset
	for (int chan = 0; chan <= 1; chan++) {
		if (d_unmute_until[chan]) {
			d_unmute_until[chan] = 0;
			d_audio.send_audio_flag_channel(op25_audio::DRAIN, chan);
			if (d_debug >= 10) {
				fprintf(stderr, "%s mute channel(%d)\n", logts.get(d_msgq_id), chan);
			}
		}
	}

	// Timers reset
	reset_timer();
}

void rx_sync::crypt_reset(void) {
	p25fdma.crypt_reset();
	p25tdma.crypt_reset();
}

void rx_sync::crypt_key(uint16_t keyid, uint8_t algid, const std::vector<uint8_t> &key) {
	p25fdma.crypt_key(keyid, algid, key);
	p25tdma.crypt_key(keyid, algid, key);
}

void rx_sync::set_nac(int nac) {
    p25fdma.set_nac(nac);
    p25tdma.set_nac(nac);
}

void rx_sync::set_slot_mask(int mask) {
	if (mask == d_slot_mask)
		return;

	if (d_debug >= 10) {
		fprintf(stderr, "%s rx_sync::set_slot_mask: current(%d), new(%d)\n", logts.get(d_msgq_id), d_slot_mask, mask);
	}

	if (d_slot_mask == 4) {
		reset_timer();
		sync_reset();
	}
	d_slot_mask = mask;
	p25tdma.set_slotid(mask & 0x1);
}

void rx_sync::set_xormask(const char* p) {
	p25tdma.set_xormask(p);
}

void rx_sync::set_slot_key(int mask) {
	if (d_debug >= 10) {
		fprintf(stderr, "%s rx_sync::set_slot_key: current(%d), new(%d)\n", logts.get(d_msgq_id), d_slot_key, mask);
	}
	d_slot_key = mask;
}

void rx_sync::set_debug(int debug) {
    d_debug = debug;
	d_audio.set_debug(debug);
	p25fdma.set_debug(debug);
	p25tdma.set_debug(debug);
	dmr.set_debug(debug);
}

static inline void debug_dump(const char *ts, const char* s, const uint8_t p[], int l) {
	char buf[64];
	for (int i=0; i<l; i++) {
		if (i*2+3 >= sizeof(buf))
			break;
		sprintf(buf+i*2, "%02x", p[i]);
	}
	fprintf(stderr, "%s %s: %s\n", ts, s, buf);
}

static inline void cfill(uint8_t result[], const uint8_t src[], int len) {
	for (int i=0; i<len; i++)
		result[i] = load_i(src+i*8, 8);
}

static int ysf_decode_fich(const uint8_t src[100], uint8_t dest[32]) {   // input is 100 dibits, result is 32 bits
// return -1 on decode error, else 0
	static const int pc[] = {0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1};
	uint8_t buf[100];
	for (int i=0; i<20; i++) {
		for (int j=0; j<5; j++) {
			buf[j+i*5] = src[i+j*20];
		}
	}
	uint8_t dr = 0;
	uint8_t ans[100];
	/* fake trellis decode */
	/* TODO: make less fake */
	for (int i=0; i<100; i++) {
		uint8_t sym = buf[i];
		uint8_t d0  = ((dr << 1) | 0) & 0x1f;
		uint8_t r0 = (pc[ d0 & 0x19 ] << 1) + pc[ d0 & 0x17];
		uint8_t d1  = ((dr << 1) | 1) & 0x1f;
		uint8_t r1 = (pc[ d1 & 0x19 ] << 1) + pc[ d1 & 0x17];
		if (sym == r0) {
			ans[i] = 0;
			dr = d0;
		} else if (sym == r1) {
			ans[i] = 1;
			dr = d1;
		} else {
			return -1;  /* decode error */
		}
	}
	uint8_t fich_bits[12*4];
	store_i(gly24128Dec(load_i(ans+24*0, 24)), fich_bits+12*0, 12);
	store_i(gly24128Dec(load_i(ans+24*1, 24)), fich_bits+12*1, 12);
	store_i(gly24128Dec(load_i(ans+24*2, 24)), fich_bits+12*2, 12);
	store_i(gly24128Dec(load_i(ans+24*3, 24)), fich_bits+12*3, 12);
	uint16_t crc_result = crc16(fich_bits, 48);
	if (crc_result != 0)
		return -1;	// crc failure
	memcpy(dest, fich_bits, 32);
	return 0;
}

void rx_sync::ysf_sync(const uint8_t dibitbuf[], bool& ysf_fullrate, bool& unmute) {
	uint8_t fich_buf[32];
	int rc = ysf_decode_fich(dibitbuf+20, fich_buf);
	if (rc == 0) {
		uint32_t fich = load_i(fich_buf, 32);
		uint32_t dt = (fich >> 8) & 3;
		d_shift_reg = dt;
	}
	switch(d_shift_reg) {
	case 0:		// voice/data mode 1
		unmute = false;
		break;
	case 1:		// data mode
		unmute = false;
		break;
	case 2:		// voice/data mode 2
		unmute = true;
		ysf_fullrate = false;
		break;
	case 3:		// voice fr mode
		unmute = true;
		ysf_fullrate = true;
		break;
	}
	if (d_debug > 5 && !unmute)
		fprintf(stderr, "%s ysf_sync: muting audio: dt: %d, rc: %d\n", logts.get(d_msgq_id), d_shift_reg, rc);
}

rx_sync::rx_sync(const char * options, log_ts& logger, int debug, int msgq_id, gr::msg_queue::sptr queue) :	// constructor
	sync_timer(op25_timer(1000000)),
	d_symbol_count(0),
	d_sync_reg(0),
	d_fs(0),
	d_cbuf_idx(0),
	d_current_type(RX_TYPE_NONE),
	d_rx_count(0),
	d_expires(0),
	d_slot_mask(3),
	d_slot_key(0),
	p25fdma(d_audio, logger, debug, true, false, true, queue, d_output_queue[0], true, msgq_id),
	p25tdma(d_audio, logger, 0, debug, true, queue, d_output_queue[0], true, msgq_id),
	dmr(logger, debug, msgq_id, queue),
	d_msgq_id(msgq_id),
	d_msg_queue(queue),
	d_previous_nxdn_sync(0),
	d_previous_nxdn_sr_structure(-1),
	d_previous_nxdn_sr_ran(-1),
	d_stereo(true),
	d_debug(debug),
	d_audio(options, debug),
    logts(logger)
{
	if (msgq_id >= 0)
		d_stereo = false; // single channel audio for trunking

	mbe_initMbeParms (&cur_mp[0], &prev_mp[0], &enh_mp[0]);
	mbe_initMbeParms (&cur_mp[1], &prev_mp[1], &enh_mp[1]);
	mbe_initErrParms (&errs_mp[0]);
	mbe_initErrParms (&errs_mp[1]);
	mbe_initToneParms (&tone_mp[0]);
	mbe_initToneParms (&tone_mp[1]);
	mbe_err_cnt[0] = 0;
	mbe_err_cnt[1] = 0;
	sync_reset();
}

rx_sync::~rx_sync()	// destructor
{
}

void rx_sync::sync_timeout(rx_types proto)
{
	if (d_debug >= 10) {
		fprintf(stderr, "%s rx_sync::sync_timeout: protocol %s\n", logts.get(d_msgq_id), MODE_DATA[proto].type);
	}
	if ((d_msgq_id >= 0) && (!d_msg_queue->full_p())) {
		std::string m_buf;
		gr::message::sptr msg;
		switch(proto) {
		case RX_TYPE_NONE:
		case RX_TYPE_P25P1:
		case RX_TYPE_P25P2:
			msg = gr::message::make_from_string(m_buf, get_msg_type(PROTOCOL_P25, M_P25_TIMEOUT), (d_msgq_id << 1), logts.get_ts());
			d_msg_queue->insert_tail(msg);
			break;
		case RX_TYPE_DMR:
			msg = gr::message::make_from_string(m_buf, get_msg_type(PROTOCOL_DMR, M_DMR_TIMEOUT), (d_msgq_id << 1), logts.get_ts());
			d_msg_queue->insert_tail(msg);
			break;
		default:
			break;
		}
    }
	reset_timer();
}

void rx_sync::sync_established(rx_types proto)
{
	if (d_debug >= 10) {
		fprintf(stderr, "%s rx_sync::sync_established: protocol %s\n", logts.get(d_msgq_id), MODE_DATA[proto].type);
	}
	if ((d_msgq_id >= 0) && (!d_msg_queue->full_p())) {
		std::string m_buf;
		gr::message::sptr msg;
		switch(proto) {
		case RX_TYPE_NONE:
            break;
		case RX_TYPE_P25P1:
		case RX_TYPE_P25P2:
			msg = gr::message::make_from_string(m_buf, get_msg_type(PROTOCOL_P25, M_P25_SYNC_ESTAB), (d_msgq_id << 1), logts.get_ts());
			d_msg_queue->insert_tail(msg);
			break;
		case RX_TYPE_DMR:
			break;
		default:
			break;
        }
    }
}

void rx_sync::codeword(const uint8_t* cw, const enum codeword_types codeword_type, int slot_id) {
	static const int x=4;
	static const int y=26;
	static const uint8_t majority[8] = {0,0,0,1,0,1,1,1};

	int b[9];
	int U[4];
	uint8_t buf[4*26];
	uint8_t tmp_codeword [144];
	uint32_t E0, ET;
	uint32_t u[8];
	size_t errs = 0;
    int rc = 0;
	bool do_fullrate = false;
	bool do_silence = false;
	bool do_tone = false;
	packed_codeword p_cw;
	voice_codeword fullrate_cw(voice_codeword_sz);

	switch(codeword_type) {
	case CODEWORD_DMR:
		errs = interleaver.process_vcw(&errs_mp[slot_id], cw, b, U);
		interleaver.pack_cw(p_cw, U);
		if (d_debug >= 9) {
			fprintf(stderr, "%s AMBE %02x %02x %02x %02x %02x %02x %02x errs %lu err_rate %f\n", logts.get(d_msgq_id),
			       	p_cw[0], p_cw[1], p_cw[2], p_cw[3], p_cw[4], p_cw[5], p_cw[6], errs, errs_mp[slot_id].ER);
		}
		if (d_slot_key) { // BP reversal if key is specified
			uint8_t skipped_bits = p_cw[1] & 0xf0;
			for (int i = 0; i <= 6; i++)
				p_cw[i]   ^= (d_slot_key >> ((i + 1) % 2) * 8);
			p_cw[1] = (p_cw[1] & 0x0f) + skipped_bits;
			interleaver.unpack_cw(p_cw, U);
			interleaver.unpack_b(b, U);
			interleaver.pack_cw(p_cw, U);

			if (d_debug >= 9) {
				fprintf(stderr, "%s ambe^%02x^%02x^%02x^%02x^%02x^%02x^%02x\n", logts.get(d_msgq_id),
			       		p_cw[0], p_cw[1], p_cw[2], p_cw[3], p_cw[4], p_cw[5], p_cw[6]);
			}
		}

		// handle frame repeats, tones and voice
		rc = mbe_dequantizeAmbeTone(&tone_mp[slot_id], &errs_mp[slot_id], U);
		if (rc >= 0) {					// Tone Frame
			if (rc == 0) {                  // Valid Tone
				do_tone = true;
				mbe_err_cnt[slot_id] = 0;
			} else {                        // Tone Erasure with Frame Repeat
				if ((++mbe_err_cnt[slot_id] < 4) && do_tone) {
					mbe_useLastMbeParms(&cur_mp[slot_id], &prev_mp[slot_id]);
					rc = 0;
				} else {
					do_tone = false;        // Mute audio output after 3 successive Frame Repeats
					do_silence = true;
				}
 			}
		} else {
			rc = mbe_dequantizeAmbe2250Parms (&cur_mp[slot_id], &prev_mp[slot_id], &errs_mp[slot_id], b);
			if (rc == 0) {				// Voice Frame
				do_tone = false;
				mbe_err_cnt[slot_id] = 0;
			} else if ((++mbe_err_cnt[slot_id] < 4) && !do_tone) {// Erasure with Frame Repeat per TIA-102.BABA.5.6
				mbe_useLastMbeParms(&cur_mp[slot_id], &prev_mp[slot_id]);
				rc = 0;
			} else {
				do_tone = false;            // Mute audio output after 3 successive Frame Repeats
				do_silence = true;
			}
		}
		if (errs_mp[slot_id].ER > 0.096) { // Mute if error rate exceeds threshold
			do_tone = false;
			do_silence = true;
		}
		break;
	case CODEWORD_NXDN_EHR:		// halfrate
		interleaver.process_vcw(&errs_mp[slot_id], cw, b, U);
		if (b[0] < 120)
			mbe_dequantizeAmbe2250Parms(&cur_mp[slot_id], &prev_mp[slot_id], &errs_mp[slot_id], b);
		break;
	case CODEWORD_DSTAR:
		interleaver.decode_dstar(cw, b, false);
		if (b[0] < 120) // TODO: frame repeats and tones
			mbe_dequantizeAmbe2400Parms(&cur_mp[slot_id], &prev_mp[slot_id], &errs_mp[slot_id], b);
		else
			do_silence = true;
		break;
	case CODEWORD_YSF_HALFRATE:	// 104 bits
		for (int i=0; i<x; i++) {
			for (int j=0; j<y; j++) 
				buf[j+i*y] = cw[i+j*x];
		}
		ysf_scramble(buf, 104);
		for (int i=0; i<27; i++)
			tmp_codeword[i] = majority[ (buf[0+i*3] << 2) | (buf[1+i*3] << 1) | buf[2+i*3] ];

		memcpy(tmp_codeword+27, buf+81, 22);
		decode_49bit(b, tmp_codeword);
		if (b[0] < 120) // TODO: frame repeats and tones
			mbe_dequantizeAmbe2250Parms(&cur_mp[slot_id], &prev_mp[slot_id], &errs_mp[slot_id], b);
		else
			do_silence = true;
		break;
	case CODEWORD_P25P2:
		break; // Not used; handled by p25p2_tdma
	case CODEWORD_P25P1:
		break; // Not used; handled by p25p1_fdma
	case CODEWORD_YSF_FULLRATE:	// 144 bits
		for (int i=0; i<144; i++)
			fullrate_cw[i] = cw[ysf_permutation[i]];
		imbe_header_decode(fullrate_cw, u[0], u[1], u[2], u[3], u[4], u[5], u[6], u[7], E0, ET);
		do_fullrate = true;
		break;
	}
	if (do_tone) {
		d_software_decoder[slot_id].decode_tone(tone_mp[slot_id].ID, tone_mp[slot_id].AD, &tone_mp[slot_id].n);
	} else {
		mbe_moveMbeParms (&cur_mp[slot_id], &prev_mp[slot_id]);
		if (do_fullrate) {
			d_software_decoder[slot_id].decode(fullrate_cw);
		} else {	/* halfrate */
			if (!do_silence) {
				d_software_decoder[slot_id].decode_tap(cur_mp[slot_id].L, 0, cur_mp[slot_id].w0, &cur_mp[slot_id].Vl[1], &cur_mp[slot_id].Ml[1]);
			}
		}
	}
	audio_samples *samples = d_software_decoder[slot_id].audio();
	float snd;
	int16_t samp_buf[NSAMP_OUTPUT];
	for (int i=0; i < NSAMP_OUTPUT; i++) {
		if ((!do_silence) && samples->size() > 0) {
			snd = samples->front();
			samples->pop_front();
		} else {
			snd = 0;
		}
		if (do_fullrate)
			snd *= 32768.0;
		samp_buf[i] = snd;
	}
	output(samp_buf, slot_id);
}

void rx_sync::output(int16_t * samp_buf, const ssize_t slot_id) {
	if (d_stereo) 
		d_audio.send_audio_channel(samp_buf, NSAMP_OUTPUT * sizeof(int16_t), slot_id);
	else
		d_audio.send_audio(samp_buf, NSAMP_OUTPUT * sizeof(int16_t));
}

bool rx_sync::nxdn_gate(enum rx_types sync_detected) {
	// if nxdn sync is detected while another type is already active, 
	// we require two consecutive nxdn frames before allowing change to new type
	// (to try to prevent falsing due to shortened nxdn sync signature size)
	// returns false if sync is either not present or should be ignored
	static const int NXDN_FRSIZE = 192;
	bool rc;
	if (sync_detected == RX_TYPE_NONE)
		return false;
	if (sync_detected == d_current_type)
		return true;
	if (sync_detected != RX_TYPE_NXDN)
		return true;
	if (d_current_type == RX_TYPE_NONE)
		return true;
	// trying to switch from another type to nxdn
	if (d_symbol_count - d_previous_nxdn_sync != NXDN_FRSIZE) {
		if (d_debug)
			fprintf(stderr, "%s ignoring NXDN frame sync in state %s, count %d, symbol %d\n", logts.get(d_msgq_id), MODE_DATA[d_current_type].type, d_symbol_count - d_previous_nxdn_sync, d_symbol_count);
		rc = false;
	} else {
		if (d_debug)
			fprintf(stderr, "%s changing to NXDN from state %s, symbol %d\n", logts.get(d_msgq_id), MODE_DATA[d_current_type].type, d_symbol_count);
		rc = true;
	}
	d_previous_nxdn_sync = d_symbol_count;
	return rc;
}

void rx_sync::rx_sym(const uint8_t sym)
{
	uint8_t bitbuf[864*2];
	enum rx_types sync_detected = RX_TYPE_NONE;
	bool unmute;
	uint8_t tmpcw[144];
	bool ysf_fullrate;
	int excess_count = 0;

    if (d_slot_mask & 0x4) { // Setting bit 3 of slot mask disables framing for idle receiver 
        return;
    }

	d_symbol_count ++;
	d_sync_reg = (d_sync_reg << 2) | (sym & 3);
	for (int i = 0; i < KNOWN_MAGICS; i++) {
		if (check_frame_sync(SYNC_MAGIC[i].magic ^ d_sync_reg, (SYNC_MAGIC[i].type == d_current_type) ? d_threshold : 0, MODE_DATA[SYNC_MAGIC[i].type].sync_len)) {
			sync_detected = (enum rx_types) SYNC_MAGIC[i].type;
            d_fs = SYNC_MAGIC[i].magic;
			break;
		}
	}
	cbuf_insert(sym);
	if (d_current_type == RX_TYPE_NONE && sync_detected == RX_TYPE_NONE) {
		if (sync_timer.expired()) {
			sync_timeout(RX_TYPE_NONE);
		}
		return;
        }
	d_rx_count ++;
	if (sync_detected != RX_TYPE_NONE) {
		if (d_current_type != sync_detected) {
			d_current_type = sync_detected;
			d_expires = d_symbol_count + MODE_DATA[d_current_type].expiration;
			d_rx_count = MODE_DATA[d_current_type].sync_offset + (MODE_DATA[d_current_type].sync_len >> 1);
			d_fragment_len = MODE_DATA[d_current_type].fragment_len;
            sync_established(d_current_type);
		}
		if ((d_fragment_len != MODE_DATA[d_current_type].fragment_len) && (d_rx_count < d_fragment_len)) { // P25 variable length frames
			excess_count = MODE_DATA[d_current_type].sync_offset + (MODE_DATA[d_current_type].sync_len >> 1);
			d_fragment_len = d_rx_count - excess_count;
		}
		else if (d_rx_count != MODE_DATA[d_current_type].sync_offset + (MODE_DATA[d_current_type].sync_len >> 1)) {
			if (d_debug >= 10) {
				fprintf(stderr, "%s resync at count %d for protocol %s (expected count %d)\n", logts.get(d_msgq_id), d_rx_count, MODE_DATA[d_current_type].type, (MODE_DATA[d_current_type].sync_offset + (MODE_DATA[d_current_type].sync_len >> 1)));
            }
			sync_reset();
			d_rx_count = MODE_DATA[d_current_type].sync_offset + (MODE_DATA[d_current_type].sync_len >> 1);
		} else {
			d_threshold = std::min(d_threshold + 1, 2);
		}
		d_expires = d_symbol_count + MODE_DATA[d_current_type].expiration;
	}
	if ((d_current_type != RX_TYPE_NONE) && (d_symbol_count >= d_expires)) {
		if (d_debug >= 10) {
			fprintf(stderr, "%s %s: sync expiry, symbol %d\n", logts.get(d_msgq_id), MODE_DATA[d_current_type].type, d_symbol_count);
        }
        sync_reset();
		return;
	}
	if (d_rx_count < d_fragment_len)
		return;

	d_rx_count = excess_count;	// excess symbols may be carried forward to next frame
	int start_idx = d_cbuf_idx + CBUF_SIZE - d_fragment_len - excess_count;
	assert (start_idx >= 0);
	uint8_t * symbol_ptr = d_cbuf+start_idx;
	uint8_t * bit_ptr = symbol_ptr;
	if ((d_current_type == RX_TYPE_DSTAR) || (d_current_type==RX_TYPE_YSF)) {
		dibits_to_bits(bitbuf, symbol_ptr, d_fragment_len);
		bit_ptr = bitbuf;
	}
	switch (d_current_type) {
	case RX_TYPE_NONE:
		break;
	case RX_TYPE_P25P1:
        if (d_fragment_len == MODE_DATA[d_current_type].fragment_len) {
		    int frame_len = p25fdma.load_nid(symbol_ptr, MODE_DATA[d_current_type].fragment_len, d_fs);
            if (frame_len > 0) {
                d_fragment_len = frame_len;                             // expected length of remainder of this frame
            } else {
                sync_reset();
            }
        } else {
		    p25fdma.load_body(symbol_ptr, d_fragment_len);
            d_fragment_len = MODE_DATA[d_current_type].fragment_len;    // accumulate next NID
        }
		break;
	case RX_TYPE_P25P2:
		p25tdma.handle_packet(symbol_ptr, d_fs); // passing 180 dibit packets is faster than bit-shuffling via p25tdma::rx_sym()
        p25fdma.reset_timer();                   // reset FDMA timer in case of long TDMA transmissions
		break;
	case RX_TYPE_DMR:
		// frame with explicit sync resets expiration counter
		if (dmr.load_frame(symbol_ptr, unmute))
			d_expires = d_symbol_count + MODE_DATA[d_current_type].expiration;

		// update audio timeout counters etc
		if (unmute && ((dmr.chan() + 1) & d_slot_mask)) {
			if (!d_unmute_until[dmr.chan()])
				if (d_debug >= 10) {
					fprintf(stderr, "%s unmute channel(%d)\n", logts.get(d_msgq_id), dmr.chan());
				}
			d_unmute_until[dmr.chan()] = d_symbol_count + MODE_DATA[d_current_type].expiration;
		}
		if (!unmute || (d_symbol_count >= d_unmute_until[dmr.chan()])) {
			if (d_unmute_until[dmr.chan()]) {
				d_unmute_until[dmr.chan()] = 0;
				d_audio.send_audio_flag_channel(op25_audio::DRAIN, dmr.chan());
				if (d_debug >= 10) {
					fprintf(stderr, "%s mute channel(%d)\n", logts.get(d_msgq_id), dmr.chan());
				}
			}
			break;
		}

		codeword(symbol_ptr+12, CODEWORD_DMR, dmr.chan());
		memcpy(tmpcw, symbol_ptr+48, 18);
		memcpy(tmpcw+18, symbol_ptr+90, 18);
		codeword(tmpcw, CODEWORD_DMR, dmr.chan());
		codeword(symbol_ptr+108, CODEWORD_DMR, dmr.chan());
		break;
	case RX_TYPE_DSTAR:
		codeword(bit_ptr, CODEWORD_DSTAR, 0);   // 72 bits = 72 symbols
		break;
	case RX_TYPE_YSF:
		ysf_sync(symbol_ptr, ysf_fullrate, unmute);
		if (!unmute)
			break;
		for (int vcw = 0; vcw < 5; vcw++) {
			if (ysf_fullrate) {
				codeword(bit_ptr + 2*(vcw*72 + 120), CODEWORD_YSF_FULLRATE, 0);  // 144 bits
			} else {	/* halfrate */
				codeword(bit_ptr + 2*(vcw*72 + 120 + 20), CODEWORD_YSF_HALFRATE, 0);   // 104 bits
			}
		}
		break;
	case RX_TYPE_NXDN:
		nxdn_frame(symbol_ptr);
		break;
	case RX_N_TYPES:
		assert(0==1);     /* should not occur */
		break;
	}
}

static inline void qmsg(const gr::msg_queue::sptr msg_queue, const uint8_t s[], int len, int msgq_id) {
	unsigned char hdr[4] = {0xaa, 0x55, (unsigned char)((msgq_id >> 8) & 0xff), (unsigned char)(msgq_id & 0xff)};
	if (!msg_queue->full_p()) {
		gr::message::sptr msg = gr::message::make_from_string(std::string((char*)hdr, 4) + std::string((char*)s, len), -5, 0, 0);
		msg_queue->insert_tail(msg);
	}
}

void rx_sync::nxdn_frame(const uint8_t symbol_ptr[])
{	// length is implicitly 192, with frame sync in first 10 dibits
	uint8_t dbuf[182];
	uint8_t lich;
	int answer_len=0;
	uint8_t answer[32];
	uint8_t sacch_answer[32];
	uint8_t lich_buf[8];
	int lich_parity_received;
	int lich_parity_computed;
	int voice=0;
	int facch=0;
	int facch2=0;
	int sacch=0;
	int cac=0;
	int sr_structure;
	int sr_ran;

	memcpy(lich_buf, symbol_ptr+10, sizeof(lich_buf));
	nxdn_descramble(lich_buf, sizeof(lich_buf));
	lich = 0;
	for (int i=0; i<8; i++)
		lich |= (lich_buf[i] >> 1) << (7-i);
	lich_parity_received = lich & 1;
	lich_parity_computed = ((lich >> 7) + (lich >> 6) + (lich >> 5) + (lich >> 4)) & 1;
	lich = lich >> 1;
	if (lich_parity_received != lich_parity_computed) {
		if (d_debug)
			fprintf(stderr, "%s NXDN lich parity error, ignoring frame at symbol %d\n", logts.get(d_msgq_id), d_symbol_count);
		return;
	}
	voice = 0;
	facch = 0;
	facch2 = 0;
	sacch = 0;
	cac = 0;
	switch(lich) {
	case 0x01:	// CAC type
	case 0x05:
		cac = 1;
		break;
	case 0x28:
	case 0x29:
	case 0x2e:
	case 0x2f:
	case 0x48:
	case 0x49:
	case 0x4e:
	case 0x4f:
	case 0x69:
	case 0x6f:
		facch2 = 1;
		break;
	case 0x32:
	case 0x33:
	case 0x52:
	case 0x53:
	case 0x73:
		voice = 2;	// second half is voice
		facch = 1;
		sacch = 1;
		break;
	case 0x34:
	case 0x35:
	case 0x54:
	case 0x55:
	case 0x75:
		voice = 1;	// first half is voice
		facch = 2;
		sacch = 1;
		break;
	case 0x36:
	case 0x37:
	case 0x56:
	case 0x57:
	case 0x77:
		voice = 3;	// voice in both first and last
		facch = 0;
		sacch = 1;
		break;
	case 0x20:
	case 0x21:
	case 0x30:
	case 0x31:
	case 0x40:
	case 0x41:
	case 0x50:
	case 0x51:
	case 0x61:
	case 0x71:
		voice = 0;
		facch = 3;	// facch in both 
		sacch = 1;
		break;
	case 0x38:
	case 0x39:
		sacch = 1;
		break;
	default:
		if (d_debug)
			fprintf(stderr, "%s unsupported NXDN lich type 0x%x, symbol %d\n", logts.get(d_msgq_id), lich, d_symbol_count);
		voice = 0;
		break;
	} // end of switch(lich)
	if (d_debug > 3)
		fprintf(stderr, "%s nxdn lich %x voice %d facch %d sacch %d cac %d symbol %d\n", logts.get(d_msgq_id), lich, voice, facch, sacch, cac, d_symbol_count);
	if (voice || facch || facch2 || sacch || cac) {
		memcpy(dbuf, symbol_ptr+10, sizeof(dbuf));
		nxdn_descramble(dbuf, sizeof(dbuf));
	}
	if (voice & 1)
		for (int vcw = 0; vcw < 2; vcw++)
			codeword(dbuf+38+36*vcw, CODEWORD_NXDN_EHR, 0);
	if (voice & 2)
		for (int vcw = 2; vcw < 4; vcw++)
			codeword(dbuf+38+36*vcw, CODEWORD_NXDN_EHR, 0);
	if (sacch) {
		bool non_superframe = (lich == 0x20 || lich == 0x21 || lich == 0x61 || lich == 0x40 || lich == 0x41) ? true : false;
		answer_len = sizeof(sacch_answer);
		nxdn_decode_sacch(dbuf+8, 30, sacch_answer, answer_len);  // sacch size = 30 dibits, 26 bits returned if successful
		sr_structure = load_i(sacch_answer, 2) & 3;
		if (answer_len > 0 && non_superframe == true && sr_structure == 0) {
			answer[0] = 's';
			answer[1] = lich;
			int nbytes = (answer_len + 7) / 8;
			cfill(answer+2, sacch_answer, nbytes);
			qmsg(d_msg_queue, answer, nbytes+2, d_msgq_id);
			if (d_debug > 2)
				debug_dump(logts.get(d_msgq_id), "nxdn: sacch", answer, nbytes+2);
		} else if (answer_len > 0 && non_superframe == false) {
			sr_ran = load_i(sacch_answer+2, 6) & 0x3f;
			bool ok = true;
			if (d_previous_nxdn_sr_structure == -1 && sr_structure != 3)
				ok = false;
			else if (sr_structure < 3 && sr_structure+1 != d_previous_nxdn_sr_structure)
				ok = false;
			else if (sr_structure < 3 && d_previous_nxdn_sr_ran != sr_ran)
				ok = false;
			if (ok) {
				int seg = 3 - sr_structure;
				memcpy(d_sacch_buf + 18*seg, sacch_answer + 8, 18);
				if (sr_structure > 0) {
					d_previous_nxdn_sr_ran = sr_ran;
					d_previous_nxdn_sr_structure = sr_structure;
				} else {
					answer[0] = 'S';
					answer[1] = lich;
					answer[2] = sr_ran;
					int nbytes = 9;
					cfill(answer+3, d_sacch_buf, nbytes);
					qmsg(d_msg_queue, answer, nbytes+3, d_msgq_id);
					if (d_debug > 2)
						debug_dump(logts.get(d_msgq_id), "nxdn: sacch", answer, nbytes+3);
					d_previous_nxdn_sr_ran = -1;
					d_previous_nxdn_sr_structure = -1;
				}
			} else {
				d_previous_nxdn_sr_ran = -1;
				d_previous_nxdn_sr_structure = -1;
			}
		}
	}
	if (facch & 1) {
		answer_len = sizeof(answer)-2;
		nxdn_decode_facch(dbuf+38,    72, answer+2, answer_len);	// facch size = 72 dibits
		if (answer_len > 0) {
			answer[0] = 'f';
			answer[1] = lich;
			qmsg(d_msg_queue, answer, answer_len+2, d_msgq_id);
			if (d_debug > 2)
				debug_dump(logts.get(d_msgq_id), "nxdn: facch", answer, answer_len+2);
		}
	}
	if (facch & 2) {
		if ((facch & 1) && !memcmp(dbuf+38, dbuf+38+72, 72)) {
			if (d_debug > 5)
				fprintf(stderr, "%s nxdn: skipping duplicate facch\n", logts.get(d_msgq_id));
		} else {
			answer_len = sizeof(answer)-2;
			nxdn_decode_facch(dbuf+38+72, 72, answer+2, answer_len);
			if (answer_len > 0) {
				answer[0] = 'f';
				answer[1] = lich;
				qmsg(d_msg_queue, answer, answer_len+2, d_msgq_id);
				if (d_debug > 2)
					debug_dump(logts.get(d_msgq_id), "nxdn: facch", answer, answer_len+2);
			}
		}
	}
	if (facch2) {
		answer_len = sizeof(answer)-2;
		nxdn_decode_facch2_udch(dbuf+8, 174, answer+2, answer_len);
		if (answer_len > 0) {
			answer[0] = 'u';
			answer[1] = lich;
			qmsg(d_msg_queue, answer, answer_len+2, d_msgq_id);
			if (d_debug > 2)
				debug_dump(logts.get(d_msgq_id), "nxdn: facch2", answer, answer_len+2);
		}
	}
	if (cac) {
		answer_len = sizeof(answer)-2;
		nxdn_decode_cac(dbuf+8, 150, answer+2, answer_len);
		if (answer_len > 0) {
			answer[0] = 'c';
			answer[1] = lich;
			qmsg(d_msg_queue, answer, answer_len+2, d_msgq_id);
			if (d_debug > 2)
				debug_dump(logts.get(d_msgq_id), "nxdn: cac", answer, answer_len+2);
		}
	}
}

    } // end namespace op25_repeater
} // end namespace gr
