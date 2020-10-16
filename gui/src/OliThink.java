/* OliThink5 Java(c) Oliver Brausch 16.Oct.2020, ob112@web.de, http://brausch.org */
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.StringTokenizer;
import java.util.concurrent.ConcurrentLinkedDeque;

public class OliThink {
	static final String VER = "5.8.7 Java";
	static final Class<?> otclass = OliThink.class;

	static final int PAWN = 1, KNIGHT = 2, KING = 3, ENP = 4, BISHOP = 5, ROOK = 6, QUEEN = 7;
	static final int LOWER = 0, EXACT = 1, UPPER = 2;
	static final int NO_MOVE = 0, ANY_MOVE =1, GOOD_MOVE = 2;
	static final int NOPE = 0, HASH = 1, NOISY = 2, QUIET = 3, EXIT = 4;

	static final int CNODES = 0x3FFF;
	static final int pval[] = {0, 100, 290, 0, 100, 310, 500, 980};
	static final int fval[] = {0, 0, 2, 0, 0, 3, 5, 9};
	static final int pawnrun[] = {0, 0, 1, 8, 16, 32, 64, 128};
	static final int MAXSCORE = 16384;

	static int FROM(int x) { return ((x) & 63); }
	static int TO(int x) { return (((x) >> 6) & 63); }
	static int ONMV(int x) { return (((x) >> 12) & 1); }
	static int PROM(int x) { return (((x) >> 13) & 7); }
	static int PIECE(int x) { return (((x) >> 16) & 7); }
	static int CAP(int x) { return (((x) >> 19) & 7); }

	static int _TO(int x) { return ((x) << 6); }
	static int _ONMV(int x) { return ((x) << 12); }
	static int _PROM(int x) { return ((x) << 13); }
	static int _PIECE(int x) { return ((x) << 16); }
	static int _CAP(int x) { return ((x) << 19); }
	static int PREMOVE(int f, int p, int c) { return ((f) | _ONMV(c) | _PIECE(p)); }

	static long RATT1(int f) { return rays[((f) << 7) | key000(BOARD(), f)]; }
	static long RATT2(int f) { return rays[((f) << 7) | key090(BOARD(), f) | 0x2000]; }
	static long BATT3(int f) { return rays[((f) << 7) | key045(BOARD(), f) | 0x4000]; }
	static long BATT4(int f) { return rays[((f) << 7) | key135(BOARD(), f) | 0x6000]; }
	static long RXRAY1(int f) { return rays[((f) << 7) | key000(BOARD(), f) | 0x8000]; }
	static long RXRAY2(int f) { return rays[((f) << 7) | key090(BOARD(), f) | 0xA000]; }
	static long BXRAY3(int f) { return rays[((f) << 7) | key045(BOARD(), f) | 0xC000]; }
	static long BXRAY4(int f) { return rays[((f) << 7) | key135(BOARD(), f) | 0xE000]; }

	static long ROCC1(int f) { return (RATT1(f) & BOARD()); }
	static long ROCC2(int f) { return (RATT2(f) & BOARD()); }
	static long BOCC3(int f) { return (BATT3(f) & BOARD()); }
	static long BOCC4(int f) { return (BATT4(f) & BOARD()); }
	static long RMOVE1(int f) { return (RATT1(f) & (~BOARD())); }
	static long RMOVE2(int f) { return (RATT2(f) & (~BOARD())); }
	static long BMOVE3(int f) { return (BATT3(f) & (~BOARD())); }
	static long BMOVE4(int f) { return (BATT4(f) & (~BOARD())); }
	static long RCAP1(int f, int c) { return (RATT1(f) & colorb[(c)^1]); }
	static long RCAP2(int f, int c) { return (RATT2(f) & colorb[(c)^1]); }
	static long BCAP3(int f, int c) { return (BATT3(f) & colorb[(c)^1]); }
	static long BCAP4(int f, int c) { return (BATT4(f) & colorb[(c)^1]); }
	static long ROCC(int f) { return (ROCC1(f) | ROCC2(f)); }
	static long BOCC(int f) { return (BOCC3(f) | BOCC4(f)); }
	static long RMOVE(int f) { return (RMOVE1(f) | RMOVE2(f)); }
	static long BMOVE(int f) { return (BMOVE3(f) | BMOVE4(f)); }
	static long RCAP(int f, int c) { return (ROCC(f) & colorb[(c)^1]); }
	static long BCAP(int f, int c) { return (BOCC(f) & colorb[(c)^1]); }

	static long SHORTMOVE(long x) { return ((x) & ((x)^BOARD())); }
	static long SHORTCAP(long x, int c) { return ((x) & colorb[(c)^1]); }

	static long NMOVE(int x) { return (SHORTMOVE(nmoves[x])); }
	static long KMOVE(int x) { return (SHORTMOVE(kmoves[x])); }
	static long PMOVE(int x, int c) { return (pmoves[(c)][(x)] & (~BOARD())); }
	static long POCC(int x, int c) { return (pcaps[(c)][(x)] & BOARD()); }
	static long NCAP(int x, int c) { return (SHORTCAP(nmoves[x], (c))); }
	static long KCAP(int x, int c) { return (SHORTCAP(kmoves[x], (c))); }
	static long PCAP(int x, int c) { return (pcaps[(c)][(x)] & colorb[(c)^1]); }
	static long PCA3(int x, int c) {
		return (pcaps[(c)][(x) | 64] & (colorb[(c)^1] | (BIT[ENPASS()] & (c == 1 ? 0xFF0000L : 0xFF0000000000L)))); }
	static long PCA4(int x, int c) {
		return (pcaps[(c)][(x) | 128] & (colorb[(c)^1] | (BIT[ENPASS()] & (c == 1? 0xFF0000L : 0xFF0000000000L)))); }

	static boolean RANK(int x, int y) { return (((x) & 0x38) == (y)); }
	static boolean TEST(int f, long b) { return (BIT[f] & (b)) != 0; }
	static int ENPASS() { return (flags & 63); }
	static int CASTLE() { return (flags & 960); }
	static int COUNT() { return (count & 0x3FF); }
	static int MEVAL(int w) {
		return w > MAXSCORE-500 ? (200000+MAXSCORE+1-w)/2 : (w < 500-MAXSCORE ? (-200000-MAXSCORE-w)/2 : w); }

	static boolean NOMATEMAT(int c) {
		return (sf[c] <= 4 || (sf[c] <= 8 && sf[c] <= sf[c^1] + 3)) && (pieceb[PAWN] & colorb[c]) == 0;
	}

	static final int HSIZE = 0x800000;
	static final int HMASK = HSIZE - 1;

	static class Entry {
		long key;
		int move;
		short value;
		char depth;
		char type;
		short valstat;
		void set(long key, int move, short value, char depth, char type, short valstat) {
			this.key = key; this.move = move; this.value = value;
			this.depth = depth; this.type = type; this.valstat = valstat;
		}
	}

	static class Movep {
		int n = 0;
		int list[] = new int[128];
		int nquiet;
		int quiets[] = new int[128];
		static Movep[] movep = new Movep[256];
		static Movep get(int p) {
			if (movep[p] == null) movep[p] = new Movep();
			return movep[p];
		}
	}

	static final Entry[] hashDB = new Entry[HSIZE];
	static long hashb = 0L;
	static final long[] hstack = new long[0x800];
	static final long[] mstack = new long[0x800];

	static final long[] BIT = new long[64];
	static final long[] hashxor = new long[4096];
	static final long[] rays = new long[0x10000];
	static final long[][] pmoves = new long[2][64];
	static final long[][] pcaps = new long[2][192];
	static final long[] nmoves = new long[64];
	static final long[] kmoves = new long[64];
	static final int[] _knight = {-17,-10,6,15,17,10,-6,-15};
	static final int[] _king = {-9,-1,7,8,9,1,-7,-8};
	static final int[] nmobil = new int[64];
	static final int[] kmobil = new int[64];
	static final int[][] pawnprg = new int[2][64];
	static final int[] crevoke = new int[64];
	static final long[][] pawnfree = new long[2][64];
	static final long[][] pawnfile = new long[2][64];
	static final long[][] pawnhelp = new long[2][64];
	static final int cornbase[] = {4, 4, 2, 1, 0, 0 ,0};
	static final int bishcorn[] = new int[64];
	static long whitesq;

	static final int[][] pv = new int[128][128];
	static final String pieceChar = "*PNK.BRQ";
	static long maxtime, starttime;
	static final long[] pieceb = new long[8], colorb = new long[2];
	static final int[] kingpos = new int[2], sf = new int[2];
	static int pon, sabort, mat, onmove, engine =-1, sd = 64;
	static int count, flags;
	static boolean ics = false, ponder = false, pondering = false, analyze = false;

	static final StringBuffer irbuf = new StringBuffer();
	static long BOARD() { return (colorb[0] | colorb[1]); }
	static long RQU() { return (pieceb[QUEEN] | pieceb[ROOK]); }
	static long BQU() { return (pieceb[QUEEN] | pieceb[BISHOP]); }

	static int _getpiece(char s, int[] c) {
		int i;
		for (i = 1; i < 8; i++) 
			if (pieceChar.charAt(i) == s) { c[0] = 0; return i; }
			else if (pieceChar.charAt(i) == s-32) { c[0] = 1; return i; }
		return 0;
	}

	static boolean book;
	static void _parse_fen(String fen, boolean reset) {
		char s, mv = 'w';
		String pos = "", cas = "", enps = "";
		int c, i, halfm = 0, fullm = 1, col = 0, row = 7;
		for (i = 0; i < 8; i++) pieceb[i] = 0L;
		colorb[0] = colorb[1] = hashb = 0L;
		mat = i = c = sf[0] = sf[1] = 0;
		book = false;
		StringTokenizer st = new StringTokenizer(fen, " ");
		if (st.hasMoreTokens()) pos = st.nextToken();
		if (st.hasMoreTokens()) mv = st.nextToken().charAt(0);
		if (st.hasMoreTokens()) cas = st.nextToken();
		if (st.hasMoreTokens()) enps = st.nextToken();
		try {
			if (st.hasMoreTokens()) halfm = Integer.parseInt(st.nextToken());
			if (st.hasMoreTokens()) fullm = Integer.parseInt(st.nextToken()); if (fullm < 1) fullm = 1;
		} catch (NumberFormatException nfe) { }

		for (i = 1; i <= pos.length(); i++) {
			s = pos.charAt(i - 1);
			if (s == '/') {
				row--; col = 0;
			} else if (s >= '1' && s <= '8') {
				col += s - '0';
			} else {
				int[] cp = new int[]{c};
				int p = _getpiece(s, cp), t = row*8 + (col++);
				c = cp[0];
				if (p == KING) kingpos[c] = t;
				else mat += changeMat(_CAP(p) | _TO(t), c^1, -1);
				hashb ^= hashxor[col | row << 3 | p << 6 | c << 9];
				pieceb[p] |= BIT[t];
				colorb[c] |= BIT[t];
			}
		}
		onmove = mv == 'b' ? 1 : 0;
		flags = i = 0;
		for (i = 0; i < cas.length(); i++) {
			s = cas.charAt(i);
			if (s == 'K') flags |= BIT[6];
			if (s == 'k') flags |= BIT[7];
			if (s == 'Q') flags |= BIT[8];
			if (s == 'q') flags |= BIT[9];
		}
		if (enps.charAt(0) >= 'a' && enps.charAt(0) <= 'h' && enps.charAt(1) >= '1' && enps.charAt(1) <= '8')
			flags |= 8*(enps.charAt(1) -'1') + enps.charAt(0) -'a';
		count = (fullm - 1)*2 + onmove + (halfm << 10);
		for (i = 0; i < COUNT(); i++) hstack[i] = 0L;
		if (reset) for (i = 0; i < HSIZE; i++) if (hashDB[i] != null) hashDB[i].key = 0L;
		if (reset) sendBoard(0);
	}

	static String sfen = "rnbqkbnr/pppppppp/////PPPPPPPP/RNBQKBNR w KQkq - 0 1";
	static final int BKSIZE = 8192;
	static final int[] bkmove = new int[BKSIZE*32];
	static final int[] bkflag = new int[BKSIZE];
	static final int[] bkcount = new int[3];

	static void _readbook(String bk) {
		String s0, s1, s2;
		int k, n = 0;
		bkcount[0] = bkcount[1] = 0;
		for (k = 0; k < BKSIZE; k++) bkflag[k] = 2;
		try {
			FileReader fr = new FileReader(bk);
			BufferedReader bf = new BufferedReader(fr);
			String buf = null;
			while ((buf = bf.readLine()) != null) {
				if (buf.length() == 0) continue;
				if (buf.charAt(0) == '[') {
					StringTokenizer st = new StringTokenizer(buf, " ");
					s1 = st.nextToken();
					s2 = st.nextToken();
					if (s2.startsWith("\"OliThink")) bkflag[n] = !s1.startsWith("[Black") ? 0 : 1;
					else if (s1.startsWith("[Result")) {
						if (bkflag[n] != 0) {
							if (s2.startsWith("\"0-")) bkflag[n] = 2;
						} else if (!s2.startsWith("\"1-0")) bkflag[n] = 2;
					}
				} else if (buf.startsWith("1.") && bkflag[n] < 2) {
					int i = 0, j = 0;
					_parse_fen(sfen, false);
					for (;;) {
						String bufi = buf.substring(i);
						if (bufi.indexOf(' ') == -1) break;
						StringTokenizer st = new StringTokenizer(bufi, " ");
						s0 = st.nextToken();
						if (s0.charAt(0) < '1' || s0.charAt(0) > '9') break;
						if (!st.hasMoreTokens()) break;
						s2 = st.nextToken();
						i += s0.length() + s2.length() + 2;
						if (s0.endsWith(".")) {
							s1 = s2; s2 = "";
							bufi = i < buf.length() ? buf.substring(i) : "";
							st = new StringTokenizer(bufi, " ");
							if (st.hasMoreTokens()) {
								s2 = st.nextToken();
								i += s2.length() + 1;
							}
						} else {
							int n1 = s0.indexOf('.');
							if (n1 < 0) break;
							s1 = s0.substring(n1 + 1);
						}
						doMove(bkmove[n*32+ (j++)] = parseMove(s1, 0, 0), 0);
						if ("".equals(s2) || s2.charAt(0) == '*') break;
						doMove(bkmove[n*32+ (j++)] = parseMove(s2, 1, 0), 1);
						if (j > 30 || i >= buf.length()) break;
					}
					bkmove[n*32 + j] = 0;
					if (j != 0) bkcount[bkflag[n]]++;
					if (++n == BKSIZE) break;
				}
			}
			bf.close();
			fr.close();
		} catch (IOException e) {
		}

		_parse_fen(sfen, true);
		if (bkcount[0] > 0 || bkcount[1] > 0) book = true;
	}

	static long getTime() {
		return System.currentTimeMillis();
	}

	static byte getLsb(long bm) {
		return (byte)Long.numberOfTrailingZeros(bm); // _bitcnt((bm & -bm) -1);
	}

	static byte bitcnt(long bit) {
		return (byte)Long.bitCount(bit);
	}

	static int identPiece(int f) {
		for (int i = PAWN; i <= QUEEN; i++) if (i != ENP && TEST(f, pieceb[i])) return i;
		return ENP;
	}

	static final long[] bmask45 = new long[64];
	static final long[] bmask135 = new long[64];
	static int key000(long b, int f) {
		return (int) ((b >> (f & 56)) & 0x7E);
	}

	static int key090(long b, int f) {
		long _b = (b >> (f&7)) & 0x0101010101010101L;
		_b = _b * 0x0080402010080400L;
		return (int)((_b >> 57) & 0x7F); // or (_b >>> 57)
	}

	static int keyDiag(long _b) {
		_b = _b * 0x0202020202020202L;
		return (int)((_b >> 57) & 0x7F); // or (_b >>> 57)
	}

	static int key045(long b, int f) {
		return keyDiag(b & bmask45[f]);
	}

	static int key135(long b, int f) {
		return keyDiag(b & bmask135[f]);
	}

	static boolean DUALATT(int x, int y, int c) {
		return (battacked(x, c) || battacked(y, c)); }
	static boolean battacked(int f, int c) {
		if ((PCAP(f, c) & pieceb[PAWN]) != 0) return true;
		if ((NCAP(f, c) & pieceb[KNIGHT]) != 0) return true;
		if ((KCAP(f, c) & pieceb[KING]) != 0) return true;
		if ((RCAP1(f, c) & RQU()) != 0) return true;
		if ((RCAP2(f, c) & RQU()) != 0) return true;
		if ((BCAP3(f, c) & BQU()) != 0) return true;
		if ((BCAP4(f, c) & BQU()) != 0) return true;
		return false;
	}

	static long reach(int f, int c) {
		return (NCAP(f, c) & pieceb[KNIGHT])
			| (RCAP1(f, c) & RQU())
			| (RCAP2(f, c) & RQU())
			| (BCAP3(f, c) & BQU())
			| (BCAP4(f, c) & BQU());
	}

	static long attacked(int f, int c) {
		return (PCAP(f, c) & pieceb[PAWN]) | reach(f, c);
	}

	static void _init_pawns(long[] moves, long[] caps, long[] freep, long[] filep, long[] helpp, int c) {
		int i, j;
		for (i = 0; i < 64; i++) {
			int rank = i/8;
			int file = i&7;
			int m = i + (c == 1 ? -8 : 8);
			pawnprg[c][i] = pawnrun[c == 1 ? 7-rank : rank];
			for (j = 0; j < 64; j++) {
				int jrank = j/8;
				int jfile = j&7;
				int dfile = (jfile - file)*(jfile - file);
				if (dfile > 1) continue;
				if ((c == 1 && jrank < rank) || (c == 0 && jrank > rank)) {//The not touched part of the board
					if (dfile == 0) filep[i] |= BIT[j];
					freep[i] |= BIT[j];
				} else if (dfile != 0 && (jrank - rank)*(jrank - rank) <= 1) {
					helpp[i] |= BIT[j];
				}
			}
			if (m < 0 || m > 63) continue;
			moves[i] |= BIT[m];
			if (file > 0) {
				m = i + (c == 1 ? -9 : 7);
				if (m < 0 || m > 63) continue;
				caps[i] |= BIT[m];
				caps[i + 64*(2 - c)] |= BIT[m];
			}
			if (file < 7) {
				m = i + (c == 1 ? -7 : 9);
				if (m < 0 || m > 63) continue;
				caps[i] |= BIT[m];
				caps[i + 64*(c + 1)] |= BIT[m];
			}
		}
	}

	static void _init_shorts(long[] moves, int[] m) {
		int i, j, n;
		for (i = 0; i < 64; i++) {
			for (j = 0; j < 8; j++) {
				n = i + m[j];
				if (n < 64 && n >= 0 && ((n & 7)-(i & 7))*((n & 7)-(i & 7)) <= 4) {
					moves[i] |= BIT[n];
				}
			}
		}
	}

	static long _occ_free_board(int bc, int del, long free) {
		long low, perm = free;
		int i;
		for (i = 0; i < bc; i++) {
			low = free & (-free); // Lowest bit
			free &= (~low);
			if (!TEST(i, del)) perm &= (~low);
		}
		return perm;
	}

	static void _init_rays(int off, Class<?> c, String srayf, String skey)  throws Exception {
		int i, f, iperm, bc, index;
		long board, mmask, occ, move, xray;
		Method rayFunc = c.getDeclaredMethod(srayf, int.class, long.class, int.class);
		Method key = c.getDeclaredMethod(skey, long.class, int.class);
		for (f = 0; f < 64; f++) {
			mmask = (Long) rayFunc.invoke(c, f, 0L, 0) | BIT[f];
			iperm = 1 << (bc = bitcnt(mmask));
			for (i = 0; i < iperm; i++) {
				board = _occ_free_board(bc, i, mmask);
				move = (Long) rayFunc.invoke(c, f, board, 1);
				occ = (Long) rayFunc.invoke(c, f, board, 2);
				xray = (Long) rayFunc.invoke(c, f, board, 3);
				index = (Integer) key.invoke(c, board, f);
				rays[(f << 7) + index + off] = occ | move;
				rays[(f << 7) + index + 0x8000 + off] = xray;
			}
		}
	}

	static long _rook0(int f, long board, int t) {
		long free = 0L, occ = 0L, xray = 0L;
		int i, b;
		for (b = 0, i = f+1; i < 64 && i%8 != 0; i++) {
			if (TEST(i, board)) { if (b != 0) { xray |= BIT[i]; break; } else { occ |= BIT[i]; b = 1; }}
			if (b == 0) free |= BIT[i];
		}
		for (b = 0, i = f-1; i >= 0 && i%8 != 7; i--) {
			if (TEST(i, board)) { if (b != 0) { xray |= BIT[i]; break; } else { occ |= BIT[i]; b = 1; }}
			if (b == 0) free |= BIT[i];
		}
		return (t < 2) ? free : (t == 2 ? occ : xray);
	}

	static long _rook90(int f, long board, int t) {
		long free = 0L, occ = 0L, xray = 0L;
		int i, b;
		for (b = 0, i = f-8; i >= 0; i-=8) {
			if (TEST(i, board)) { if (b != 0) { xray |= BIT[i]; break; } else { occ |= BIT[i]; b = 1; }}
			if (b == 0) free |= BIT[i];
		}
		for (b = 0, i = f+8; i < 64; i+=8) {
			if (TEST(i, board)) { if (b != 0) { xray |= BIT[i]; break; } else { occ |= BIT[i]; b = 1; }}
			if (b == 0) free |= BIT[i];
		}
		return (t < 2) ? free : (t == 2 ? occ : xray);
	}

	static long _bishop45(int f, long board, int t) {
		long free = 0L, occ = 0L, xray = 0L;
		int i, b;
		for (b = 0, i = f+9; i < 64 && (i%8 != 0); i+=9) {
			if (TEST(i, board)) { if (b != 0) { xray |= BIT[i]; break; } else { occ |= BIT[i]; b = 1; }}
			if (b == 0) free |= BIT[i];
		}
		for (b = 0, i = f-9; i >= 0 && (i%8 != 7); i-=9) {
			if (TEST(i, board)) { if (b != 0) { xray |= BIT[i]; break; } else { occ |= BIT[i]; b = 1; }}
			if (b == 0) free |= BIT[i];
		}
		return (t < 2) ? free : (t == 2 ? occ : xray);
	}

	static long _bishop135(int f, long board, int t) {
		long free = 0L, occ = 0L, xray = 0L;
		int i, b;
		for (b = 0, i = f-7; i >= 0 && (i%8 != 0); i-=7) {
			if (TEST(i, board)) { if (b != 0) { xray |= BIT[i]; break; } else { occ |= BIT[i]; b = 1; }}
			if (b == 0) free |= BIT[i];
		}
		for (b = 0, i = f+7; i < 64 && (i%8 != 7); i+=7) {
			if (TEST(i, board)) { if (b != 0) { xray |= BIT[i]; break; } else { occ |= BIT[i]; b = 1; }}
			if (b == 0) free |= BIT[i];
		}
		return (t < 2) ? free : (t == 2 ? occ : xray);
	}

	static class ReadThread extends Thread {
		boolean stop = false;
		public void run() {
			while (!this.stop) {
				readln();
				try {
					Thread.sleep(10);
				} catch (InterruptedException e) {
				}
			}
		}
	}

	static boolean bioskey() {
		return !inString.isEmpty();
	}

	static void printf(String s) {
		System.out.print(s);
	}

	static void errprintf(String s) {
		System.err.print(s);
	}

	static long pinnedPieces(int f, int oc) {
		long pin = 0L;
		long b = ((RXRAY1(f) | RXRAY2(f)) & colorb[oc]) & RQU();
		while (b != 0) {
			int t = getLsb(b); b &= b - 1;
			pin |= RCAP(t, oc) & ROCC(f);
		}
		b = ((BXRAY3(f) | BXRAY4(f)) & colorb[oc]) & BQU();
		while (b != 0) {
			int t = getLsb(b); b &= b - 1;
			pin |= BCAP(t, oc) & BOCC(f);
		}
		return pin;
	}

	/* precondition: f and t are on common rank (8), file (16), diagonal (32) or antidiagonal (64) */
	static byte getDir(int f, int t) {
		if (((f ^ t) & 56) == 0) return 8;
		if (((f ^ t) & 7) == 0) return 16;
		return (byte)(((f - t) % 9) == 0 ? 32 : 64);
	}

	static int changeMat(int m, int c, int d) {
		int dm = pval[CAP(m)];
		if (PROM(m) != 0) dm += -pval[PAWN] + pval[PROM(m)];
		sf[c] += d*fval[PROM(m)];
		sf[c^1] -= d*fval[CAP(m)];
		return c != 0 ? -d*dm : d*dm;
	}

	/* move is for both doMove and undoMove, only for undo the globalflags have to be restored (counter, castle, enp)*/
	static void move(int m, int c, int d) {
		int f = FROM(m);
		int t = TO(m);
		int p = PIECE(m);
		int a = CAP(m);

		colorb[c] ^= BIT[f];
		pieceb[p] ^= BIT[f];

		colorb[c] ^= BIT[t];
		pieceb[p] ^= BIT[t];
		hashb ^= hashxor[(f) | (p) << 6 | (c) << 9];
		hashb ^= hashxor[(t) | (p) << 6 | (c) << 9];

		if (a != 0) {
			if (a == ENP) { // Enpassant Capture
				t = (t&7) | (f&56); a = PAWN;
			} else if (a == ROOK && CASTLE() != 0) { //Revoke castling rights.
				flags &= crevoke[t];
			}
			pieceb[a] ^= BIT[t];
			colorb[c^1] ^= BIT[t];
			hashb ^= hashxor[(t) | (a) << 6 | (c^1) << 9];
			count &= 0x3FF; //Reset Fifty Counter
			mat += changeMat(m, c, d);
		}
		if (p == PAWN) {
			if (((f^t)&8) == 0) flags |= f^24; //Enpassant
			else if ((t&56) == 0 || (t&56) == 56) {
				pieceb[PAWN] ^= BIT[t];
				pieceb[PROM(m)] ^= BIT[t];
				hashb ^= hashxor[(t) | (PAWN) << 6 | (c) << 9];
				hashb ^= hashxor[(t) | (PROM(m)) << 6 | (c) << 9];
				if (a == 0) mat += changeMat(m, c, d);
			}
			count &= 0x3FF; //Reset Fifty Counter
		} else if (p == KING) {
			if (kingpos[c] == f) kingpos[c] = t; else kingpos[c] = f;
			flags &= ~(320 << c); // Lose castling rights
			if (((f^t)&3) == 2) { // Castle
				if (t == 6) { f = 7; t = 5; }
				else if (t == 2) { f = 0; t = 3; }
				else if (t == 62) { f = 63; t = 61; }
				else { f = 56; t = 59; }
				colorb[c] ^= BIT[f];
				pieceb[ROOK] ^= BIT[f];
				colorb[c] ^= BIT[t];
				pieceb[ROOK] ^= BIT[t];
				hashb ^= hashxor[(f) | (ROOK) << 6 | (c) << 9];
				hashb ^= hashxor[(t) | (ROOK) << 6 | (c) << 9];
			}
		} else if (p == ROOK && CASTLE() != 0) {
			flags &= crevoke[f];
		}
	}

	static void doMove(int m, int c) {
		mstack[COUNT()] = count | (flags << 17) | (((long)m) << 27);
		flags &= 960; // reset en-passant flags
		count += 0x401; // counter++
		if (m != 0) move(m, c, 1);
	}

	static void undoMove(int m, int c) {
		long u = mstack[COUNT() - 1];
		if (m != 0) move(m, c, -1);
		count = (int)(u & 0x1FFFF);
		flags = (int)((u >> 17L) & 0x3FF);
	}

	static void regMoves(int m, long bt, Movep mp, int cap) {
		while (bt != 0) {
			int t = getLsb(bt); bt &= bt - 1;
			mp.list[mp.n++] = m | _TO(t) | (cap != 0 ? _CAP(identPiece(t)) : 0);
		}
	}
	
	static void regMovesCaps(int m, long bc, long bm, Movep mp) {
		regMoves(m, bc, mp, 1);
		regMoves(m, bm, mp, 0);
	}

	static void regPromotions(int f, int c, long bt, Movep mp, int cap, int queen) {
		while (bt != 0) {
			int t = getLsb(bt); bt &= bt - 1;
			int m = f | _ONMV(c) | _PIECE(PAWN) | _TO(t) | (cap != 0 ? _CAP(identPiece(t)) : 0);
			if (queen != 0) mp.list[mp.n++] = m | _PROM(QUEEN);
			mp.list[mp.n++] = m | _PROM(KNIGHT);
			mp.list[mp.n++] = m | _PROM(ROOK);
			mp.list[mp.n++] = m | _PROM(BISHOP);
		}
	}

	static void regKings(int m, long bt, Movep mp, int c, int cap) {
		while (bt != 0) {
			int t = getLsb(bt); bt &= bt - 1;
			if (battacked(t, c)) continue;
			mp.list[mp.n++] = m | _TO(t) | (cap != 0 ? _CAP(identPiece(t)) : 0);
		}
	}

	static int generateCheckEsc(long ch, long apin, int c, int k, Movep mp) {
		long cc, fl;
		int d, bf = bitcnt(ch);
		colorb[c] ^= BIT[k];
		regKings(PREMOVE(k, KING, c), KCAP(k, c), mp, c, 1);
		regKings(PREMOVE(k, KING, c), KMOVE(k), mp, c, 0);
		colorb[c] ^= BIT[k];
		if (bf > 1) return bf; //Doublecheck
		bf = getLsb(ch);

		cc = attacked(bf, c^1) & apin;  //Can we capture the checker?
		while (cc != 0) {
			int cf = getLsb(cc); cc &= cc -1;
			int p = identPiece(cf);
			if (p == PAWN && RANK(cf, c != 0 ? 0x08 : 0x30)) {
				regPromotions(cf, c, ch, mp, 1, 1);
			} else {
				regMovesCaps(PREMOVE(cf, p, c), ch, 0L, mp);
			}
		}
		if (ENPASS() != 0 && (ch & pieceb[PAWN]) != 0) { //Enpassant capture of attacking Pawn
			cc = PCAP(ENPASS(), c^1) & pieceb[PAWN] & apin;
			while (cc != 0) {
				int cf = getLsb(cc); cc &= cc -1;
				regMovesCaps(PREMOVE(cf, PAWN, c), BIT[ENPASS()], 0L, mp);
			}
		}
		if ((ch & (nmoves[k] | kmoves[k])) != 0) return 1; //We can't move anything between!

		d = getDir(bf, k);
		if ((d & 8) != 0) fl = RMOVE1(bf) & RMOVE1(k);
		else if ((d & 16) != 0) fl = RMOVE2(bf) & RMOVE2(k);
		else if ((d & 32) != 0) fl = BMOVE3(bf) & BMOVE3(k);
		else fl = BMOVE4(bf) & BMOVE4(k);

		while (fl != 0) {
			int f = getLsb(fl);
			fl ^= BIT[f];
			cc = reach(f, c^1) & apin;
			while (cc != 0) {
				int cf = getLsb(cc); cc &= cc -1;
				int p = identPiece(cf);
				regMovesCaps(PREMOVE(cf, p, c), 0L, BIT[f], mp);
			}
			bf = c != 0 ? f+8 : f-8;
			if (bf < 0 || bf > 63) continue;
			if ((BIT[bf] & pieceb[PAWN] & colorb[c] & apin) != 0) {
				if (RANK(bf, c != 0 ? 0x08 : 0x30))
					regPromotions(bf, c, BIT[f], mp, 0, 1);
				else
					regMovesCaps(PREMOVE(bf, PAWN, c), 0L, BIT[f], mp);
			}
			if (RANK(f, c != 0 ? 0x20 : 0x18) && (BOARD() & BIT[bf]) == 0
					&& (BIT[c != 0 ? f+16 : f-16] & pieceb[PAWN] & colorb[c] & apin) != 0)
						regMovesCaps(PREMOVE(c != 0 ? f+16 : f-16, PAWN, c), 0L, BIT[f], mp);
		}
		return 1;
	}

	static void generateNonCaps(int c, int f, long pin, Movep mp) {
		long m, b, cb = colorb[c] & (~pin);

		regKings(PREMOVE(f, KING, c), KMOVE(f), mp, c, 0);

		b = pieceb[PAWN] & cb;
		while (b != 0) {
			f = getLsb(b); b &= b - 1;
			m = PMOVE(f, c);
			if (m != 0 && RANK(f, c != 0 ? 0x30 : 0x08)) m |= PMOVE(c != 0 ? f-8 : f+8, c);
			if (RANK(f, c != 0 ? 0x08 : 0x30)) {
				long a = PCAP(f, c);
				if (a != 0L) regPromotions(f, c, a, mp, 1, 0);
				regPromotions(f, c, m, mp, 0, 0);
			} else {
				regMoves(PREMOVE(f, PAWN, c), m, mp, 0);
			}
		}

		b = pin & pieceb[PAWN];
		while (b != 0) {
			f = getLsb(b); b &= b - 1;
			int t = getDir(f, kingpos[c]);
			if ((t & 8) != 0) continue;
			m = 0L;
			if ((t & 16) != 0) {
				m = PMOVE(f, c);
				if (m != 0 && RANK(f, c != 0 ? 0x30 : 0x08)) m |= PMOVE(c != 0 ? f-8 : f+8, c);
			}
			if (RANK(f, c != 0 ? 0x08 : 0x30)) {
				long a = (t & 32) != 0 ? PCA3(f, c) : ((t & 64) != 0 ? PCA4(f, c) : 0L);
				if (a != 0L) regPromotions(f, c, a, mp, 1, 0);
			} else {
				regMoves(PREMOVE(f, PAWN, c), m, mp, 0);
			}
		}

		b = pieceb[KNIGHT] & cb;
		while (b != 0) {
			f = getLsb(b); b &= b - 1;
			regMoves(PREMOVE(f, KNIGHT, c), NMOVE(f), mp, 0);
		}

		b = pieceb[ROOK] & cb;
		while (b != 0) {
			f = getLsb(b); b &= b - 1;
			regMoves(PREMOVE(f, ROOK, c), RMOVE(f), mp, 0);
			if (CASTLE() != 0) {
				if (c != 0) {
					if ((flags & 128) != 0 && (f == 63) && (RMOVE1(63) & BIT[61]) != 0)
						if (!DUALATT(61, 62, c)) regMoves(PREMOVE(60, KING, c), BIT[62], mp, 0);
					if ((flags & 512) != 0 && (f == 56) && (RMOVE1(56) & BIT[59]) != 0)
						if (!DUALATT(59, 58, c)) regMoves(PREMOVE(60, KING, c), BIT[58], mp, 0);
				} else {
					if ((flags & 64) != 0 && (f == 7) && (RMOVE1(7) & BIT[5]) != 0)
						if (!DUALATT(5, 6, c)) regMoves(PREMOVE(4, KING, c), BIT[6], mp, 0);
					if ((flags & 256) != 0 && (f == 0) && (RMOVE1(0) & BIT[3]) != 0)
						if (!DUALATT(3, 2, c)) regMoves(PREMOVE(4, KING, c), BIT[2], mp, 0);
				}
			}
		}

		b = pieceb[BISHOP] & cb;
		while (b != 0) {
			f = getLsb(b); b &= b - 1;
			regMoves(PREMOVE(f, BISHOP, c), BMOVE(f), mp, 0);
		}

		b = pieceb[QUEEN] & cb;
		while (b != 0) {
			f = getLsb(b); b &= b - 1;
			regMoves(PREMOVE(f, QUEEN, c), RMOVE(f) | BMOVE(f), mp, 0);
		}

		b = pin & (pieceb[ROOK] | pieceb[BISHOP] | pieceb[QUEEN]); 
		while (b != 0) {
			f = getLsb(b); b &= b - 1;
			int p = identPiece(f);
			int t = p | getDir(f, kingpos[c]);
			if ((t & 10) == 10) regMoves(PREMOVE(f, p, c), RMOVE1(f), mp, 0);
			if ((t & 18) == 18) regMoves(PREMOVE(f, p, c), RMOVE2(f), mp, 0);
			if ((t & 33) == 33) regMoves(PREMOVE(f, p, c), BMOVE3(f), mp, 0);
			if ((t & 65) == 65) regMoves(PREMOVE(f, p, c), BMOVE4(f), mp, 0);
		}
	}

	static void generateCaps(int c, int f, long pin, Movep mp) {
		long m, b, a, cb = colorb[c] & (~pin);

		regKings(PREMOVE(f, KING, c), KCAP(f, c), mp, c, 1);

		b = pieceb[PAWN] & cb;
		while (b != 0) {
			f = getLsb(b); b &= b - 1;
			a = PCAP(f, c);
			if (RANK(f, c != 0 ? 0x08 : 0x30)) {
				regMovesCaps(PREMOVE(f, PAWN, c) | _PROM(QUEEN), a, PMOVE(f, c), mp);
			} else {
				if (ENPASS() != 0 && (BIT[ENPASS()] & pcaps[(c)][(f)]) != 0) {
					colorb[c^1] ^= BIT[ENPASS()^8];
					if ((ROCC1(f) & BIT[kingpos[c]]) == 0 || (ROCC1(f) & colorb[c^1] & RQU()) == 0) {
						a = a | BIT[ENPASS()];
					}
					colorb[c^1] ^= BIT[ENPASS()^8];
				}
				regMoves(PREMOVE(f, PAWN, c), a, mp, 1);
			}
		}

		b = pin & pieceb[PAWN];
		while (b != 0) {
			f = getLsb(b); b &= b - 1;
			int t = getDir(f, kingpos[c]);
			if ((t & 8) != 0) continue;
			m = a = 0L;
			if ((t & 16) != 0) {
				m = PMOVE(f, c);
			} else if ((t & 32) != 0) {
				a = PCA3(f, c);
			} else {
				a = PCA4(f, c);
			}
			if (RANK(f, c != 0 ? 0x08 : 0x30)) {
				regMovesCaps(PREMOVE(f, PAWN, c) | _PROM(QUEEN), a, m, mp);
			} else {
				regMoves(PREMOVE(f, PAWN, c), a, mp, 1);
			}
		}

		b = pieceb[KNIGHT] & cb;
		while (b != 0) {
			f = getLsb(b); b &= b - 1;
			regMoves(PREMOVE(f, KNIGHT, c), NCAP(f, c), mp, 1);
		}

		b = pieceb[BISHOP] & cb;
		while (b != 0) {
			f = getLsb(b); b &= b - 1;
			regMoves(PREMOVE(f, BISHOP, c), BCAP(f, c), mp, 1);
		}

		b = pieceb[ROOK] & cb;
		while (b != 0) {
			f = getLsb(b); b &= b - 1;
			regMoves(PREMOVE(f, ROOK, c), RCAP(f, c), mp, 1);
		}

		b = pieceb[QUEEN] & cb;
		while (b != 0) {
			f = getLsb(b); b &= b - 1;
			regMoves(PREMOVE(f, QUEEN, c), RCAP(f, c) | BCAP(f,c), mp, 1);
		}

		b = pin & (pieceb[ROOK] | pieceb[BISHOP] | pieceb[QUEEN]);
		while (b != 0) {
			f = getLsb(b); b &= b - 1;
			int p = identPiece(f);
			int t = p | getDir(f, kingpos[c]);
			if ((t & 10) == 10) regMoves(PREMOVE(f, p, c), RCAP1(f, c), mp, 1);
			if ((t & 18) == 18) regMoves(PREMOVE(f, p, c), RCAP2(f, c), mp, 1);
			if ((t & 33) == 33) regMoves(PREMOVE(f, p, c), BCAP3(f, c), mp, 1);
			if ((t & 65) == 65) regMoves(PREMOVE(f, p, c), BCAP4(f, c), mp, 1);
		}
	}

	static int generate(long ch, int c, Movep mp, boolean cap, boolean noncap) {
		int f = kingpos[c];
		long pin = pinnedPieces(f, c^1);
		mp.n = 0;

		if (ch != 0L) return generateCheckEsc(ch, ~pin, c, f, mp);
		if (cap) generateCaps(c, f, pin, mp);
		if (noncap) generateNonCaps(c, f, pin, mp);
		return 0;
	}

	static int swap(int m) { //SEE
		int[] s_list = new int[32];
		int f = FROM(m), t = TO(m), c = ONMV(m);
		int a_piece = pval[CAP(m)], piece = PIECE(m), nc = 1;
		long temp = 0, colstore0 = colorb[0], colstore1 = colorb[1];

		long attacks = ((PCAP(t, 0) | PCAP(t, 1)) & pieceb[PAWN]) |
				(nmoves[t] & pieceb[KNIGHT]) | (kmoves[t] & pieceb[KING]);
		s_list[0] = a_piece;
		a_piece = pval[piece];
		colorb[c] &= ~BIT[f]; // ^= BIT[f];

		do {
			c ^= 1;
			attacks |= (BOCC(t) & BQU()) | (ROCC(t) & RQU());
			attacks &= BOARD();

			if ((temp = pieceb[PAWN] & colorb[c] & attacks) != 0) piece = PAWN;
			else if ((temp = pieceb[KNIGHT] & colorb[c] & attacks) != 0) piece = KNIGHT;
			else if ((temp = pieceb[BISHOP] & colorb[c] & attacks) != 0) piece = BISHOP;
			else if ((temp = pieceb[ROOK] & colorb[c] & attacks) != 0) piece = ROOK;
			else if ((temp = pieceb[QUEEN] & colorb[c] & attacks) != 0) piece = QUEEN;
			else if ((temp = pieceb[KING] & colorb[c] & attacks) != 0) { 
				piece = KING; if ((colorb[c^1] & attacks) !=0) break; }
			else break;

			temp &= -(long)temp;
			colorb[c] ^= temp;

			s_list[nc] = -s_list[nc - 1] + a_piece;
			a_piece = pval[piece];
			if (a_piece < s_list[++nc - 1]) break;
		} while (true);

		while ((--nc) != 0)
			if (s_list[nc] > -s_list[nc - 1])
				s_list[nc - 1] = -s_list[nc];

		colorb[0] = colstore0;
		colorb[1] = colstore1;
		return s_list[0];
	}

	/* In quiesce the list are ordered just for the value of the captured piece */
	static int qpick(Movep mp, int s) {
		int m;
		int i, t, pi = 0, vmax = -9999;
		for (i = s; i < mp.n; i++) {
			m = mp.list[i];
			t = pval[CAP(m)] - fval[PIECE(m)];
			if (t > vmax) { vmax = t; pi = i; }
		}
		m = mp.list[pi];
		if (pi != s) mp.list[pi] = mp.list[s];
		return m;
	}

	static final int[] killer = new int[128];
	static final long[] history = new long[0x2000];
	/* In normal search some basic move ordering heuristics are used */
	static int spick(Movep mp, int s, int ply) {
		int m, i, pi = 0;
		long vmax = -(1L << 62);
		for (i = s; i < mp.n; i++) {
			m = mp.list[i];
			if (m == killer[ply]) {
				pi = i;
				break;
			}
			if (vmax < history[m & 0x1FFF]) { vmax = history[m & 0x1FFF]; pi = i; }
		}
		m = mp.list[pi];
		if (pi != s) mp.list[pi] = mp.list[s];
		return m;
	}

	static long rankb[] = new long [8];
	static long fileb[] = new long [8];

	static long pawnAttack(int c) {
		long p = colorb[c] & pieceb[PAWN];
		return c == 0 ? (p &~ fileb[0]) << 7 | (p &~ fileb[7]) << 9 : (p &~ fileb[7]) >> 7 | (p &~ fileb[0]) >> 9;
	}

	static long mobilityb(int c) {
		long b = c == 0 ? rankb[1] | (BOARD() >> 8) : rankb[6] | (BOARD() << 8);
		b &= b & colorb[c] & pieceb[PAWN];
		return ~(b | pawnAttack(c^1));
	}

	static int MOBILITY(long a, long mb) { return bitcnt(a) + bitcnt(a & mb); }
	/* The eval for Color c. It's almost only mobility. Pinned pieces are still awarded for limiting opposite's king */
	static int evalc(int c) {
		int f, mn = 0, katt = 0, egf = 5200/(40 + sf[c]);
		int oc = c^1;
		long b, a, cb, ocb = colorb[oc], mb = sf[c] != 0 ? mobilityb(c) : 0L;
		long kn = kmoves[kingpos[oc]] & (~pieceb[PAWN]);
		long pin = pinnedPieces(kingpos[c], oc);

		b = pieceb[PAWN] & colorb[c];
		while (b != 0) {
			f = getLsb(b); b &= b - 1;

			/* The only non-mobility eval is the detection of free pawns/hanging pawns */
			int ppos = pawnprg[c][f]* egf / 100;
			if ((pawnfree[c][f] & pieceb[PAWN] & ocb) == 0) ppos <<= 1; //Free run?

			if ((pawnhelp[c][f] & pieceb[PAWN] & colorb[c]) == 0) { // No support
				boolean openfile = (pawnfile[c][f] & pieceb[PAWN] & ocb) == 0;
				ppos -= (openfile ? 32 : 10);  // Open file
			}

			a = POCC(f, c);
			if (a != 0) ppos += bitcnt(a & pieceb[PAWN] & colorb[c]) << 2;
			if ((a & kn) != 0) katt += MOBILITY(a & kn, mb) << 3;
			mn += ppos;
		}

		cb = colorb[c] & (~pin);
		b = pieceb[KNIGHT] & cb;
		while (b != 0) {
			f = getLsb(b); b &= b - 1;
			a = nmoves[f];
			if ((a & kn) != 0) katt += MOBILITY(a & kn, mb) << 3;
			mn += MOBILITY(a, mb) << 2;
		}

		b = pieceb[KNIGHT] & pin;
		while (b != 0) {
			f = getLsb(b); b &= b - 1;
			a = nmoves[f];
			if ((a & kn) != 0) katt += MOBILITY(a & kn, mb) << 3;
		}

		colorb[oc] ^= BIT[kingpos[oc]]; //Opposite King doesn't block mobility at all
		colorb[c] ^= pieceb[QUEEN] & cb; //Own non-pinned Queen doesn't block mobility for bishop.
		b = pieceb[QUEEN] & cb;
		while (b != 0) {
			f = getLsb(b); b &= b - 1;
			a = BATT3(f) | BATT4(f) | RATT1(f) | RATT2(f);
			if ((a & kn) != 0) katt += MOBILITY(a & kn, mb) << 3;
			mn += MOBILITY(a, mb) * egf * egf / 78 / 78;
		}

		colorb[oc] ^= RQU() & ocb; //Opposite Queen & Rook doesn't block mobility for bisho
		b = pieceb[BISHOP] & cb;
		while (b != 0) {
			f = getLsb(b); b &= b - 1;
			a = BATT3(f) | BATT4(f);
			if ((a & kn) != 0) katt += MOBILITY(a & kn, mb) << 3;
			mn += MOBILITY(a, mb) << 2;
		}

		colorb[oc] ^= pieceb[ROOK] & ocb; //Opposite Queen doesn't block mobility for rook.
		colorb[c] ^= pieceb[ROOK] & cb; //Own non-pinned Rook doesn't block mobility for rook.
		b = pieceb[ROOK] & cb;
		while (b != 0) {
			f = getLsb(b); b &= b - 1;
			a = RATT1(f) | RATT2(f);
			if ((a & kn) != 0) katt += MOBILITY(a & kn, mb) << 3;
			mn += (MOBILITY(a, mb) << 1) * egf / 75;
		}

		colorb[c] ^= RQU() & cb; // Back
		b = pin & (pieceb[ROOK] | pieceb[BISHOP] | pieceb[QUEEN]);
		while (b != 0) {
			f = getLsb(b); b &= b - 1;
			int p = identPiece(f);
			if (p == BISHOP) a = BATT3(f) | BATT4(f);
			else if (p == ROOK) a = RATT1(f) | RATT2(f);
			else a = RATT1(f) | RATT2(f) | BATT3(f) | BATT4(f);

			if ((a & kn) != 0) katt += MOBILITY(a & kn, mb) << 3;
			int t = p | getDir(f, kingpos[c]);
			if ((t & 10) == 10) mn += bitcnt(RATT1(f));
			if ((t & 18) == 18) mn += bitcnt(RATT2(f));
			if ((t & 33) == 33) mn += bitcnt(BATT3(f));
			if ((t & 65) == 65) mn += bitcnt(BATT4(f));
		}

		colorb[oc] ^= pieceb[QUEEN] & ocb; //Back
		colorb[oc] ^= BIT[kingpos[oc]]; //Back
		return mn + katt * sf[c] / 17; //Reduce the bonus for attacking king squares
	}

	static int kmobilf(int c) {
		int km = kmobil[kingpos[c]] << 2, sfo = sf[c^1];
		if (sf[c] == 0  && sfo == 5 && pieceb[BISHOP] != 0 && pieceb[PAWN] == 0) { // BNK_vs_k
			int bc = bishcorn[kingpos[c]] << 5;
			if ((pieceb[BISHOP] & whitesq) != 0) km += bc; else km -= bc;
		}
		return sfo < 14 ? km : km * (16 - sfo) /4;
	}

	static int evallazy(int c, int matrl) {
		int ev = kmobilf(c) - kmobilf(c^1);

		if ((matrl < 0 && NOMATEMAT(1)) || (matrl > 0 && NOMATEMAT(0)))
			matrl = 0;

		return ev + (c != 0 ? -matrl : matrl);
	}

	static long eval1 = 0;
	static int eval(int c, int matrl) {
		int ev = evalc(c) - evalc(c^1);
		eval1++;

		return ev + evallazy(c, matrl);
	}

	static long nodes, qnodes;
	static int t1, t2;
	static int quiesce(long ch, int c, int ply, int alpha, int beta) {
		int i, best = -MAXSCORE;
		if (ply == 127) return eval(c, mat);

		if (ch == 0) do {
			int cmat = evallazy(c, mat);
			if (cmat - 125 >= beta) return beta;
			if (cmat + 85 <= alpha) break;
			best = eval(c, mat);
			if (best > alpha) {
				alpha = best;
				if (best >= beta) return beta;
			}
		} while(false);

		Movep mp = Movep.get(ply); generate(ch, c, mp, true, false);
		if (ch != 0 && mp.n == 0) return -MAXSCORE + ply;

		for (i = 0; i < mp.n; i++) {
			int m = qpick(mp, i);
			if (ch == 0 && PROM(m) == 0 && pval[PIECE(m)] > pval[CAP(m)] && swap(m) < 0) continue;

			doMove(m, c);
			qnodes++;

			int w = -quiesce(attacked(kingpos[c^1], c^1), c^1, ply+1, -beta, -alpha);

			undoMove(m, c);

			if (w > best) {
				best = w;
				if (w > alpha) {
					alpha = w;
					if (w >= beta) return beta;
				}
			}
		}
		return best > -MAXSCORE ? best : eval(c, mat);
	}

	static int retPVMove(int c, int ply) {
		int i;
		Movep mp = Movep.get(ply); generate(attacked(kingpos[c], c), c, mp, true, true);
		for (i = 0; i < mp.n; i++) {
			int m = mp.list[i];
			if (m == pv[0][ply]) return m;
		}
		return 0;
	}

	static String base;
	static int time = 30000, mps = 0, inc = 0, st = 0;
	static boolean post = true;

	static int inputSearch() {
		int ex;
		irbuf.append(inString.pollFirst());

		ex = protV2(irbuf.toString(), false);
		if (analyze) { if (ex <= -1) return ex; else ex = 0; }
		if (!ponder || ex != 0 || engine != onmove) pondering = analyze;
		if (ex == 0) irbuf.setLength(0);
		if (ex < -1) return ex;
		if (ex != -1) return !pondering ? 1: 0;
		ex = parseMove(irbuf.toString(), ONMV(pon), pon);
		if (ex == 0 || ex == -1) return -1;
		irbuf.setLength(0); pon = 0;
		return time < 50 ? -1 : 0;
	}

	static int isDraw(long hp, int nrep) {
		if (count > 0xFFF) { //fifty > 3
			int i, c = 0, n = COUNT() - (count >> 10);
			if (count >= 0x400*100) return 2; //100 plies
			for (i = COUNT() - 2; i >= n; i--) 
				if (hstack[i] == hp && ++c == nrep) return 1;
		} else if ((pieceb[PAWN] | RQU()) == 0) { //Check for mating material
			if (bitcnt(BOARD()) <= 3) return 3;
		}
		return 0;
	}

	static final int nullvar[] = new int[] {13, 43, 149, 519, 1809, 6311, 22027};
	static int nullvariance(int delta) {
		int r = 0;
		if (delta >= 4) for (r = 1; r <= nullvar.length; r++) if (delta < nullvar[r - 1]) break;
		return r;
	}

	static long HASHP(int c) { return (hashb ^ hashxor[flags | 1024 | (c << 11)]); }
	static int search(long ch, int c, int d, int ply, int alpha, int beta, boolean isnull) {
		int i, j, n, w = 0, oc = c^1;
		boolean pvnode = beta > alpha + 1;

		if (ply != 0) pv[ply][ply] = 0;
		if ((++nodes & CNODES) == 0) {
			while (bioskey() && sabort == 0) sabort = inputSearch();
			if (!pondering && getTime() - starttime > maxtime) sabort = 1;
		}
		if (sabort != 0) return alpha;

		long hp = HASHP(c), hismax = -1L;
		if (ply != 0 && isDraw(hp, 1) != 0) return 0;

		if (ch != 0) d++;
		if (d <= 0 || ply > 100) return quiesce(ch, c, ply, alpha, beta);

		if (alpha < -MAXSCORE+ply) alpha = -MAXSCORE+ply;
		if (beta > MAXSCORE-ply-1) beta = MAXSCORE-ply-1;
		if (alpha >= beta) return alpha;

		int hmove = ply != 0 ? 0 : retPVMove(c, ply);

		Entry he = hashDB[(int)(hp & HMASK)]; if (he == null) hashDB[(int)(hp & HMASK)] = he = new Entry();
		if (he.key == hp) {
			if (he.depth >= d) {
				if (he.type <= EXACT && he.value >= beta) return beta;
				if (he.type >= EXACT && he.value <= alpha) return alpha;
			}
			if (hmove == 0) hmove = he.move;
		}

		int wstat = ch != 0 ? -MAXSCORE+ply : he.key == hp ? he.valstat : eval(c, mat);
		if (ch == 0 && !pvnode && beta > -MAXSCORE+500) {
			if (d <= 3 && wstat + 400 < beta) { w = quiesce(ch, c, ply, alpha, beta); if (w < beta) return w; }
			if (d <= 8 && wstat - 88*d > beta) return wstat;
		}

		hstack[COUNT()] = hp;
		//Null Move - pvnode => null == 0
		isnull = isnull && ch == 0 && beta > -MAXSCORE+500 && d > 1 && wstat > alpha
				&& (ply < 2 || (mstack[COUNT()-2] >> 27) != 0);
		if (isnull && bitcnt(colorb[c] & (~pieceb[PAWN]) & (~pinnedPieces(kingpos[c], oc))) > 1) {
			int R = (10 + d + nullvariance(wstat - alpha))/4;
			doMove(0, c);
			w = -search(0L, oc, d-R, ply+1, -beta, 1-beta, false); //Null Move Search
			undoMove(0, c);
			if (sabort == 0 && w >= beta) return w >= MAXSCORE-500 ? beta : w;
		}

		if (d >= 5 && hmove == 0) { // Internal Iterative Reduction (IIR)
			d--;
		}

		Movep mp = Movep.get(ply); mp.nquiet = 0;
		int first = NO_MOVE;
		for (n = HASH; n <= ((ch != 0L) ? NOISY : QUIET); n++) {
			if (n == HASH) {
				if (hmove == 0) continue;
				mp.n = 1;
			} else if (n == NOISY) {
				generate(ch, c, mp, true, false);
			} else {
				generate(ch, c, mp, false, true);
			}
			for (i = 0; i < mp.n; i++) {
				int m;
				long nch;
				int ext = 0;
				if (n == HASH) {
					m = hmove;
				} else {
					if (n == NOISY) m = qpick(mp, i);
					else m = spick(mp, i, ply);
					if (m == hmove) continue;
					if (first != NO_MOVE && d <= 8 && swap(m) < -d*60) continue;
				}
				doMove(m, c);
				if (CAP(m) == 0 && PROM(m) == 0) mp.quiets[mp.nquiet++] = m;
				nch = attacked(kingpos[c^1], c^1);
				if (nch != 0 || pvnode || ch != 0); // Don't reduce pvnodes and check evasions
				else if (n == NOISY && d >= 2 && PROM(m) == 0 && swap(m) < 0) ext-= (d + 1)/3; //Reduce bad exchanges
				else if (n == QUIET) { //LMR
					if (m == killer[ply]); //Don't reduce killers
					else if (PIECE(m) == PAWN && (pawnfree[c][TO(m)] & pieceb[PAWN] & colorb[oc]) == 0);
					else {
						long his = history[m & 0x1FFF];
						if (his > hismax) hismax = his;
	                    else if (d <= 5 && (his < -1 || his*his < hismax)) { undoMove(m, c); continue; }
						else if (d >= 2) ext-= (d + 1)/3;
					}
				}
				if (PROM(m) == QUEEN) ext++;

				if (first == NO_MOVE && pvnode) {
					w = -search(nch, oc, d-1+ext, ply+1, -beta, -alpha, false);
				} else {
					w = -search(nch, oc, d-1+ext, ply+1, -alpha-1, -alpha, true);
					if (w > alpha && ext < 0) w = -search(nch, oc, d-1, ply+1, -alpha-1, -alpha, true);
					if (w > alpha && w < beta && pvnode) w = -search(nch, oc, d-1+ext, ply+1, -beta, -alpha, false);
				}
				undoMove(m, c);
				if (sabort != 0) return alpha;

				if (w > alpha) {
					alpha = w; first = GOOD_MOVE;
					pv[ply][ply] = m;
					for (j = ply +1; pv[ply +1][j] != 0; j++) pv[ply][j] = pv[ply +1][j];
					pv[ply][j] = 0;

					if (w >= beta) {
						if (CAP(m) == 0 && PROM(m) == 0) {
							int his = Math.min(d*d, 512);
							killer[ply] = m;
							history[m & 0x1FFF] += his;

							for (j = 0; j < mp.nquiet; j++) {
								int m2 = mp.quiets[j];
								if (m2 != m) history[m2 & 0x1FFF] -= his;
							}
						}
						n = EXIT; break;
					}
				} else if (first == NO_MOVE) first = ANY_MOVE;
			}
		}
		if (sabort != 0) return alpha;
		if (first == NO_MOVE) alpha = ch != 0 ? -MAXSCORE+ply : 0;

		char type = UPPER;
		if (first == GOOD_MOVE) { type = (char)(alpha >= beta ? LOWER : EXACT); hmove = pv[ply][ply]; } // Good move

		he.set(hp, hmove, (short)alpha, (char)d, type, (short)wstat);

		return alpha;
	}

	static int execMove(int m) {
		doMove(m, onmove);
		sendMove(m, engine == onmove);
		onmove ^= 1;
		int i, c = onmove;
		if (book) for (i = 0; i < BKSIZE; i++) {
			if (bkflag[i] < 2 && (bkmove[i*32 + COUNT() - 1] != m || bkmove[i*32 + COUNT()] == 0)) {
				bkcount[bkflag[i]]--;
				bkflag[i] = 2;
			}
		}
		hstack[COUNT()] = HASHP(c);
		for (i = 0; i < 127; i++) pv[0][i] = pv[0][i+1];

		Movep mp = Movep.get(0); i = generate(attacked(kingpos[c], c), c, mp, true, true);
		if (pondering) return (mp.n == 0 ? 7 : 0);
		if (mp.n == 0) {
			if (i == 0) {
				printf("1/2-1/2 {Stalemate}\n"); return 4;
			} else {
				printf(c == 1 ? "1-0 {White mates}\n" : "0-1 {Black mates}\n"); return 5 + c;
			}
		}
		switch (isDraw(HASHP(c), 2)) {
			case 1: printf("1/2-1/2 {Draw by Repetition}\n"); return 1;
			case 2: printf("1/2-1/2 {Draw by Fifty Move Rule}\n"); return 2;
			case 3: printf("1/2-1/2 {Insufficient material}\n"); return 3;
		}
		return 0;
	}

	static boolean ISRANK(int c) { return (c >= '1' && c <= '8'); }
	static boolean ISFILE(int c) { return (c >= 'a' && c <= 'h'); }
	static boolean ismove(int m, int to, int from, int piece, int prom, int h) {
		if (TO(m) != to) return false;
		if (from < 0 && PIECE(m) != piece) return false;
		if (from >= 0 && FROM(m) != from) return false;
		if (ISFILE(h) && (FROM(m) & 7) != h - 'a') return false;
		if (ISRANK(h) && (FROM(m) & 56) != 8*(h - '1')) return false;
		if (prom != 0 && PROM(m) != prom) return false;
		return true;
	}

	static int parseMove(String s, int c, int p) {
		int i, to, from = -1, piece = PAWN, prom = 0;
		char h = 0, c1, c2;
		int[] ip = new int[1];
		if (s.startsWith("O-O-O")) s = c != 0 ? "Kc8" : "Kc1";
		else if (s.startsWith("O-O")) s = c != 0 ? "Kg8" : "Kg1";
		int sp = 0;
		try {
			if (s.charAt(sp) >= 'A' && s.charAt(sp) <= 'Z') if ((piece = _getpiece(s.charAt(sp++), ip)) < 1) return -1;
			if (s.charAt(sp) == 'x') sp++;
			if (ISRANK(s.charAt(sp))) { h = s.charAt(sp++); if (s.charAt(sp) == 'x') sp++; }
			if (!ISFILE(s.charAt(sp))) return -1;
			c1 = s.charAt(sp++);
			if (s.charAt(sp) == 'x') sp++;
			if (ISFILE(s.charAt(sp))) {h = c1; c1 = s.charAt(sp++);}
			c2 = s.charAt(sp++);
			if (!ISRANK(c2)) return -1;
			if (s.length() > sp) {
				if (s.charAt(sp) == '=') prom = _getpiece(s.charAt(sp + 1), ip);
				else if (s.charAt(sp) == '+');
				else { // Algebraic Notation
					from = c1 - 'a' + 8*(c2 - '1');
					c1 = s.charAt(sp++);
					c2 = s.charAt(sp++);
					if (!ISFILE(c1) || !ISRANK(c2)) return -1;
					if (s.length() > sp) prom = _getpiece(s.charAt(sp), ip);
				}
			}
			to = c1 - 'a' + 8*(c2 - '1');
			if (p != 0) {
				if (ismove(p, to, from, piece, prom, h)) return p;
				return 0;
			}
			Movep mp = Movep.get(0); generate(attacked(kingpos[c], c), c, mp, true, true);
			for (i = 0; i < mp.n; i++) if (ismove(mp.list[i], to, from, piece, prom, h)) return mp.list[i];
		} catch (StringIndexOutOfBoundsException e) {
		}
		return 0;
	}

	static int parseMoveNExec(String s, int c) {
		int m = parseMove(s, c, 0);
		if (m == -1) printf("UNKNOWN COMMAND: " + s + "\n");
		else if (m == 0) errprintf("Illegal move: " + s + "\n");
		else return execMove(m);
		sendBoard(ONMV(m));
		return -1;
	}

	static void undo() {
		int i, cnt = COUNT() - 1;
		if (cnt < 0) return;
		onmove ^= 1;
		int m = (int)(mstack[cnt] >> 27L);
		undoMove(m, onmove);
		for (i = 1; i < 127; i++) pv[0][i] = pv[0][i-1];
		pv[0][0] = m;
	}

	static void displaym(int m) {
		printf(String.valueOf((char)('a' + FROM(m) % 8)) + String.valueOf((char)('1' + FROM(m) / 8))
			+ String.valueOf((char)('a' + TO(m) % 8)) + String.valueOf((char)('1' + TO(m) / 8)));
		if (PROM(m) != 0) printf(String.valueOf((char)(pieceChar.charAt(PROM(m))+32)));
	}

	static void displaypv() {
		int i;
		if (pon != 0 && pondering) { printf("("); displaym(pon); printf(") "); }
		for (i = 0; pv[0][i] != 0; i++) {
			displaym(pv[0][i]); printf(" ");
		}
	}

	static int calc(int tm) {
		int i, j, w, d; 
		int m2go = mps == 0 ? 32 : 1 + mps - ((COUNT()/2) % mps);
		long t1 = 0, tmsh = Math.max(tm*8L-50-mps*5, 10);
		long searchtime = Math.min(tm*6L/m2go + inc*1000L, tmsh);
		maxtime = Math.min(searchtime*5L, tmsh);
		if (st > 0) maxtime = searchtime = st*1000L;

		starttime = getTime();
		long ch = attacked(kingpos[onmove], onmove);
		Arrays.fill(history, 0);
		Arrays.fill(killer, 0);

		sabort = w = d = 0;
		eval1 = qnodes = nodes = 0L;
		if (book) {
			if (bkcount[onmove] == 0) book = false;
			else {
				j = (int)(hashxor[(int)starttime & 4095] & 0xFFFFFF) % bkcount[onmove];
				for (i = 0; i < BKSIZE; i++) {
					if (bkflag[i] == onmove && j == d++) { pv[0][0] = bkmove[i*32 + COUNT()]; break; }
				}
			}
		}
		if (!book || analyze) for (d = 1; d <= sd; d++) {
			int alpha = d > 6 ? w - 13 : -MAXSCORE, beta = d > 6 ? w + 13: MAXSCORE, delta = 18;
			int bestm = pv[0][0];

			for(;;) {
				if (alpha < -pval[QUEEN]*2) alpha = -MAXSCORE;
				if (beta > pval[QUEEN]*2) beta = MAXSCORE;

				w = search(ch, onmove, d, 0, alpha, beta, false);
				if (sabort != 0) break;

				if (w <= alpha) { alpha -= delta; beta = (alpha + beta)/2; }
				else if (w >= beta) beta += delta;
				else break;
				delta += delta * 2 / 3;
			}

			t1 = (int)(getTime() - starttime);
			if (post && pv[0][0] != 0 && (sabort == 0 || (sabort >= 1 && !analyze)) && w > -MAXSCORE) {
				printf(String.format("%2d %5d %6d %9d  ", d, MEVAL(w), t1/10, nodes + qnodes));
				displaypv(); printf("\n");
			}
			if (sabort != 0) break;
			if (pondering) continue;
			if (d >= MAXSCORE - w) break;
			if (t1 < searchtime || d == 1) continue;

			if (bestm == pv[0][0] || t1 > searchtime*2) break;
		}
		if (analyze) return 1;
		pondering = false;
		if (sabort < -1) { pon = 0; return sabort; }
		if (pon != 0) {
			undo();
			pon = 0;
			return engine != onmove ? 1 : 0;
		}
		printf("move "); displaym(pv[0][0]); printf("\n");

		if (post && ics) printf("kibitz W: " + MEVAL(w)
				+ " Nodes: " + nodes
				+ " QNodes: " + qnodes
				+ " Evals: " + eval1
				+ " cs: " + t1/10
				+ " knps: "+ (nodes+qnodes)/(t1+1) + "\n");
		return execMove(pv[0][0]);
	}

	static int doponder(int c) {
		pon = retPVMove(c, 0);
		if (pon != 0) {
			pondering = true;
			if (execMove(pon) != 0) {
				pondering = false;
				undo();
				pon = 0;
			}
		}
		return pondering ? 0 : -1;
	}

	static long perft(int c, int d, int div) {
		int i;
		long n, cnt = 0L;

		Movep mp = Movep.get(d); generate(attacked(kingpos[c], c), c, mp, true, true);
		if (d == 1 || bioskey()) return (long)mp.n;
		for (i = 0; i < mp.n; i++) {
			int m = mp.list[i];
			doMove(m, c);
			cnt += n = perft(c^1, d - 1, 0);
			if (div != 0) { displaym(m); printf(" " + n + "\n"); }
			undoMove(m, c);
		}
		return cnt;
	}

	static void newGame() {
		_readbook("olibook.pgn");
		engine = 1;
	}

	static int protV2(String buf, boolean parse) {
		if (buf.startsWith("protover")) printf("feature setboard=1 myname=\"OliThink " + VER
				+ "\" colors=0 analyze=1 ping=1 sigint=0 sigterm=0 done=1\n");
		else if (buf.startsWith("xboard"));
		else if (buf.startsWith("ping")) printf(buf.replace("ping", "pong") + "\n");
		else if (buf.startsWith("quit")) return -2;
		else if (buf.startsWith("new")) return -3;
		else if (buf.startsWith("remove")) return -4;
		else if (buf.startsWith("force")) return -7;
		else if (buf.startsWith("go")) engine = pondering ? onmove^1 : onmove;
		else if (buf.startsWith("setboard")) if (parse) _parse_fen(buf.substring(9), true); else return -9;
		else if (buf.startsWith("undo")) return -8;
		else if (buf.startsWith("easy")) ponder = false;
		else if (buf.startsWith("hard")) ponder = true;
		else if (buf.startsWith("analyze")) return -5;
		else if (buf.startsWith("exit")) return -6;	
		else if (buf.startsWith("sd")) sd = Integer.parseInt(buf.substring(3));
		else if (buf.startsWith("time")) time = Integer.parseInt(buf.substring(5));
		else if (buf.startsWith("level")) {
			StringTokenizer st = new StringTokenizer(buf.substring(6), " ");
			mps = Integer.parseInt(st.nextToken());
			base = st.nextToken();
			inc = Integer.parseInt(st.nextToken());
		}
		else if (buf.startsWith("post")) post = true;
		else if (buf.startsWith("nopost")) post = false;
		else if (buf.startsWith("result")) return -6;//result 0-1 {Black mates}
		else if (buf.startsWith("otim"));//otim <optime>
		else if (buf.startsWith("draw"));//draw offer
		else if (buf.startsWith("st")) st = Integer.parseInt(buf.substring(3));
		else if (buf.startsWith("?")) return 1;
		else if (buf.startsWith("."));
		else if (buf.startsWith("bk"));
		else if (buf.startsWith("hint"));
		else if (buf.startsWith("computer"));
		else if (buf.startsWith("accepted") || buf.startsWith("rejected"));//accepted/rejected <feature>
		else if (buf.startsWith("random"));
		else if (buf.startsWith("rating")) ics = true;//ICS: rating <myrat> <oprat>
		else if (buf.startsWith("name"));//ICS: name <opname>
		else if (buf.startsWith("perft")) {
			int i; for (i = 1; i <= sd; i++) printf("Depth: " + i + " Nodes: " + perft(onmove, i, 0) + "\n");}
		else if (buf.startsWith("divide")) perft(onmove, sd, 1);
		else if (buf.contains("/")) {
			engine = -1; analyze = pondering = true; if (parse) _parse_fen(buf, true); else return -9; } 
		else if (buf.length() == 0);
		else return -1;
		return 0;
	}

	static StringBuffer sbuf = new StringBuffer();
	static ConcurrentLinkedDeque<String> inString = new ConcurrentLinkedDeque<String>();

	static void readln() {
		char c = 0;
		while (c != '\n') {
		try {
				c = (char) System.in.read();
			} catch (IOException e) {
		 		e.printStackTrace();
			}
			if (c != '\n' && c!= '\r') sbuf.append(c);
		}

		inString.add(sbuf.toString());
		sbuf.setLength(0);
	}

	static void writeLog(String s) {
		try {
			java.io.FileWriter w = new java.io.FileWriter("/tmp/olithink.log", true);
			w.write(s);
			w.close();
		} catch (java.io.IOException io) {
			io.printStackTrace();
		}
	}

	static int input(int c) {
		String buf;
		if (irbuf.length() > 0) {
			buf = irbuf.toString();
		} else {
			while (inString.isEmpty()) try {
				Thread.sleep(10);
			} catch (InterruptedException e) {
				e.printStackTrace();
			}

			buf = inString.pollFirst();
		}
		irbuf.setLength(0);
		int ex = protV2(buf, true);
		if (ex == -1) return parseMoveNExec(buf, c);
		return ex;
	}
	/**
	 * @param args
	 */
	public static void main(String[] args) {
		int i, ex = -1; long m, n;

		ReadThread read = new ReadThread();
		read.start();

		for (i = 4096, n = 1, m = 6364136223846793005L; i-- != 0; hashxor[4095-i] = n = n*m +1L);
		for (i = 0; i < 64; i++) BIT[i] = 1L << i;
		for (i = 0; i < 64; i++) pmoves[0][i] = pawnfree[0][i] = pawnfile[0][i] = pawnhelp[0][i] = 0L;
		for (i = 0; i < 192; i++) pcaps[0][i] = 0L;
		for (i = 0; i < 64; i++) pmoves[1][i] = pawnfree[1][i] = pawnfile[1][i] = pawnhelp[1][i] = 0L;
		for (i = 0; i < 192; i++) pcaps[1][i] = 0L;
		for (i = 0; i < 64; i++) bmask45[i] = _bishop45(i, 0L, 0) | BIT[i];
		for (i = 0; i < 64; i++) bmask135[i] = _bishop135(i, 0L, 0) | BIT[i];
		for (i = 0; i < 64; i++) { crevoke[i] = 0x3FF; rankb[i/8] |= BIT[i]; fileb[i&7] |= BIT[i]; }
		for (i = 0; i < 64; i++) kmoves[i] = nmoves[i] = 0L;
		for (i = 0; i < 64; i++) if ((i/8)%2 != (i&7)%2) whitesq |= BIT[i];
		crevoke[7] ^= BIT[6];
		crevoke[63] ^= BIT[7];
		crevoke[0] ^= BIT[8];
		crevoke[56] ^= BIT[9];

		try {
			_init_rays(0, otclass, "_rook0", "key000");
			_init_rays(0x2000, otclass, "_rook90", "key090");
			_init_rays(0x4000, otclass, "_bishop45", "key045");
			_init_rays(0x6000, otclass, "_bishop135", "key135");
		} catch (Exception e) { e.printStackTrace(); }
		_init_shorts(nmoves, _knight);
		_init_shorts(kmoves, _king);
		_init_pawns(pmoves[0], pcaps[0], pawnfree[0], pawnfile[0], pawnhelp[0], 0);
		_init_pawns(pmoves[1], pcaps[1], pawnfree[1], pawnfile[1], pawnhelp[1], 1);

		for (i = 0; i < 64; i++) nmobil[i] = (bitcnt(nmoves[i]))*8;
		for (i = 0; i < 64; i++) kmobil[i] = Math.max(bitcnt(nmoves[i]), 3);
		for (i = 0; i < 32; i++) 
			bishcorn[i] = bishcorn[63-i] = (i&7) < 4 ? cornbase[(i&7) +i/8] : -cornbase[7 -(i&7) +i/8];
		newGame();

		if (args.length > 0 && "-sd".equals(args[0])) {
			time = 99999999;
			if (args.length > 1) {
				sd = Integer.parseInt(args[1]);
				if (args.length > 2) { _parse_fen(args[2], true); calc(time); System.exit(0); }
			}
		}

		for (;;) {
			if (engine == onmove || analyze) ex = calc(time);
			else if (ex == 0 && ponder && engine != -1 && !book) ex = doponder(onmove);

			if (!ponder || book || engine == -1 || ex != 0) ex = input(onmove);
			if (ex == -2) break;
			if (ex == -3) newGame();
			if (ex == -4) { undo(); undo(); }
			if (ex == -5) { analyze = pondering = true; engine = -1; }
			if (ex == -6) pondering = analyze = false;
			if (ex == -7) { pondering = false; engine = -1; }
			if (ex == -8) undo();
		}
		read.stop = true;
		System.exit(0);
	}

	static void receiveCommand(String cmd) {
		inString.add(cmd);
	}

	static boolean identColor(int f) {
		return (colorb[1] & BIT[f]) != 0;
	}

	static void sendMove(int m, boolean engine) {
		if (engine) {
			OliThinkFrame.engineMove(FROM(m) % 8, FROM(m) / 8, TO(m) % 8, TO(m) / 8);
		}
		try {
			Thread.sleep(20);
			sendBoard(ONMV(m)^1);
		} catch (InterruptedException e) {
		}
	}

	static void sendBoard(int c) {
		String fen = "";
		int i, j;
		for (i = 0; i < 8; i++) {
			int ws = 0;
			for (j = 0; j < 8; j++) {
				int f = j + (7-i)*8;
				char p = (char)(pieceChar.charAt(identPiece(f)) + (identColor(f) ? 32 : 0));
				if (p == '.') { ws++; continue; } else if (ws > 0) { fen+= String.valueOf(ws); ws = 0; }
				fen += String.valueOf(p);
			} fen += ( ws > 0 ? String.valueOf(ws) : "") + (i < 7 ? "/" : "");
		}
		//printf(fen + (c != 0 ? " b" : " w") + "\n");
		OliThinkFrame.parsePos(fen);
	}
}