60440000  RALO(Lb,68)
62070000  RALO(Ob,7)
54000061  LDLO(L0,97)
54040073  LDLO(L1,115)
54080001  LDLO(L2,1)
540c0018  LDLO(L3,24)
64100c04  BALO(L4,L3,1)
5414032e  LDLO(L5,814)
54180000  LDLO(L6,0)
74141018  BSET(L5,L4,L6)
541c0003  LDLO(L7,3)
54200376  LDLO(L8,886)
74201008  BSET(L8,L4,L2)
54240005  LDLO(L9,5)
542803a6  LDLO(L10,934)
542c0002  LDLO(L11,2)
7428102c  BSET(L10,L4,L11)
7414101c  BSET(L5,L4,L7)
54300396  LDLO(L12,918)
54340004  LDLO(L13,4)
74301034  BSET(L12,L4,L13)
54380106  LDLO(L14,262)
74381024  BSET(L14,L4,L9)
543c039e  LDLO(L15,926)
54400006  LDLO(L16,6)
743c1040  BSET(L15,L4,L16)
5444034e  LDLO(L17,846)
54480007  LDLO(L18,7)
74441048  BSET(L17,L4,L18)
544c03d6  LDLO(L19,982)
54500008  LDLO(L20,8)
744c1050  BSET(L19,L4,L20)
54540009  LDLO(L21,9)
74141054  BSET(L5,L4,L21)
5458000a  LDLO(L22,10)
74381058  BSET(L14,L4,L22)
545c0146  LDLO(L23,326)
5460000b  LDLO(L24,11)
745c1060  BSET(L23,L4,L24)
54640186  LDLO(L25,390)
5468000c  LDLO(L26,12)
74641068  BSET(L25,L4,L26)
546c000d  LDLO(L27,13)
7438106c  BSET(L14,L4,L27)
5470000e  LDLO(L28,14)
74281070  BSET(L10,L4,L28)
5474037e  LDLO(L29,894)
5478000f  LDLO(L30,15)
74741078  BSET(L29,L4,L30)
547c0010  LDLO(L31,16)
7438107c  BSET(L14,L4,L31)
54800011  LDLO(L32,17)
74141080  BSET(L5,L4,L32)
548403c6  LDLO(L33,966)
54880012  LDLO(L34,18)
74841088  BSET(L33,L4,L34)
548c0013  LDLO(L35,19)
7444108c  BSET(L17,L4,L35)
54900014  LDLO(L36,20)
74281090  BSET(L10,L4,L36)
5494014e  LDLO(L37,334)
54980015  LDLO(L38,21)
74941098  BSET(L37,L4,L38)
549c01f6  LDLO(L39,502)
54a00016  LDLO(L40,22)
749c10a0  BSET(L39,L4,L40)
54a40017  LDLO(L41,23)
743810a4  BSET(L14,L4,L41)
54a80778  LDLO(L42,1912)
5f901000  MOVE(O4,L4)
48a80000  CALL(L42)
5cab8000  MOVE(L42,O0)
78ac0000  BREA(L43)
14b0ac08  ASL(L44,L43,L2)
20b4b008  OR(L45,L44,L2)
14b8b42c  ASL(L46,L45,L11)
20bcb82c  OR(L47,L46,L11)
54c8016e  LDLO(L50,366)
34bcc8de  JNE(L47,L50,222)
64c80b28  BALO(L50,L2,202)
54cc0c00  LDLO(L51,3072)
74ccc818  BSET(L51,L50,L6)
5cc0c800  MOVE(L48,L50)
5cc40800  MOVE(L49,L2)
78c80000  BREA(L50)
14ccc808  ASL(L51,L50,L2)
20d0cc08  OR(L52,L51,L2)
14d4d02c  ASL(L53,L52,L11)
20d8d42c  OR(L54,L53,L11)
54dc04f8  LDLO(L55,1272)
5f900000  MOVE(O4,L0)
5f940400  MOVE(O5,L1)
5f98d800  MOVE(O6,L54)
48dc0000  CALL(L55)
5cdf8000  MOVE(L55,O0)
30dc580f  JEQ(L55,L22,15)
18dcc408  ASR(L55,L49,L2)
08e090dc  MUL(L56,L36,L55)
00e4e008  ADD(L57,L56,L2)
18e8d82c  ASR(L58,L54,L11)
04ece800  SUB(L59,L58,L0)
00f0ec08  ADD(L60,L59,L2)
70f4c018  BGET(L61,L48,L6)
5f90c000  MOVE(O4,L48)
5f94e400  MOVE(O5,L57)
5f98f000  MOVE(O6,L60)
48f40000  CALL(L61)
5cf78000  MOVE(L61,O0)
5cc4f400  MOVE(L49,L61)
43ffffe7  JI(-25)
5ca8c400  MOVE(L42,L49)
30a808bc  JEQ(L42,L2,188)
64ac2c0c  BALO(L43,L11,3)
741cac18  BSET(L7,L43,L6)
64b01808  BALO(L44,L6,2)
74b0ac08  BSET(L44,L43,L2)
54b40848  LDLO(L45,2120)
5f90ac00  MOVE(O4,L43)
5f94a800  MOVE(O5,L42)
48b40000  CALL(L45)
5caf8000  MOVE(L43,O0)
54b00614  LDLO(L44,1556)
5f90ac00  MOVE(O4,L43)
48b00000  CALL(L44)
5cb38000  MOVE(L44,O0)
34b0081f  JNE(L44,L2,31)
64b08804  BALO(L44,L34,1)
7420b018  BSET(L8,L44,L6)
7474b008  BSET(L29,L44,L2)
7438b02c  BSET(L14,L44,L11)
743cb01c  BSET(L15,L44,L7)
7474b034  BSET(L29,L44,L13)
54b40366  LDLO(L45,870)
74b4b024  BSET(L45,L44,L9)
54b803ae  LDLO(L46,942)
74b8b040  BSET(L46,L44,L16)
7428b048  BSET(L10,L44,L18)
7444b050  BSET(L17,L44,L20)
7474b054  BSET(L29,L44,L21)
7420b058  BSET(L8,L44,L22)
7438b060  BSET(L14,L44,L24)
54bc0336  LDLO(L47,822)
74bcb068  BSET(L47,L44,L26)
7474b06c  BSET(L29,L44,L27)
74b8b070  BSET(L46,L44,L28)
7420b078  BSET(L8,L44,L30)
54c00326  LDLO(L48,806)
74c0b07c  BSET(L48,L44,L31)
54c4010e  LDLO(L49,270)
74c4b080  BSET(L49,L44,L32)
54c80778  LDLO(L50,1912)
5f90b000  MOVE(O4,L44)
48c80000  CALL(L50)
5ccb8000  MOVE(L50,O0)
7c580000  BWRI(L22)
43ffff69  JI(-151)
64b00b28  BALO(L44,L2,202)
54b40b00  LDLO(L45,2816)
74b4b018  BSET(L45,L44,L6)
64b41808  BALO(L45,L6,2)
5cb8b000  MOVE(L46,L44)
5cbcb400  MOVE(L47,L45)
5cc0ac00  MOVE(L48,L43)
6cc4c000  BTAG(L49,L48)
14c8c408  ASL(L50,L49,L2)
20ccc808  OR(L51,L50,L2)
34cc247a  JNE(L51,L9,122)
54c40614  LDLO(L49,1556)
5f90ac00  MOVE(O4,L43)
48c40000  CALL(L49)
5cc78000  MOVE(L49,O0)
5cc8bc00  MOVE(L50,L47)
5cccc400  MOVE(L51,L49)
54d00614  LDLO(L52,1556)
5f90c800  MOVE(O4,L50)
48d00000  CALL(L52)
5cd38000  MOVE(L52,O0)
34d0cc6d  JNE(L52,L51,109)
7c580000  BWRI(L22)
54d00614  LDLO(L52,1556)
5f90c800  MOVE(O4,L50)
48d00000  CALL(L52)
5cd38000  MOVE(L52,O0)
54d40530  LDLO(L53,1328)
5f900000  MOVE(O4,L0)
5f94d000  MOVE(O5,L52)
48d40000  CALL(L53)
5cd78000  MOVE(L53,O0)
64d45404  BALO(L53,L21,1)
54d8016e  LDLO(L54,366)
74d8d418  BSET(L54,L53,L6)
54dc038e  LDLO(L55,910)
74dcd408  BSET(L55,L53,L2)
54e003ae  LDLO(L56,942)
74e0d42c  BSET(L56,L53,L11)
7414d41c  BSET(L5,L53,L7)
7414d434  BSET(L5,L53,L13)
7420d424  BSET(L8,L53,L9)
745cd440  BSET(L23,L53,L16)
743cd448  BSET(L15,L53,L18)
7494d450  BSET(L37,L53,L20)
54e40778  LDLO(L57,1912)
5f90d400  MOVE(O4,L53)
48e40000  CALL(L57)
5ce78000  MOVE(L57,O0)
7c580000  BWRI(L22)
64e44004  BALO(L57,L16,1)
54e80366  LDLO(L58,870)
74e8e418  BSET(L58,L57,L6)
7444e408  BSET(L17,L57,L2)
743ce42c  BSET(L15,L57,L11)
7428e41c  BSET(L10,L57,L7)
54ec01d6  LDLO(L59,470)
74ece434  BSET(L59,L57,L13)
7438e424  BSET(L14,L57,L9)
54f00778  LDLO(L60,1912)
5f90e400  MOVE(O4,L57)
48f00000  CALL(L60)
5cf38000  MOVE(L60,O0)
54f00028  LDLO(L60,40)
7cf00000  BWRI(L60)
64f42f28  BALO(L61,L11,202)
54f80b94  LDLO(L62,2964)
74f8f418  BSET(L62,L61,L6)
7400f408  BSET(L0,L61,L2)
5cf8f400  MOVE(L62,L61)
5cfcc800  MOVE(L63,L50)
6d00fc00  BTAG(L64,L63)
15050008  ASL(L65,L64,L2)
21090408  OR(L66,L65,L2)
3508242f  JNE(L66,L9,47)
55000029  LDLO(L64,41)
7d000000  BWRI(L64)
7c580000  BWRI(L22)
55040614  LDLO(L65,1556)
5f90c800  MOVE(O4,L50)
49040000  CALL(L65)
5d078000  MOVE(L65,O0)
65080b28  BALO(L66,L2,202)
550c0bcc  LDLO(L67,3020)
750d0818  BSET(L67,L66,L6)
550c0aac  LDLO(L67,2732)
5f900800  MOVE(O4,L2)
5f950400  MOVE(O5,L65)
5f990800  MOVE(O6,L66)
490c0000  CALL(L67)
5d0f8000  MOVE(L67,O0)
7c580000  BWRI(L22)
5cd02c00  MOVE(L52,L11)
6cd0c800  BTAG(L52,L50)
14d4d008  ASL(L53,L52,L2)
20d8d408  OR(L54,L53,L2)
34d82403  JNE(L54,L9,3)
7c580000  BWRI(L22)
43ffff06  JI(-250)
70d0c818  BGET(L52,L50,L6)
64d42f28  BALO(L53,L11,202)
54d80b24  LDLO(L54,2852)
74d8d418  BSET(L54,L53,L6)
74d0d408  BSET(L52,L53,L2)
54d80aac  LDLO(L54,2732)
5f900800  MOVE(O4,L2)
5f94cc00  MOVE(O5,L51)
5f98d400  MOVE(O6,L53)
48d80000  CALL(L54)
5cdb8000  MOVE(L54,O0)
64d80804  BALO(L54,L2,1)
54dc03e6  LDLO(L55,998)
74dcd818  BSET(L55,L54,L6)
54e00778  LDLO(L56,1912)
5f90d800  MOVE(O4,L54)
48e00000  CALL(L56)
5ce38000  MOVE(L56,O0)
7c580000  BWRI(L22)
70e0c808  BGET(L56,L50,L2)
5cc8e000  MOVE(L50,L56)
43ffff99  JI(-103)
7100fc18  BGET(L64,L63,L6)
7104f818  BGET(L65,L62,L6)
5f90f800  MOVE(O4,L62)
5f950000  MOVE(O5,L64)
49040000  CALL(L65)
5d078000  MOVE(L65,O0)
7104fc08  BGET(L65,L63,L2)
5cfd0400  MOVE(L63,L65)
43ffffc6  JI(-58)
5cd02c00  MOVE(L52,L11)
43ffffda  JI(-38)
70c4c018  BGET(L49,L48,L6)
70c8b818  BGET(L50,L46,L6)
5f90b800  MOVE(O4,L46)
5f94bc00  MOVE(O5,L47)
5f98c400  MOVE(O6,L49)
48c80000  CALL(L50)
5ccb8000  MOVE(L50,O0)
70ccc008  BGET(L51,L48,L2)
5cbcc800  MOVE(L47,L50)
5cc0cc00  MOVE(L48,L51)
43ffff79  JI(-135)
50180000  HALT(L6)
54c804f8  LDLO(L50,1272)
5f900000  MOVE(O4,L0)
5f940400  MOVE(O5,L1)
5f98bc00  MOVE(O6,L47)
48c80000  CALL(L50)
5ccb8000  MOVE(L50,O0)
30c8580a  JEQ(L50,L22,10)
64c80b28  BALO(L50,L2,202)
54cc0c18  LDLO(L51,3096)
74ccc818  BSET(L51,L50,L6)
18ccbc2c  ASR(L51,L47,L11)
04d0cc00  SUB(L52,L51,L0)
00d4d008  ADD(L53,L52,L2)
5cc0c800  MOVE(L48,L50)
5cc4d400  MOVE(L49,L53)
43ffff19  JI(-231)
5ca80800  MOVE(L42,L2)
43ffff32  JI(-206)
60020000  RALO(Lb,2)
54000002  LDLO(L0,2)
18071800  ASR(L1,I6,L0)
3f100408  JGT(I4,L1,8)
3c071404  JGT(L1,I5,4)
5400001a  LDLO(L0,26)
5f100000  MOVE(I4,L0)
4c000000  RET
5400000a  LDLO(L0,10)
5f100000  MOVE(I4,L0)
4c000000  RET
5400000a  LDLO(L0,10)
5f100000  MOVE(I4,L0)
4c000000  RET
60020000  RALO(Lb,2)
62060000  RALO(Ob,6)
54000001  LDLO(L0,1)
3b140010  JGE(I5,L0,16)
5400002d  LDLO(L0,45)
7c000000  BWRI(L0)
54000002  LDLO(L0,2)
54000001  LDLO(L0,1)
3b140005  JGE(I5,L0,5)
54000584  LDLO(L0,1412)
5f931000  MOVE(O4,I4)
5f971400  MOVE(O5,I5)
44000000  TCAL(L0)
54000002  LDLO(L0,2)
04040314  SUB(L1,L0,I5)
54000584  LDLO(L0,1412)
5f931000  MOVE(O4,I4)
5f940400  MOVE(O5,L1)
44000000  TCAL(L0)
54000002  LDLO(L0,2)
43fffff3  JI(-13)
60050000  RALO(Lb,5)
62060000  RALO(Ob,6)
5403ffed  LDLO(L0,-19)
3f14001e  JGT(I5,L0,30)
54000013  LDLO(L0,19)
00071400  ADD(L1,I5,L0)
54000001  LDLO(L0,1)
04080400  SUB(L2,L1,L0)
04040800  SUB(L1,L2,L0)
5408000a  LDLO(L2,10)
0c0c0408  DIV(L3,L1,L2)
20040c00  OR(L1,L3,L0)
54000584  LDLO(L0,1412)
5f931000  MOVE(O4,I4)
5f940400  MOVE(O5,L1)
48000000  CALL(L0)
5c038000  MOVE(L0,O0)
54000002  LDLO(L0,2)
04040314  SUB(L1,L0,I5)
54080001  LDLO(L2,1)
040c0408  SUB(L3,L1,L2)
54040014  LDLO(L1,20)
10100c04  MOD(L4,L3,L1)
00041008  ADD(L1,L4,L2)
000c0710  ADD(L3,L1,I4)
04040c08  SUB(L1,L3,L2)
140c0400  ASL(L3,L1,L0)
20040c00  OR(L1,L3,L0)
180c0400  ASR(L3,L1,L0)
18040c08  ASR(L1,L3,L2)
7c040000  BWRI(L1)
5f100000  MOVE(I4,L0)
4c000000  RET
54000002  LDLO(L0,2)
5f800000  MOVE(O0,L0)
43ffffed  JI(-19)
60040000  RALO(Lb,4)
62050000  RALO(Ob,5)
6c031000  BTAG(L0,I4)
54040001  LDLO(L1,1)
14080004  ASL(L2,L0,L1)
20000804  OR(L0,L2,L1)
54040005  LDLO(L1,5)
34000404  JNE(L0,L1,4)
54000001  LDLO(L0,1)
5f100000  MOVE(I4,L0)
4c000000  RET
54000003  LDLO(L0,3)
54040001  LDLO(L1,1)
700b1004  BGET(L2,I4,L1)
540c0614  LDLO(L3,1556)
5f900800  MOVE(O4,L2)
480c0000  CALL(L3)
5c0b8000  MOVE(L2,O0)
000c0008  ADD(L3,L0,L2)
04000c04  SUB(L0,L3,L1)
5f100000  MOVE(I4,L0)
4c000000  RET
60030000  RALO(Lb,3)
62060000  RALO(Ob,6)
6c031400  BTAG(L0,I5)
54040001  LDLO(L1,1)
14080004  ASL(L2,L0,L1)
20000804  OR(L0,L2,L1)
54040005  LDLO(L1,5)
34000404  JNE(L0,L1,4)
5400001a  LDLO(L0,26)
5f100000  MOVE(I4,L0)
4c000000  RET
54000000  LDLO(L0,0)
70071400  BGET(L1,I5,L0)
700b1000  BGET(L2,I4,L0)
5f931000  MOVE(O4,I4)
5f940400  MOVE(O5,L1)
48080000  CALL(L2)
5c038000  MOVE(L0,O0)
5404000a  LDLO(L1,10)
30000407  JEQ(L0,L1,7)
54000001  LDLO(L0,1)
70071400  BGET(L1,I5,L0)
5400066c  LDLO(L0,1644)
5f931000  MOVE(O4,I4)
5f940400  MOVE(O5,L1)
44000000  TCAL(L0)
5400000a  LDLO(L0,10)
5f100000  MOVE(I4,L0)
4c000000  RET
60060000  RALO(Lb,6)
62060000  RALO(Ob,6)
6c031000  BTAG(L0,I4)
54040001  LDLO(L1,1)
14080004  ASL(L2,L0,L1)
20000804  OR(L0,L2,L1)
54040005  LDLO(L1,5)
34000405  JNE(L0,L1,5)
54000000  LDLO(L0,0)
64040008  BALO(L1,L0,2)
5f100400  MOVE(I4,L1)
4c000000  RET
6c031400  BTAG(L0,I5)
54040001  LDLO(L1,1)
14080004  ASL(L2,L0,L1)
20000804  OR(L0,L2,L1)
54040005  LDLO(L1,5)
300007f7  JEQ(L0,L1,-9)
54000002  LDLO(L0,2)
6404000c  BALO(L1,L0,3)
64080000  BALO(L2,L0,0)
54000000  LDLO(L0,0)
700f1000  BGET(L3,I4,L0)
740c0800  BSET(L3,L2,L0)
700f1400  BGET(L3,I5,L0)
54100001  LDLO(L4,1)
740c0810  BSET(L3,L2,L4)
74080400  BSET(L2,L1,L0)
70031010  BGET(L0,I4,L4)
700b1410  BGET(L2,I5,L4)
540c06e0  LDLO(L3,1760)
5f900000  MOVE(O4,L0)
5f940800  MOVE(O5,L2)
480c0000  CALL(L3)
5c038000  MOVE(L0,O0)
74000410  BSET(L0,L1,L4)
5f100400  MOVE(I4,L1)
4c000000  RET
600e0000  RALO(Lb,14)
54000003  LDLO(L0,3)
54040001  LDLO(L1,1)
640807c8  BALO(L2,L1,242)
540c0000  LDLO(L3,0)
7404080c  BSET(L1,L2,L3)
54100002  LDLO(L4,2)
7010080c  BGET(L4,L2,L3)
68171000  BSIZ(L5,I4)
14181404  ASL(L6,L5,L1)
201c1804  OR(L7,L6,L1)
38101c0e  JGE(L4,L7,14)
7010080c  BGET(L4,L2,L3)
18141004  ASR(L5,L4,L1)
701b1014  BGET(L6,I4,L5)
541c0002  LDLO(L7,2)
1820181c  ASR(L8,L6,L7)
18242004  ASR(L9,L8,L1)
7c240000  BWRI(L9)
7028080c  BGET(L10,L2,L3)
002c2800  ADD(L11,L10,L0)
04302c04  SUB(L12,L11,L1)
7430080c  BSET(L12,L2,L3)
5c101c00  MOVE(L4,L7)
43ffffef  JI(-17)
54000002  LDLO(L0,2)
5f100000  MOVE(I4,L0)
4c000000  RET
60060000  RALO(Lb,6)
62060000  RALO(Ob,6)
54000000  LDLO(L0,0)
70071000  BGET(L1,I4,L0)
38071410  JGE(L1,I5,16)
54000001  LDLO(L0,1)
54040002  LDLO(L1,2)
6408040c  BALO(L2,L1,3)
54040003  LDLO(L1,3)
540c0000  LDLO(L3,0)
7013100c  BGET(L4,I4,L3)
00140410  ADD(L5,L1,L4)
04041400  SUB(L1,L5,L0)
7404080c  BSET(L1,L2,L3)
70071000  BGET(L1,I4,L0)
74040800  BSET(L1,L2,L0)
54000848  LDLO(L0,2120)
5f900800  MOVE(O4,L2)
5f971400  MOVE(O5,I5)
44000000  TCAL(L0)
54000000  LDLO(L0,0)
64040008  BALO(L1,L0,2)
5f100400  MOVE(I4,L1)
4c000000  RET
60150000  RALO(Lb,21)
62060000  RALO(Ob,6)
5c031000  MOVE(L0,I4)
6c040000  BTAG(L1,L0)
54080001  LDLO(L2,1)
140c0408  ASL(L3,L1,L2)
20100c08  OR(L4,L3,L2)
54140005  LDLO(L5,5)
34101458  JNE(L4,L5,88)
5c031000  MOVE(L0,I4)
6c040000  BTAG(L1,L0)
54080001  LDLO(L2,1)
140c0408  ASL(L3,L1,L2)
20100c08  OR(L4,L3,L2)
54140005  LDLO(L5,5)
3410141e  JNE(L4,L5,30)
54000614  LDLO(L0,1556)
5f931000  MOVE(O4,I4)
48000000  CALL(L0)
5c038000  MOVE(L0,O0)
34031402  JNE(L0,I5,2)
4c000000  RET
54000005  LDLO(L0,5)
54040001  LDLO(L1,1)
54080002  LDLO(L2,2)
640c080c  BALO(L3,L2,3)
54080003  LDLO(L2,3)
54100000  LDLO(L4,0)
74080c10  BSET(L2,L3,L4)
77100c04  BSET(I4,L3,L1)
54080848  LDLO(L2,2120)
5f900c00  MOVE(O4,L3)
5f971400  MOVE(O5,I5)
48080000  CALL(L2)
5c0b8000  MOVE(L2,O0)
6c0c0800  BTAG(L3,L2)
14100c04  ASL(L4,L3,L1)
200c1004  OR(L3,L4,L1)
340c0005  JNE(L3,L0,5)
540007e8  LDLO(L0,2024)
5f931000  MOVE(O4,I4)
5f971400  MOVE(O5,I5)
44000000  TCAL(L0)
5f100800  MOVE(I4,L2)
4c000000  RET
54040002  LDLO(L1,2)
64080728  BALO(L2,L1,202)
540c0000  LDLO(L3,0)
54100a24  LDLO(L4,2596)
7410080c  BSET(L4,L2,L3)
54100001  LDLO(L4,1)
74000810  BSET(L0,L2,L4)
54140003  LDLO(L5,3)
70180010  BGET(L6,L0,L4)
541c0614  LDLO(L7,1556)
5f901800  MOVE(O4,L6)
481c0000  CALL(L7)
5c1f8000  MOVE(L7,O0)
04201c14  SUB(L8,L7,L5)
00242010  ADD(L9,L8,L4)
00282414  ADD(L10,L9,L5)
042c2810  SUB(L11,L10,L4)
64300c08  BALO(L12,L3,2)
5c342c00  MOVE(L13,L11)
5c383000  MOVE(L14,L12)
34341015  JNE(L13,L4,21)
543c06e0  LDLO(L15,1760)
5f901800  MOVE(O4,L6)
5f943800  MOVE(O5,L14)
483c0000  CALL(L15)
5c1f8000  MOVE(L7,O0)
5420066c  LDLO(L8,1644)
5f900800  MOVE(O4,L2)
5f941c00  MOVE(O5,L7)
48200000  CALL(L8)
5c238000  MOVE(L8,O0)
5424000a  LDLO(L9,10)
30202405  JEQ(L8,L9,5)
54040001  LDLO(L1,1)
70080004  BGET(L2,L0,L1)
5c000800  MOVE(L0,L2)
43ffffb9  JI(-71)
540007e8  LDLO(L0,2024)
5f931000  MOVE(O4,I4)
5f971400  MOVE(O5,I5)
44000000  TCAL(L0)
043c3414  SUB(L15,L13,L5)
00403c10  ADD(L16,L15,L4)
6444040c  BALO(L17,L1,3)
00481440  ADD(L18,L5,L16)
044c4810  SUB(L19,L18,L4)
744c440c  BSET(L19,L17,L3)
74384410  BSET(L14,L17,L4)
5c344000  MOVE(L13,L16)
5c384400  MOVE(L14,L17)
43ffffe2  JI(-30)
54040002  LDLO(L1,2)
64080728  BALO(L2,L1,202)
540c0000  LDLO(L3,0)
54100a7c  LDLO(L4,2684)
7410080c  BSET(L4,L2,L3)
54100001  LDLO(L4,1)
74000810  BSET(L0,L2,L4)
70140010  BGET(L5,L0,L4)
5418066c  LDLO(L6,1644)
5f900800  MOVE(O4,L2)
5f941400  MOVE(O5,L5)
48180000  CALL(L6)
5c1b8000  MOVE(L6,O0)
541c000a  LDLO(L7,10)
30181c05  JEQ(L6,L7,5)
54040001  LDLO(L1,1)
70080004  BGET(L2,L0,L1)
5c000800  MOVE(L0,L2)
43ffff91  JI(-111)
540007e8  LDLO(L0,2024)
5f931000  MOVE(O4,I4)
5f971400  MOVE(O5,I5)
44000000  TCAL(L0)
60060000  RALO(Lb,6)
54000001  LDLO(L0,1)
70071000  BGET(L1,I4,L0)
54080000  LDLO(L2,0)
700c0408  BGET(L3,L1,L2)
70071408  BGET(L1,I5,L2)
700b1400  BGET(L2,I5,L0)
00100c08  ADD(L4,L3,L2)
04141000  SUB(L5,L4,L0)
34140404  JNE(L5,L1,4)
5400000a  LDLO(L0,10)
5f100000  MOVE(I4,L0)
4c000000  RET
04100c08  SUB(L4,L3,L2)
00081000  ADD(L2,L4,L0)
34080404  JNE(L2,L1,4)
5400000a  LDLO(L0,10)
5f100000  MOVE(I4,L0)
4c000000  RET
5400001a  LDLO(L0,26)
5f100000  MOVE(I4,L0)
4c000000  RET
60030000  RALO(Lb,3)
54000001  LDLO(L0,1)
70071000  BGET(L1,I4,L0)
54000000  LDLO(L0,0)
70080400  BGET(L2,L1,L0)
300b1404  JEQ(L2,I5,4)
5400001a  LDLO(L0,26)
5f100000  MOVE(I4,L0)
4c000000  RET
5400000a  LDLO(L0,10)
5f100000  MOVE(I4,L0)
4c000000  RET
60030000  RALO(Lb,3)
62070000  RALO(Ob,7)
3b131410  JGE(I4,I5,16)
54000000  LDLO(L0,0)
70071800  BGET(L1,I6,L0)
5f931800  MOVE(O4,I6)
5f971000  MOVE(O5,I4)
48040000  CALL(L1)
5c038000  MOVE(L0,O0)
54000003  LDLO(L0,3)
00071000  ADD(L1,I4,L0)
54000001  LDLO(L0,1)
04080400  SUB(L2,L1,L0)
54000aac  LDLO(L0,2732)
5f900800  MOVE(O4,L2)
5f971400  MOVE(O5,I5)
5f9b1800  MOVE(O6,I6)
44000000  TCAL(L0)
54000002  LDLO(L0,2)
5f100000  MOVE(I4,L0)
4c000000  RET
60030000  RALO(Lb,3)
54000002  LDLO(L0,2)
6404000c  BALO(L1,L0,3)
54000000  LDLO(L0,0)
77180400  BSET(I6,L1,L0)
54000001  LDLO(L0,1)
77140400  BSET(I5,L1,L0)
5f100400  MOVE(I4,L1)
4c000000  RET
60070000  RALO(Lb,7)
62050000  RALO(Ob,5)
54000001  LDLO(L0,1)
70071000  BGET(L1,I4,L0)
54080003  LDLO(L2,3)
640c0004  BALO(L3,L0,1)
541003e6  LDLO(L4,998)
54140000  LDLO(L5,0)
74100c14  BSET(L4,L3,L5)
54100778  LDLO(L4,1912)
5f900c00  MOVE(O4,L3)
48100000  CALL(L4)
5c0f8000  MOVE(L3,O0)
000f1408  ADD(L3,I5,L2)
04080c00  SUB(L2,L3,L0)
34080407  JNE(L2,L1,7)
64040004  BALO(L1,L0,1)
5400037e  LDLO(L0,894)
74000414  BSET(L0,L1,L5)
54000778  LDLO(L0,1912)
5f900400  MOVE(O4,L1)
44000000  TCAL(L0)
64040004  BALO(L1,L0,1)
54000106  LDLO(L0,262)
74000414  BSET(L0,L1,L5)
54000778  LDLO(L0,1912)
5f900400  MOVE(O4,L1)
44000000  TCAL(L0)
60020000  RALO(Lb,2)
62060000  RALO(Ob,6)
54000001  LDLO(L0,1)
70071000  BGET(L1,I4,L0)
54000530  LDLO(L0,1328)
5f900400  MOVE(O4,L1)
5f971400  MOVE(O5,I5)
48000000  CALL(L0)
5c038000  MOVE(L0,O0)
54000020  LDLO(L0,32)
7c000000  BWRI(L0)
54000002  LDLO(L0,2)
5f100000  MOVE(I4,L0)
4c000000  RET
60040000  RALO(Lb,4)
62050000  RALO(Ob,5)
54000002  LDLO(L0,2)
64040004  BALO(L1,L0,1)
54000106  LDLO(L0,262)
54080000  LDLO(L2,0)
74000408  BSET(L0,L1,L2)
540002fe  LDLO(L0,766)
54080001  LDLO(L2,1)
74000408  BSET(L0,L1,L2)
54000778  LDLO(L0,1912)
5f900400  MOVE(O4,L1)
44000000  TCAL(L0)
60030000  RALO(Lb,3)
04031718  SUB(L0,I5,I6)
54040001  LDLO(L1,1)
00080004  ADD(L2,L0,L1)
5f100800  MOVE(I4,L2)
4c000000  RET
60030000  RALO(Lb,3)
00031718  ADD(L0,I5,I6)
54040001  LDLO(L1,1)
04080004  SUB(L2,L0,L1)
5f100800  MOVE(I4,L2)
4c000000  RET
