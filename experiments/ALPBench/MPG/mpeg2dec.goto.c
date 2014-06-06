// c::__signbitl::1::tag-#anon0
// 
union anon$4;

// c::__signbitl::1::tag-#anon0$link1
// 
union anon$4$link1;

// c::tag-#anon#ST[*{U8}'frame_buf'||U32'frame_buf_size'||U32'frame_buf_offset'||ARR0000000000000000000000000000000000000000000000000000000000010100{U8}'padding'||U32'$pad0'|]
// 
struct anon$0;

// c::tag-#anon#ST[S32'id'||S32'num_slices'||S32'framenum'||S32'MBAmax'|]
// 
struct anon$2;

// c::tag-#anon#ST[S8'run'||S8'level'||S8'len'|]
// 
struct anon$1;

// c::tag-#anon#ST[S8'val'||S8'len'|]
// 
struct anon$3;

// c::tag-_IO_FILE
// file /usr/include/libio.h line 246
struct _IO_FILE;

// c::tag-_IO_FILE$link10
// file /usr/include/libio.h line 246
struct _IO_FILE$link10;

// c::tag-_IO_FILE$link11
// file /usr/include/libio.h line 246
struct _IO_FILE$link11;

// c::tag-_IO_FILE$link12
// file /usr/include/libio.h line 246
struct _IO_FILE$link12;

// c::tag-_IO_FILE$link13
// file /usr/include/libio.h line 246
struct _IO_FILE$link13;

// c::tag-_IO_FILE$link3
// file /usr/include/libio.h line 246
struct _IO_FILE$link3;

// c::tag-_IO_FILE$link4
// file /usr/include/libio.h line 246
struct _IO_FILE$link4;

// c::tag-_IO_FILE$link5
// file /usr/include/libio.h line 246
struct _IO_FILE$link5;

// c::tag-_IO_FILE$link6
// file /usr/include/libio.h line 246
struct _IO_FILE$link6;

// c::tag-_IO_FILE$link7
// file /usr/include/libio.h line 246
struct _IO_FILE$link7;

// c::tag-_IO_FILE$link8
// file /usr/include/libio.h line 246
struct _IO_FILE$link8;

// c::tag-_IO_FILE$link9
// file /usr/include/libio.h line 246
struct _IO_FILE$link9;

// c::tag-_IO_marker
// file /usr/include/libio.h line 161
struct _IO_marker;

// c::tag-_IO_marker$link10
// file /usr/include/libio.h line 161
struct _IO_marker$link10;

// c::tag-_IO_marker$link11
// file /usr/include/libio.h line 161
struct _IO_marker$link11;

// c::tag-_IO_marker$link12
// file /usr/include/libio.h line 161
struct _IO_marker$link12;

// c::tag-_IO_marker$link13
// file /usr/include/libio.h line 161
struct _IO_marker$link13;

// c::tag-_IO_marker$link14
// file /usr/include/libio.h line 161
struct _IO_marker$link14;

// c::tag-_IO_marker$link15
// file /usr/include/libio.h line 161
struct _IO_marker$link15;

// c::tag-_IO_marker$link5
// file /usr/include/libio.h line 161
struct _IO_marker$link5;

// c::tag-_IO_marker$link6
// file /usr/include/libio.h line 161
struct _IO_marker$link6;

// c::tag-_IO_marker$link7
// file /usr/include/libio.h line 161
struct _IO_marker$link7;

// c::tag-_IO_marker$link8
// file /usr/include/libio.h line 161
struct _IO_marker$link8;

// c::tag-_IO_marker$link9
// file /usr/include/libio.h line 161
struct _IO_marker$link9;

// c::tag-layer_data
// file src/global.h line 515
struct layer_data;

// c::tag-pthread_attr_t
// file /usr/include/x86_64-linux-gnu/bits/pthreadtypes.h line 63
union pthread_attr_t;

// c::tag-thrd_layer_data
// file src/global.h line 624
struct thrd_layer_data;


#include <assert.h>
#ifndef TRUE
#define TRUE (_Bool)1
#endif
#ifndef FALSE
#define FALSE (_Bool)0
#endif
#ifndef NULL
#define NULL ((void*)0)
#endif
#ifndef FENCE
#define FENCE(x) ((void)0)
#endif
#ifndef IEEE_FLOAT_EQUAL
#define IEEE_FLOAT_EQUAL(x,y) (x==y)
#endif
#ifndef IEEE_FLOAT_NOTEQUAL
#define IEEE_FLOAT_NOTEQUAL(x,y) (x!=y)
#endif

// c::Clear_Block
// file src/getpic.c line 727
static void Clear_Block(signed int comp);
// c::Clear_Options
// file src/mpeg2dec.c line 791
static void Clear_Options();
// c::Copy_Frame
// file src/subspic.c line 401
static void Copy_Frame(unsigned char *src, unsigned char *dst, signed int width, signed int height, signed int parity, signed int field_mode);
// c::Decode_Bitstream
// file src/mpeg2dec.c line 679
static signed int Decode_Bitstream(void);
// c::Decode_MPEG1_Intra_Block
// file src/getblk.c line 99
void Decode_MPEG1_Intra_Block(signed int comp, signed int *dc_dct_pred);
// c::Decode_MPEG1_Non_Intra_Block
// file src/getblk.c line 206
void Decode_MPEG1_Non_Intra_Block(signed int comp);
// c::Decode_MPEG2_Intra_Block
// file src/getblk.c line 302
void Decode_MPEG2_Intra_Block(signed int comp, signed int *dc_dct_pred);
// c::Decode_MPEG2_Non_Intra_Block
// file src/getblk.c line 475
void Decode_MPEG2_Non_Intra_Block(signed int comp);
// c::Decode_Picture
// file src/getpic.c line 155
void Decode_Picture(signed int bitstream_framenum, signed int sequence_framenum);
// c::Decode_SNR_Macroblock
// file src/getpic.c line 616
static void Decode_SNR_Macroblock(signed int *SNRMBA, signed int *SNRMBAinc, signed int MBA, signed int MBAmax, signed int *dct_type);
// c::Deinitialize_Sequence
// file src/mpeg2dec.c line 706
static void Deinitialize_Sequence(void);
// c::Deinterlace
// file src/spatscal.c line 298
static void Deinterlace(unsigned char *fld0, unsigned char *fld1, signed int j0, signed int lx, signed int ly, signed int aperture);
// c::Dual_Prime_Arithmetic
// file src/motion.c line 246
void Dual_Prime_Arithmetic(signed int (*DMV)[2l], signed int *dmvector, signed int mvx, signed int mvy);
// c::Error
// file src/global.h line 181
void Error(char *text);
// c::Extract_Components
// file src/subspic.c line 334
static signed int Extract_Components(char *filename, unsigned char **frame, signed int framenum);
// c::Fast_IDCT
// file src/global.h line 158
void Fast_IDCT(signed short int *block);
// c::Fill_Buffer
// file src/getbits.c line 115
void Fill_Buffer(void);
// c::Flush_Buffer
// file src/getbits.c line 191
void Flush_Buffer(signed int N);
// c::Flush_Buffer32
// file src/global.h line 121
void Flush_Buffer32(void);
// c::Get_B_Spatial_macroblock_type
// file src/getvlc.c line 364
static signed int Get_B_Spatial_macroblock_type(void);
// c::Get_B_macroblock_type
// file src/getvlc.c line 226
static signed int Get_B_macroblock_type(void);
// c::Get_Bits
// file src/getbits.c line 245
unsigned int Get_Bits(signed int N);
// c::Get_Bits1
// file src/getbits.c line 183
unsigned int Get_Bits1(void);
// c::Get_Bits32
// file src/global.h line 122
unsigned int Get_Bits32(void);
// c::Get_Byte
// file src/getbits.c line 151
signed int Get_Byte(void);
// c::Get_Chroma_DC_dct_diff
// file src/global.h line 155
signed int Get_Chroma_DC_dct_diff(void);
// c::Get_D_macroblock_type
// file src/getvlc.c line 272
static signed int Get_D_macroblock_type(void);
// c::Get_Hdr
// file src/gethdr.c line 145
signed int Get_Hdr(void);
// c::Get_I_Spatial_macroblock_type
// file src/getvlc.c line 285
static signed int Get_I_Spatial_macroblock_type(void);
// c::Get_I_macroblock_type
// file src/getvlc.c line 138
static signed int Get_I_macroblock_type(void);
// c::Get_Long
// file src/systems.c line 243
signed int Get_Long(void);
// c::Get_Luma_DC_dct_diff
// file src/global.h line 154
signed int Get_Luma_DC_dct_diff(void);
// c::Get_P_Spatial_macroblock_type
// file src/getvlc.c line 316
static signed int Get_P_Spatial_macroblock_type(void);
// c::Get_P_macroblock_type
// file src/getvlc.c line 182
static signed int Get_P_macroblock_type(void);
// c::Get_SNR_macroblock_type
// file src/getvlc.c line 403
static signed int Get_SNR_macroblock_type(void);
// c::Get_Word
// file src/getbits.c line 163
signed int Get_Word(void);
// c::Get_coded_block_pattern
// file src/global.h line 152
signed int Get_coded_block_pattern(void);
// c::Get_dmvector
// file src/getvlc.c line 512
signed int Get_dmvector(void);
// c::Get_macroblock_address_increment
// file src/global.h line 153
signed int Get_macroblock_address_increment(void);
// c::Get_macroblock_type
// file src/global.h line 149
signed int Get_macroblock_type(void);
// c::Get_motion_code
// file src/getvlc.c line 436
signed int Get_motion_code(void);
// c::Headers
// file src/mpeg2dec.c line 653
static signed int Headers(void);
// c::Initialize_Buffer
// file src/getbits.c line 96
void Initialize_Buffer(void);
// c::Initialize_Decoder
// file src/mpeg2dec.c line 232
static void Initialize_Decoder(void);
// c::Initialize_Fast_IDCT
// file src/idct.c line 1020
void Initialize_Fast_IDCT(void);
// c::Initialize_Frame_Buffer
// file src/mpeg2dec.c line 215
static void Initialize_Frame_Buffer(void);
// c::Initialize_Reference_IDCT
// file src/idctref.c line 112
void Initialize_Reference_IDCT();
// c::Initialize_Sequence
// file src/mpeg2dec.c line 254
static void Initialize_Sequence(void);
// c::Make_Spatial_Prediction_Frame
// file src/spatscal.c line 204
static void Make_Spatial_Prediction_Frame(signed int progressive_frame, signed int llprogressive_frame, unsigned char *fld0, unsigned char *fld1, signed short int *tmp, unsigned char *dst, signed int llx0, signed int lly0, signed int llw, signed int llh, signed int horizontal_size, signed int vertical_size, signed int vm, signed int vn, signed int hm, signed int hn, signed int aperture);
// c::Next_Packet
// file src/global.h line 119
void Next_Packet(void);
// c::Output_Last_Frame_of_Sequence
// file src/getpic.c line 944
void Output_Last_Frame_of_Sequence(signed int Framenum);
// c::Print_Bits
// file src/mpeg2dec.c line 351
void Print_Bits(signed int code, signed int bits, signed int len);
// c::Process_Options
// file src/mpeg2dec.c line 362
static void Process_Options(signed int argc, char **argv);
// c::Read_Component
// file src/subspic.c line 293
static signed int Read_Component(char *Filename, unsigned char *Frame, signed int Width, signed int Height);
// c::Read_Components
// file src/subspic.c line 267
static signed int Read_Components(char *filename, unsigned char **frame, signed int framenum);
// c::Read_Frame
// file src/subspic.c line 207
static void Read_Frame(char *fname, unsigned char **frame, signed int framenum);
// c::Read_Lower_Layer_Component_Fieldwise
// file src/spatscal.c line 163
static void Read_Lower_Layer_Component_Fieldwise(signed int comp, signed int lw, signed int lh);
// c::Read_Lower_Layer_Component_Framewise
// file src/spatscal.c line 132
static void Read_Lower_Layer_Component_Framewise(signed int comp, signed int lw, signed int lh);
// c::Reference_IDCT
// file src/global.h line 163
void Reference_IDCT(signed short int *block);
// c::Saturate
// file src/getpic.c line 783
static void Saturate(signed short int *Block_Ptr);
// c::Show_Bits
// file src/getbits.c line 174
unsigned int Show_Bits(signed int N);
// c::Spatial_Prediction
// file src/global.h line 191
void Spatial_Prediction(void);
// c::Subsample_Horizontal
// file src/spatscal.c line 354
static void Subsample_Horizontal(signed short int *s, unsigned char *d, signed int x0, signed int lx, signed int lxs, signed int lxd, signed int ly, signed int m, signed int n);
// c::Subsample_Vertical
// file src/spatscal.c line 331
static void Subsample_Vertical(unsigned char *s, signed short int *d, signed int lx, signed int lys, signed int lyd, signed int m, signed int n, signed int j0, signed int dj);
// c::Substitute_Frame_Buffer
// file src/global.h line 96
void Substitute_Frame_Buffer(signed int bitstream_framenum, signed int sequence_framenum);
// c::Sum_Block
// file src/getpic.c line 766
static void Sum_Block(signed int comp);
// c::Thrd_Add_Block
// file src/getpic.c line 2302
static void Thrd_Add_Block(signed int t, signed int comp, signed int bx, signed int by, signed int dct_type, signed int addflag);
// c::Thrd_Clear_Block
// file src/getpic.c line 2263
static void Thrd_Clear_Block(signed int t, signed int comp);
// c::Thrd_Decode_MPEG2_Intra_Block
// file src/getblk.c line 626
void Thrd_Decode_MPEG2_Intra_Block(signed int t, signed int comp, signed int *dc_dct_pred);
// c::Thrd_Decode_MPEG2_Non_Intra_Block
// file src/getblk.c line 751
void Thrd_Decode_MPEG2_Non_Intra_Block(signed int t, signed int comp);
// c::Thrd_Flush_Buffer
// file src/getbits.c line 306
void Thrd_Flush_Buffer(signed int t, signed int N);
// c::Thrd_Flush_Buffer32
// file src/global.h line 125
void Thrd_Flush_Buffer32(signed int t);
// c::Thrd_Get_B_macroblock_type
// file src/getvlc.c line 939
static signed int Thrd_Get_B_macroblock_type(signed int t);
// c::Thrd_Get_Bits
// file src/getbits.c line 339
unsigned int Thrd_Get_Bits(signed int t, signed int N);
// c::Thrd_Get_Bits1
// file src/getbits.c line 298
unsigned int Thrd_Get_Bits1(signed int t);
// c::Thrd_Get_Bits32
// file src/systems.c line 286
unsigned int Thrd_Get_Bits32(signed int t);
// c::Thrd_Get_Byte
// file src/getbits.c line 271
signed int Thrd_Get_Byte(signed int t);
// c::Thrd_Get_Chroma_DC_dct_diff
// file src/global.h line 210
signed int Thrd_Get_Chroma_DC_dct_diff(signed int t);
// c::Thrd_Get_D_macroblock_type
// file src/getvlc.c line 965
static signed int Thrd_Get_D_macroblock_type(signed int t);
// c::Thrd_Get_I_macroblock_type
// file src/getvlc.c line 895
static signed int Thrd_Get_I_macroblock_type(signed int t);
// c::Thrd_Get_Long
// file src/systems.c line 297
signed int Thrd_Get_Long(signed int t);
// c::Thrd_Get_Luma_DC_dct_diff
// file src/global.h line 209
signed int Thrd_Get_Luma_DC_dct_diff(signed int t);
// c::Thrd_Get_P_macroblock_type
// file src/getvlc.c line 913
static signed int Thrd_Get_P_macroblock_type(signed int t);
// c::Thrd_Get_Word
// file src/getbits.c line 277
signed int Thrd_Get_Word(signed int t);
// c::Thrd_Get_coded_block_pattern
// file src/global.h line 211
signed int Thrd_Get_coded_block_pattern(signed int t);
// c::Thrd_Get_dmvector
// file src/getvlc.c line 1073
signed int Thrd_Get_dmvector(signed int t);
// c::Thrd_Get_macroblock_address_increment
// file src/global.h line 215
signed int Thrd_Get_macroblock_address_increment(signed int t);
// c::Thrd_Get_macroblock_type
// file src/global.h line 208
signed int Thrd_Get_macroblock_type(signed int t);
// c::Thrd_Get_motion_code
// file src/getvlc.c line 1032
signed int Thrd_Get_motion_code(signed int t);
// c::Thrd_Initialize_Buffer
// file src/getbits.c line 261
void Thrd_Initialize_Buffer(signed int t);
// c::Thrd_Show_Bits
// file src/getbits.c line 288
unsigned int Thrd_Show_Bits(signed int t, signed int N);
// c::Thrd_Work
// file src/getpic.c line 1459
void * Thrd_Work(void *thrd_args);
// c::Thrd_decode_macroblock
// file src/getpic.c line 1833
static signed int Thrd_decode_macroblock(signed int t, signed int *macroblock_type, signed int *stwtype, signed int *stwclass, signed int *motion_type, signed int *dct_type, signed int (*PMV)[2l][2l], signed int *dc_dct_pred, signed int (*motion_vertical_field_select)[2l], signed int *dmvector);
// c::Thrd_extra_bit_information
// file src/gethdr.c line 236
static signed int Thrd_extra_bit_information(signed int t);
// c::Thrd_macroblock_modes
// file src/getpic.c line 2162
static void Thrd_macroblock_modes(signed int t, signed int *pmacroblock_type, signed int *pstwtype, signed int *pstwclass, signed int *pmotion_type, signed int *pmotion_vector_count, signed int *pmv_format, signed int *pdmv, signed int *pmvscale, signed int *pdct_type);
// c::Thrd_motion_compensation
// file src/getpic.c line 2103
static void Thrd_motion_compensation(signed int t, signed int MBA, signed int macroblock_type, signed int motion_type, signed int (*PMV)[2l][2l], signed int (*motion_vertical_field_select)[2l], signed int *dmvector, signed int stwtype, signed int dct_type);
// c::Thrd_motion_vector
// file src/global.h line 176
void Thrd_motion_vector(signed int t, signed int *PMV, signed int *dmvector, signed int h_r_size, signed int v_r_size, signed int dmv, signed int mvscale, signed int full_pel_vector);
// c::Thrd_motion_vectors
// file src/global.h line 173
void Thrd_motion_vectors(signed int t, signed int (*PMV)[2l][2l], signed int *dmvector, signed int (*motion_vertical_field_select)[2l], signed int s, signed int motion_vector_count, signed int mv_format, signed int h_r_size, signed int v_r_size, signed int dmv, signed int mvscale);
// c::Thrd_next_start_code
// file src/gethdr.c line 190
void Thrd_next_start_code(signed int t);
// c::Thrd_skipped_macroblock
// file src/getpic.c line 2051
static void Thrd_skipped_macroblock(signed int t, signed int *dc_dct_pred, signed int (*PMV)[2l][2l], signed int *motion_type, signed int (*motion_vertical_field_select)[2l], signed int *stwtype, signed int *macroblock_type);
// c::Thrd_slice_header
// file src/gethdr.c line 198
signed int Thrd_slice_header(signed int t);
// c::Thrd_start_of_slice
// file src/getpic.c line 1769
static signed int Thrd_start_of_slice(signed int t, signed int MBAmax, signed int *MBA, signed int *MBAinc, signed int *dc_dct_pred, signed int (*PMV)[2l][2l]);
// c::Update_Picture_Buffers
// file src/getpic.c line 897
static void Update_Picture_Buffers(void);
// c::Update_Temporal_Reference_Tacking_Data
// file src/gethdr.c line 1160
static void Update_Temporal_Reference_Tacking_Data(void);
// c::Write_Frame
// file src/global.h line 194
void Write_Frame(unsigned char **src, signed int frame);
// c::_IO_getc
// file /usr/include/libio.h line 435
signed int _IO_getc(struct _IO_FILE *);
// c::_IO_putc
// file /usr/include/libio.h line 436
signed int _IO_putc(signed int, struct _IO_FILE *);
// c::__assert_fail
// file /usr/include/assert.h line 70
void __assert_fail(const char *, const char *, unsigned int, const char *);
// c::__builtin___snprintf_chk
// file gcc_builtin_headers_generic.h line 50
signed int __builtin___snprintf_chk(char *, unsigned long int, signed int, unsigned long int, const char *, ...);
// c::__builtin___sprintf_chk
// file gcc_builtin_headers_generic.h line 49
signed int __builtin___sprintf_chk(char *, signed int, unsigned long int, const char *, ...);
// c::__builtin___vsnprintf_chk
// file gcc_builtin_headers_generic.h line 52
signed int __builtin___vsnprintf_chk(char *, unsigned long int, signed int, unsigned long int, const char *, void **);
// c::__builtin___vsprintf_chk
// file gcc_builtin_headers_generic.h line 51
signed int __builtin___vsprintf_chk(char *, signed int, unsigned long int, const char *, void **);
// c::__builtin_va_arg_pack
// file gcc_builtin_headers_generic.h line 5
void * __builtin_va_arg_pack();
// c::__builtin_va_arg_pack_len
// file gcc_builtin_headers_generic.h line 6
signed int __builtin_va_arg_pack_len();
// c::__confstr_alias
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 231
unsigned long int __confstr_alias(signed int, char *, unsigned long int);
// c::__confstr_chk
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 229
unsigned long int __confstr_chk(signed int, char *, unsigned long int, unsigned long int);
// c::__confstr_chk_warn
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 233
unsigned long int __confstr_chk_warn(signed int, char *, unsigned long int, unsigned long int);
// c::__ctype_tolower_loc
// file /usr/include/ctype.h line 82
const signed int ** __ctype_tolower_loc(void);
// c::__ctype_toupper_loc
// file /usr/include/ctype.h line 84
const signed int ** __ctype_toupper_loc(void);
// c::__dprintf_chk
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 131
signed int __dprintf_chk(signed int, signed int, const char *, ...);
// c::__fgets_alias
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 243
char * __fgets_alias(char *, signed int, struct _IO_FILE *);
// c::__fgets_chk
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 241
char * __fgets_chk(char *, unsigned long int, signed int, struct _IO_FILE *);
// c::__fgets_chk_warn
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 246
char * __fgets_chk_warn(char *, unsigned long int, signed int, struct _IO_FILE *);
// c::__fprintf_chk
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 85
signed int __fprintf_chk(struct _IO_FILE *, signed int, const char *, ...);
// c::__fread_alias
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 269
unsigned long int __fread_alias(void *, unsigned long int, unsigned long int, struct _IO_FILE *);
// c::__fread_chk
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 266
unsigned long int __fread_chk(void *, unsigned long int, unsigned long int, unsigned long int, struct _IO_FILE *);
// c::__fread_chk_warn
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 273
unsigned long int __fread_chk_warn(void *, unsigned long int, unsigned long int, unsigned long int, struct _IO_FILE *);
// c::__fread_unlocked_alias
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 330
unsigned long int __fread_unlocked_alias(void *, unsigned long int, unsigned long int, struct _IO_FILE *);
// c::__fread_unlocked_chk
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 327
unsigned long int __fread_unlocked_chk(void *, unsigned long int, unsigned long int, unsigned long int, struct _IO_FILE *);
// c::__fread_unlocked_chk_warn
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 334
unsigned long int __fread_unlocked_chk_warn(void *, unsigned long int, unsigned long int, unsigned long int, struct _IO_FILE *);
// c::__getcwd_alias
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 191
char * __getcwd_alias(char *, unsigned long int);
// c::__getcwd_chk
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 189
char * __getcwd_chk(char *, unsigned long int, unsigned long int);
// c::__getcwd_chk_warn
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 193
char * __getcwd_chk_warn(char *, unsigned long int, unsigned long int);
// c::__getdomainname_alias
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 362
signed int __getdomainname_alias(char *, unsigned long int);
// c::__getdomainname_chk
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 360
signed int __getdomainname_chk(char *, unsigned long int, unsigned long int);
// c::__getdomainname_chk_warn
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 365
signed int __getdomainname_chk_warn(char *, unsigned long int, unsigned long int);
// c::__getgroups_alias
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 256
signed int __getgroups_alias(signed int, unsigned int *);
// c::__getgroups_chk
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 254
signed int __getgroups_chk(signed int, unsigned int *, unsigned long int);
// c::__getgroups_chk_warn
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 258
signed int __getgroups_chk_warn(signed int, unsigned int *, unsigned long int);
// c::__gethostname_alias
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 335
signed int __gethostname_alias(char *, unsigned long int);
// c::__gethostname_chk
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 333
signed int __gethostname_chk(char *, unsigned long int, unsigned long int);
// c::__gethostname_chk_warn
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 337
signed int __gethostname_chk_warn(char *, unsigned long int, unsigned long int);
// c::__getlogin_r_alias
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 308
signed int __getlogin_r_alias(char *, unsigned long int);
// c::__getlogin_r_chk
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 306
signed int __getlogin_r_chk(char *, unsigned long int, unsigned long int);
// c::__getlogin_r_chk_warn
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 310
signed int __getlogin_r_chk_warn(char *, unsigned long int, unsigned long int);
// c::__gets_chk
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 227
char * __gets_chk(char *, unsigned long int);
// c::__gets_warn
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 228
char * __gets_warn(char *);
// c::__getwd_chk
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 214
char * __getwd_chk(char *, unsigned long int);
// c::__getwd_warn
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 216
char * __getwd_warn(char *);
// c::__mbstowcs_alias
// file /usr/include/x86_64-linux-gnu/bits/stdlib.h line 101
unsigned long int __mbstowcs_alias(signed int *, const char *, unsigned long int);
// c::__mbstowcs_chk
// file /usr/include/x86_64-linux-gnu/bits/stdlib.h line 98
unsigned long int __mbstowcs_chk(signed int *, const char *, unsigned long int, unsigned long int);
// c::__mbstowcs_chk_warn
// file /usr/include/x86_64-linux-gnu/bits/stdlib.h line 105
unsigned long int __mbstowcs_chk_warn(signed int *, const char *, unsigned long int, unsigned long int);
// c::__open_2
// file /usr/include/x86_64-linux-gnu/bits/fcntl2.h line 26
signed int __open_2(const char *, signed int);
// c::__open_alias
// file /usr/include/x86_64-linux-gnu/bits/fcntl2.h line 27
signed int __open_alias(const char *, signed int, ...);
// c::__open_missing_mode
// file /usr/include/x86_64-linux-gnu/bits/fcntl2.h line 37
void __open_missing_mode(void);
// c::__open_too_many_args
// file /usr/include/x86_64-linux-gnu/bits/fcntl2.h line 35
void __open_too_many_args(void);
// c::__openat_2
// file /usr/include/x86_64-linux-gnu/bits/fcntl2.h line 98
signed int __openat_2(signed int, const char *, signed int);
// c::__openat_alias
// file /usr/include/x86_64-linux-gnu/bits/fcntl2.h line 100
signed int __openat_alias(signed int, const char *, signed int, ...);
// c::__openat_missing_mode
// file /usr/include/x86_64-linux-gnu/bits/fcntl2.h line 113
void __openat_missing_mode(void);
// c::__openat_too_many_args
// file /usr/include/x86_64-linux-gnu/bits/fcntl2.h line 111
void __openat_too_many_args(void);
// c::__overflow
// file /usr/include/libio.h line 393
signed int __overflow(struct _IO_FILE *, signed int);
// c::__printf_chk
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 87
signed int __printf_chk(signed int, const char *, ...);
// c::__ptsname_r_alias
// file /usr/include/x86_64-linux-gnu/bits/stdlib.h line 54
signed int __ptsname_r_alias(signed int, char *, unsigned long int);
// c::__ptsname_r_chk
// file /usr/include/x86_64-linux-gnu/bits/stdlib.h line 52
signed int __ptsname_r_chk(signed int, char *, unsigned long int, unsigned long int);
// c::__ptsname_r_chk_warn
// file /usr/include/x86_64-linux-gnu/bits/stdlib.h line 57
signed int __ptsname_r_chk_warn(signed int, char *, unsigned long int, unsigned long int);
// c::__read_alias
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 25
signed long int __read_alias(signed int, void *, unsigned long int);
// c::__read_chk
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 23
signed long int __read_chk(signed int, void *, unsigned long int, unsigned long int);
// c::__read_chk_warn
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 27
signed long int __read_chk_warn(signed int, void *, unsigned long int, unsigned long int);
// c::__readlink_alias
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 127
signed long int __readlink_alias(const char *, char *, unsigned long int);
// c::__readlink_chk
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 123
signed long int __readlink_chk(const char *, char *, unsigned long int, unsigned long int);
// c::__readlink_chk_warn
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 131
signed long int __readlink_chk_warn(const char *, char *, unsigned long int, unsigned long int);
// c::__readlinkat_alias
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 159
signed long int __readlinkat_alias(signed int, const char *, char *, unsigned long int);
// c::__readlinkat_chk
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 155
signed long int __readlinkat_chk(signed int, const char *, char *, unsigned long int, unsigned long int);
// c::__readlinkat_chk_warn
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 164
signed long int __readlinkat_chk_warn(signed int, const char *, char *, unsigned long int, unsigned long int);
// c::__realpath_alias
// file /usr/include/x86_64-linux-gnu/bits/stdlib.h line 26
char * __realpath_alias(const char *, char *);
// c::__realpath_chk
// file /usr/include/x86_64-linux-gnu/bits/stdlib.h line 23
char * __realpath_chk(const char *, char *, unsigned long int);
// c::__signbit
// file /usr/include/x86_64-linux-gnu/bits/mathinline.h line 139
signed int __signbit(double __x);
// c::__signbitf
// file /usr/include/x86_64-linux-gnu/bits/mathinline.h line 127
signed int __signbitf(float __x);
// c::__signbitl
// file /usr/include/x86_64-linux-gnu/bits/mathinline.h line 151
signed int __signbitl(long double __x);
// c::__ttyname_r_alias
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 281
signed int __ttyname_r_alias(signed int, char *, unsigned long int);
// c::__ttyname_r_chk
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 279
signed int __ttyname_r_chk(signed int, char *, unsigned long int, unsigned long int);
// c::__ttyname_r_chk_warn
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 284
signed int __ttyname_r_chk_warn(signed int, char *, unsigned long int, unsigned long int);
// c::__uflow
// file /usr/include/libio.h line 392
signed int __uflow(struct _IO_FILE *);
// c::__vdprintf_chk
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 133
signed int __vdprintf_chk(signed int, signed int, const char *, void **);
// c::__vfprintf_chk
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 88
signed int __vfprintf_chk(struct _IO_FILE *, signed int, const char *, void **);
// c::__wcstombs_alias
// file /usr/include/x86_64-linux-gnu/bits/stdlib.h line 133
unsigned long int __wcstombs_alias(char *, const signed int *, unsigned long int);
// c::__wcstombs_chk
// file /usr/include/x86_64-linux-gnu/bits/stdlib.h line 130
unsigned long int __wcstombs_chk(char *, const signed int *, unsigned long int, unsigned long int);
// c::__wcstombs_chk_warn
// file /usr/include/x86_64-linux-gnu/bits/stdlib.h line 137
unsigned long int __wcstombs_chk_warn(char *, const signed int *, unsigned long int, unsigned long int);
// c::__wctomb_alias
// file /usr/include/x86_64-linux-gnu/bits/stdlib.h line 79
signed int __wctomb_alias(char *, signed int);
// c::__wctomb_chk
// file /usr/include/x86_64-linux-gnu/bits/stdlib.h line 77
signed int __wctomb_chk(char *, signed int, unsigned long int);
// c::atof
// file /usr/include/x86_64-linux-gnu/bits/stdlib-float.h line 26
double atof(const char *__nptr);
// c::atoi
// file /usr/include/stdlib.h line 278
signed int atoi(const char *__nptr);
// c::atol
// file /usr/include/stdlib.h line 283
signed long int atol(const char *__nptr);
// c::atoll
// file /usr/include/stdlib.h line 292
signed long long int atoll(const char *__nptr);
// c::close
// file /usr/include/unistd.h line 353
signed int close(signed int);
// c::confstr
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 240
unsigned long int confstr(signed int __name, char *__buf, unsigned long int __len);
// c::conv420to422
// file src/store.c line 579
static void conv420to422(unsigned char *src, unsigned char *dst);
// c::conv422to444
// file src/store.c line 509
static void conv422to444(unsigned char *src, unsigned char *dst);
// c::copyright_extension
// file src/gethdr.c line 1112
static void copyright_extension(void);
// c::cos
// file /usr/include/x86_64-linux-gnu/bits/mathcalls.h line 63
double cos(double);
// c::decode_motion_vector
// file src/motion.c line 219
static void decode_motion_vector(signed int *pred, signed int r_size, signed int motion_code, signed int motion_residual, signed int full_pel_vector);
// c::dprintf
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 139
signed int dprintf(signed int __fd, const char * restrict __fmt, ...);
// c::exit
// file /usr/include/stdlib.h line 542
void exit(signed int);
// c::extension_and_user_data
// file src/gethdr.c line 510
static void extension_and_user_data(void);
// c::extra_bit_information
// file src/gethdr.c line 1066
static signed int extra_bit_information(void);
// c::fclose
// file /usr/include/stdio.h line 237
signed int fclose(struct _IO_FILE$link10 *);
// c::feof_unlocked
// file /usr/include/x86_64-linux-gnu/bits/stdio.h line 125
signed int feof_unlocked(struct _IO_FILE *__stream);
// c::ferror_unlocked
// file /usr/include/x86_64-linux-gnu/bits/stdio.h line 132
signed int ferror_unlocked(struct _IO_FILE *__stream);
// c::fgetc
// file /usr/include/stdio.h line 531
signed int fgetc(struct _IO_FILE$link10 *);
// c::fgetc_unlocked
// file /usr/include/x86_64-linux-gnu/bits/stdio.h line 53
signed int fgetc_unlocked(struct _IO_FILE *__fp);
// c::fgets
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 253
char * fgets(char * restrict __s, signed int __n, struct _IO_FILE * restrict __stream);
// c::floor
// file /usr/include/x86_64-linux-gnu/bits/mathcalls.h line 185
double floor(double);
// c::fopen
// file /usr/include/stdio.h line 272
struct _IO_FILE$link10 * fopen(const char *, const char *);
// c::form_component_prediction
// file src/recon.c line 437
static void form_component_prediction(unsigned char *src, unsigned char *dst, signed int lx, signed int lx2, signed int w, signed int h, signed int x, signed int y, signed int dx, signed int dy, signed int average_flag);
// c::form_component_prediction2
// file src/recon.c line 992
static void form_component_prediction2(unsigned char *src, unsigned char *dst, signed int lx, signed int lx2, signed int w, signed int h, signed int dx, signed int dy, signed int average_flag);
// c::form_prediction
// file src/recon.c line 326
static void form_prediction(unsigned char **src, signed int sfield, unsigned char **dst, signed int dfield, signed int lx, signed int lx2, signed int w, signed int h, signed int x, signed int y, signed int dx, signed int dy, signed int average_flag);
// c::form_predictions
// file src/global.h line 186
void form_predictions(signed int bx, signed int by, signed int macroblock_type, signed int motion_type, signed int (*PMV)[2l][2l], signed int (*motion_vertical_field_select)[2l], signed int *dmvector, signed int stwtype);
// c::fprintf
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 95
signed int fprintf(struct _IO_FILE * restrict __stream, const char * restrict __fmt, ...);
// c::fputc_unlocked
// file /usr/include/x86_64-linux-gnu/bits/stdio.h line 88
signed int fputc_unlocked(signed int __c, struct _IO_FILE *__stream);
// c::frame_reorder
// file src/getpic.c line 955
static void frame_reorder(signed int Bitstream_Framenum, signed int Sequence_Framenum);
// c::fread
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 282
unsigned long int fread(void * restrict __ptr, unsigned long int __size, unsigned long int __n, struct _IO_FILE * restrict __stream);
// c::fread_unlocked
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 343
unsigned long int fread_unlocked(void * restrict __ptr, unsigned long int __size, unsigned long int __n, struct _IO_FILE * restrict __stream);
// c::free
// file /usr/include/stdlib.h line 482
void free(void *);
// c::fseek
// file /usr/include/stdio.h line 749
signed int fseek(struct _IO_FILE$link12 *, signed long int, signed int);
// c::getc_unlocked
// file /usr/include/x86_64-linux-gnu/bits/stdio.h line 63
signed int getc_unlocked(struct _IO_FILE *__fp);
// c::getchar
// file /usr/include/x86_64-linux-gnu/bits/stdio.h line 44
signed int getchar(void);
// c::getchar_unlocked
// file /usr/include/x86_64-linux-gnu/bits/stdio.h line 70
signed int getchar_unlocked(void);
// c::getcwd
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 200
char * getcwd(char *__buf, unsigned long int __size);
// c::getdomainname
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 373
signed int getdomainname(char *__buf, unsigned long int __buflen);
// c::getgroups
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 265
signed int getgroups(signed int __size, unsigned int *__list);
// c::gethostname
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 344
signed int gethostname(char *__buf, unsigned long int __buflen);
// c::getlogin_r
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 317
signed int getlogin_r(char *__buf, unsigned long int __buflen);
// c::gets
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 233
char * gets(char *__str);
// c::getwd
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 221
char * getwd(char *__buf);
// c::gnu_dev_major
// file /usr/include/x86_64-linux-gnu/sys/sysmacros.h line 44
unsigned int gnu_dev_major(unsigned long long int __dev);
// c::gnu_dev_makedev
// file /usr/include/x86_64-linux-gnu/sys/sysmacros.h line 56
unsigned long long int gnu_dev_makedev(unsigned int __major, unsigned int __minor);
// c::gnu_dev_minor
// file /usr/include/x86_64-linux-gnu/sys/sysmacros.h line 50
unsigned int gnu_dev_minor(unsigned long long int __dev);
// c::group_of_pictures_header
// file src/gethdr.c line 332
static void group_of_pictures_header(void);
// c::idct_M128ASM_scalar
// file src/idct.c line 750
static void idct_M128ASM_scalar(signed short int *src);
// c::lseek
// file /usr/include/unistd.h line 334
signed long int lseek(signed int, signed long int, signed int);
// c::macroblock_modes
// file src/getpic.c line 363
static void macroblock_modes(signed int *pmacroblock_type, signed int *pstwtype, signed int *pstwclass, signed int *pmotion_type, signed int *pmotion_vector_count, signed int *pmv_format, signed int *pdmv, signed int *pmvscale, signed int *pdct_type);
// c::malloc
// file /usr/include/stdlib.h line 465
void * malloc(unsigned long int);
// c::marker_bit
// file src/gethdr.c line 1084
void marker_bit(char *text);
// c::mbstowcs
// file /usr/include/x86_64-linux-gnu/bits/stdlib.h line 113
unsigned long int mbstowcs(signed int * restrict __dst, const char * restrict __src, unsigned long int __len);
// c::motion_vector
// file src/motion.c line 144
void motion_vector(signed int *PMV, signed int *dmvector, signed int h_r_size, signed int v_r_size, signed int dmv, signed int mvscale, signed int full_pel_vector);
// c::motion_vectors
// file src/motion.c line 91
void motion_vectors(signed int (*PMV)[2l][2l], signed int *dmvector, signed int (*motion_vertical_field_select)[2l], signed int s, signed int motion_vector_count, signed int mv_format, signed int h_r_size, signed int v_r_size, signed int dmv, signed int mvscale);
// c::new_slice
// file src/getpic.c line 1622
static signed int new_slice(signed int framenum, signed int MBAmax);
// c::next_start_code
// file src/gethdr.c line 181
void next_start_code(void);
// c::open
// file /usr/include/x86_64-linux-gnu/bits/fcntl2.h line 41
signed int open(const char *__path, signed int __oflag, ...);
// c::openat
// file /usr/include/x86_64-linux-gnu/bits/fcntl2.h line 117
signed int openat(signed int __fd, const char *__path, signed int __oflag, ...);
// c::picture_coding_extension
// file src/gethdr.c line 928
static void picture_coding_extension(void);
// c::picture_data
// file src/getpic.c line 201
static void picture_data(signed int framenum);
// c::picture_display_extension
// file src/gethdr.c line 851
static void picture_display_extension(void);
// c::picture_header
// file src/gethdr.c line 377
static void picture_header(void);
// c::picture_spatial_scalable_extension
// file src/gethdr.c line 1004
static void picture_spatial_scalable_extension(void);
// c::picture_temporal_scalable_extension
// file src/gethdr.c line 1054
static void picture_temporal_scalable_extension(void);
// c::printf
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 102
signed int printf(const char * restrict __fmt, ...);
// c::pthread_attr_init
// file /usr/include/pthread.h line 286
signed int pthread_attr_init(union pthread_attr_t *);
// c::pthread_attr_setdetachstate
// file /usr/include/pthread.h line 298
signed int pthread_attr_setdetachstate(union pthread_attr_t *, signed int);
// c::pthread_create
// file /usr/include/pthread.h line 232
signed int pthread_create(unsigned long int *, const union pthread_attr_t *, void * (*)(void *), void *);
// c::pthread_equal
// file /usr/include/pthread.h line 1144
signed int pthread_equal(unsigned long int __thread1, unsigned long int __thread2);
// c::pthread_join
// file /usr/include/pthread.h line 249
signed int pthread_join(unsigned long int, void **);
// c::ptsname_r
// file /usr/include/x86_64-linux-gnu/bits/stdlib.h line 64
signed int ptsname_r(signed int __fd, char *__buf, unsigned long int __buflen);
// c::putbyte
// file src/store.c line 490
static void putbyte(signed int c);
// c::putc_unlocked
// file /usr/include/x86_64-linux-gnu/bits/stdio.h line 98
signed int putc_unlocked(signed int __c, struct _IO_FILE *__stream);
// c::putchar
// file /usr/include/x86_64-linux-gnu/bits/stdio.h line 79
signed int putchar(signed int __c);
// c::putchar_unlocked
// file /usr/include/x86_64-linux-gnu/bits/stdio.h line 105
signed int putchar_unlocked(signed int __c);
// c::putword
// file src/store.c line 502
static void putword(signed int w);
// c::quant_matrix_extension
// file src/gethdr.c line 726
static void quant_matrix_extension(void);
// c::read
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 34
signed long int read(signed int __fd, void *__buf, unsigned long int __nbytes);
// c::readlink
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 139
signed long int readlink(const char * restrict __path, char * restrict __buf, unsigned long int __len);
// c::readlinkat
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 173
signed long int readlinkat(signed int __fd, const char * restrict __path, char * restrict __buf, unsigned long int __len);
// c::realloc
// file /usr/include/stdlib.h line 479
void * realloc(void *, unsigned long int);
// c::realpath
// file /usr/include/x86_64-linux-gnu/bits/stdlib.h line 37
char * realpath(const char * restrict __name, char * restrict __resolved);
// c::sequence_display_extension
// file src/gethdr.c line 676
static void sequence_display_extension(void);
// c::sequence_extension
// file src/gethdr.c line 573
static void sequence_extension(void);
// c::sequence_header
// file src/gethdr.c line 255
static void sequence_header(void);
// c::sequence_scalable_extension
// file src/gethdr.c line 789
static void sequence_scalable_extension(void);
// c::slice_header
// file src/gethdr.c line 441
signed int slice_header(void);
// c::snprintf
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 61
signed int snprintf(char * restrict __s, unsigned long int __n, const char * restrict __fmt, ...);
// c::sprintf
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 31
signed int sprintf(char * restrict __s, const char * restrict __fmt, ...);
// c::sqrt
// file /usr/include/x86_64-linux-gnu/bits/mathcalls.h line 157
double sqrt(double);
// c::store_one
// file src/store.c line 144
static void store_one(char *outname, unsigned char **src, signed int offset, signed int incr, signed int height);
// c::store_ppm_tga
// file src/store.c line 365
static void store_ppm_tga(char *outname, unsigned char **src, signed int offset, signed int incr, signed int height, signed int tgaflag);
// c::store_sif
// file src/store.c line 295
static void store_sif(char *outname, unsigned char **src, signed int offset, signed int incr, signed int height);
// c::store_yuv
// file src/store.c line 229
static void store_yuv(char *outname, unsigned char **src, signed int offset, signed int incr, signed int height);
// c::store_yuv1
// file src/store.c line 260
static void store_yuv1(char *name, unsigned char *src, signed int offset, signed int incr, signed int width, signed int height);
// c::store_yuv_progressive
// file src/store.c line 198
static void store_yuv_progressive(char *outname, unsigned char **src, signed int offset, signed int incr, signed int height);
// c::store_yuvp
// file src/store.c line 176
static void store_yuvp(char *name, unsigned char *src, signed int offset, signed int incr, signed int width, signed int height);
// c::strcat
// file src/spatscal.c line 143 function Read_Lower_Layer_Component_Framewise
signed int strcat(void);
// c::strtod
// file /usr/include/stdlib.h line 164
double strtod(const char *, char **);
// c::strtol
// file /usr/include/stdlib.h line 183
signed long int strtol(const char *, char **, signed int);
// c::strtoll
// file /usr/include/stdlib.h line 209
signed long long int strtoll(const char *, char **, signed int);
// c::tolower
// file /usr/include/ctype.h line 216
signed int tolower(signed int __c);
// c::toupper
// file /usr/include/ctype.h line 222
signed int toupper(signed int __c);
// c::ttyname_r
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 291
signed int ttyname_r(signed int __fd, char *__buf, unsigned long int __buflen);
// c::user_data
// file src/gethdr.c line 1099
static void user_data(void);
// c::vdprintf
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 150
signed int vdprintf(signed int __fd, const char * restrict __fmt, void **__ap);
// c::vfprintf
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 124
signed int vfprintf(struct _IO_FILE * restrict __stream, const char * restrict __fmt, void **__ap);
// c::video_sequence
// file src/mpeg2dec.c line 736
static signed int video_sequence(signed int *Bitstream_Framenumber);
// c::vprintf
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 114
signed int vprintf(const char * restrict __fmt, void **__ap);
// c::vsnprintf
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 74
signed int vsnprintf(char * restrict __s, unsigned long int __n, const char * restrict __fmt, void **__ap);
// c::vsprintf
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 43
signed int vsprintf(char * restrict __s, const char * restrict __fmt, void **__ap);
// c::wcstombs
// file /usr/include/x86_64-linux-gnu/bits/stdlib.h line 144
unsigned long int wcstombs(char * restrict __dst, const signed int * restrict __src, unsigned long int __len);
// c::wctomb
// file /usr/include/x86_64-linux-gnu/bits/stdlib.h line 83
signed int wctomb(char *__s, signed int __wchar);
// c::write
// file /usr/include/unistd.h line 366
signed long int write(signed int, const void *, unsigned long int);
// c::write_frame_buf32
// file src/getpic.c line 1448
void write_frame_buf32(signed int t, unsigned int data);
// c::write_frame_buf8
// file src/getpic.c line 1428
void write_frame_buf8(signed int t, unsigned char data);

union anon$4
{
  // __l
  long double __l;
  // __i
  signed int __i[3l];
};

union anon$4$link1
{
  // __l
  long double __l;
  // __i
  signed int __i[3l];
};

struct anon$0
{
  // frame_buf
  unsigned char *frame_buf;
  // frame_buf_size
  unsigned int frame_buf_size;
  // frame_buf_offset
  unsigned int frame_buf_offset;
  // padding
  unsigned char padding[20l];
};

struct anon$2
{
  // id
  signed int id;
  // num_slices
  signed int num_slices;
  // framenum
  signed int framenum;
  // MBAmax
  signed int MBAmax;
};

struct anon$1
{
  // run
  char run;
  // level
  char level;
  // len
  char len;
};

struct anon$3
{
  // val
  char val;
  // len
  char len;
};

struct _IO_FILE
{
  // _flags
  signed int _flags;
  // _IO_read_ptr
  char *_IO_read_ptr;
  // _IO_read_end
  char *_IO_read_end;
  // _IO_read_base
  char *_IO_read_base;
  // _IO_write_base
  char *_IO_write_base;
  // _IO_write_ptr
  char *_IO_write_ptr;
  // _IO_write_end
  char *_IO_write_end;
  // _IO_buf_base
  char *_IO_buf_base;
  // _IO_buf_end
  char *_IO_buf_end;
  // _IO_save_base
  char *_IO_save_base;
  // _IO_backup_base
  char *_IO_backup_base;
  // _IO_save_end
  char *_IO_save_end;
  // _markers
  struct _IO_marker *_markers;
  // _chain
  struct _IO_FILE *_chain;
  // _fileno
  signed int _fileno;
  // _flags2
  signed int _flags2;
  // _old_offset
  signed long int _old_offset;
  // _cur_column
  unsigned short int _cur_column;
  // _vtable_offset
  signed char _vtable_offset;
  // _shortbuf
  char _shortbuf[1l];
  // _lock
  void *_lock;
  // _offset
  signed long int _offset;
  // __pad1
  void *__pad1;
  // __pad2
  void *__pad2;
  // __pad3
  void *__pad3;
  // __pad4
  void *__pad4;
  // __pad5
  unsigned long int __pad5;
  // _mode
  signed int _mode;
  // _unused2
  char _unused2[20l /*[[signed int]]*/];
};

struct _IO_FILE$link10
{
  // _flags
  signed int _flags;
  // _IO_read_ptr
  char *_IO_read_ptr;
  // _IO_read_end
  char *_IO_read_end;
  // _IO_read_base
  char *_IO_read_base;
  // _IO_write_base
  char *_IO_write_base;
  // _IO_write_ptr
  char *_IO_write_ptr;
  // _IO_write_end
  char *_IO_write_end;
  // _IO_buf_base
  char *_IO_buf_base;
  // _IO_buf_end
  char *_IO_buf_end;
  // _IO_save_base
  char *_IO_save_base;
  // _IO_backup_base
  char *_IO_backup_base;
  // _IO_save_end
  char *_IO_save_end;
  // _markers
  struct _IO_marker$link12 *_markers;
  // _chain
  struct _IO_FILE$link10 *_chain;
  // _fileno
  signed int _fileno;
  // _flags2
  signed int _flags2;
  // _old_offset
  signed long int _old_offset;
  // _cur_column
  unsigned short int _cur_column;
  // _vtable_offset
  signed char _vtable_offset;
  // _shortbuf
  char _shortbuf[1l];
  // _lock
  void *_lock;
  // _offset
  signed long int _offset;
  // __pad1
  void *__pad1;
  // __pad2
  void *__pad2;
  // __pad3
  void *__pad3;
  // __pad4
  void *__pad4;
  // __pad5
  unsigned long int __pad5;
  // _mode
  signed int _mode;
  // _unused2
  char _unused2[20l /*[[signed int]]*/];
};

struct _IO_FILE$link11
{
  // _flags
  signed int _flags;
  // _IO_read_ptr
  char *_IO_read_ptr;
  // _IO_read_end
  char *_IO_read_end;
  // _IO_read_base
  char *_IO_read_base;
  // _IO_write_base
  char *_IO_write_base;
  // _IO_write_ptr
  char *_IO_write_ptr;
  // _IO_write_end
  char *_IO_write_end;
  // _IO_buf_base
  char *_IO_buf_base;
  // _IO_buf_end
  char *_IO_buf_end;
  // _IO_save_base
  char *_IO_save_base;
  // _IO_backup_base
  char *_IO_backup_base;
  // _IO_save_end
  char *_IO_save_end;
  // _markers
  struct _IO_marker$link13 *_markers;
  // _chain
  struct _IO_FILE$link11 *_chain;
  // _fileno
  signed int _fileno;
  // _flags2
  signed int _flags2;
  // _old_offset
  signed long int _old_offset;
  // _cur_column
  unsigned short int _cur_column;
  // _vtable_offset
  signed char _vtable_offset;
  // _shortbuf
  char _shortbuf[1l];
  // _lock
  void *_lock;
  // _offset
  signed long int _offset;
  // __pad1
  void *__pad1;
  // __pad2
  void *__pad2;
  // __pad3
  void *__pad3;
  // __pad4
  void *__pad4;
  // __pad5
  unsigned long int __pad5;
  // _mode
  signed int _mode;
  // _unused2
  char _unused2[20l /*[[signed int]]*/];
};

struct _IO_FILE$link12
{
  // _flags
  signed int _flags;
  // _IO_read_ptr
  char *_IO_read_ptr;
  // _IO_read_end
  char *_IO_read_end;
  // _IO_read_base
  char *_IO_read_base;
  // _IO_write_base
  char *_IO_write_base;
  // _IO_write_ptr
  char *_IO_write_ptr;
  // _IO_write_end
  char *_IO_write_end;
  // _IO_buf_base
  char *_IO_buf_base;
  // _IO_buf_end
  char *_IO_buf_end;
  // _IO_save_base
  char *_IO_save_base;
  // _IO_backup_base
  char *_IO_backup_base;
  // _IO_save_end
  char *_IO_save_end;
  // _markers
  struct _IO_marker$link14 *_markers;
  // _chain
  struct _IO_FILE$link12 *_chain;
  // _fileno
  signed int _fileno;
  // _flags2
  signed int _flags2;
  // _old_offset
  signed long int _old_offset;
  // _cur_column
  unsigned short int _cur_column;
  // _vtable_offset
  signed char _vtable_offset;
  // _shortbuf
  char _shortbuf[1l];
  // _lock
  void *_lock;
  // _offset
  signed long int _offset;
  // __pad1
  void *__pad1;
  // __pad2
  void *__pad2;
  // __pad3
  void *__pad3;
  // __pad4
  void *__pad4;
  // __pad5
  unsigned long int __pad5;
  // _mode
  signed int _mode;
  // _unused2
  char _unused2[20l /*[[signed int]]*/];
};

struct _IO_FILE$link13
{
  // _flags
  signed int _flags;
  // _IO_read_ptr
  char *_IO_read_ptr;
  // _IO_read_end
  char *_IO_read_end;
  // _IO_read_base
  char *_IO_read_base;
  // _IO_write_base
  char *_IO_write_base;
  // _IO_write_ptr
  char *_IO_write_ptr;
  // _IO_write_end
  char *_IO_write_end;
  // _IO_buf_base
  char *_IO_buf_base;
  // _IO_buf_end
  char *_IO_buf_end;
  // _IO_save_base
  char *_IO_save_base;
  // _IO_backup_base
  char *_IO_backup_base;
  // _IO_save_end
  char *_IO_save_end;
  // _markers
  struct _IO_marker$link15 *_markers;
  // _chain
  struct _IO_FILE$link13 *_chain;
  // _fileno
  signed int _fileno;
  // _flags2
  signed int _flags2;
  // _old_offset
  signed long int _old_offset;
  // _cur_column
  unsigned short int _cur_column;
  // _vtable_offset
  signed char _vtable_offset;
  // _shortbuf
  char _shortbuf[1l];
  // _lock
  void *_lock;
  // _offset
  signed long int _offset;
  // __pad1
  void *__pad1;
  // __pad2
  void *__pad2;
  // __pad3
  void *__pad3;
  // __pad4
  void *__pad4;
  // __pad5
  unsigned long int __pad5;
  // _mode
  signed int _mode;
  // _unused2
  char _unused2[20l /*[[signed int]]*/];
};

struct _IO_FILE$link3
{
  // _flags
  signed int _flags;
  // _IO_read_ptr
  char *_IO_read_ptr;
  // _IO_read_end
  char *_IO_read_end;
  // _IO_read_base
  char *_IO_read_base;
  // _IO_write_base
  char *_IO_write_base;
  // _IO_write_ptr
  char *_IO_write_ptr;
  // _IO_write_end
  char *_IO_write_end;
  // _IO_buf_base
  char *_IO_buf_base;
  // _IO_buf_end
  char *_IO_buf_end;
  // _IO_save_base
  char *_IO_save_base;
  // _IO_backup_base
  char *_IO_backup_base;
  // _IO_save_end
  char *_IO_save_end;
  // _markers
  struct _IO_marker$link5 *_markers;
  // _chain
  struct _IO_FILE$link3 *_chain;
  // _fileno
  signed int _fileno;
  // _flags2
  signed int _flags2;
  // _old_offset
  signed long int _old_offset;
  // _cur_column
  unsigned short int _cur_column;
  // _vtable_offset
  signed char _vtable_offset;
  // _shortbuf
  char _shortbuf[1l];
  // _lock
  void *_lock;
  // _offset
  signed long int _offset;
  // __pad1
  void *__pad1;
  // __pad2
  void *__pad2;
  // __pad3
  void *__pad3;
  // __pad4
  void *__pad4;
  // __pad5
  unsigned long int __pad5;
  // _mode
  signed int _mode;
  // _unused2
  char _unused2[20l /*[[signed int]]*/];
};

struct _IO_FILE$link4
{
  // _flags
  signed int _flags;
  // _IO_read_ptr
  char *_IO_read_ptr;
  // _IO_read_end
  char *_IO_read_end;
  // _IO_read_base
  char *_IO_read_base;
  // _IO_write_base
  char *_IO_write_base;
  // _IO_write_ptr
  char *_IO_write_ptr;
  // _IO_write_end
  char *_IO_write_end;
  // _IO_buf_base
  char *_IO_buf_base;
  // _IO_buf_end
  char *_IO_buf_end;
  // _IO_save_base
  char *_IO_save_base;
  // _IO_backup_base
  char *_IO_backup_base;
  // _IO_save_end
  char *_IO_save_end;
  // _markers
  struct _IO_marker$link6 *_markers;
  // _chain
  struct _IO_FILE$link4 *_chain;
  // _fileno
  signed int _fileno;
  // _flags2
  signed int _flags2;
  // _old_offset
  signed long int _old_offset;
  // _cur_column
  unsigned short int _cur_column;
  // _vtable_offset
  signed char _vtable_offset;
  // _shortbuf
  char _shortbuf[1l];
  // _lock
  void *_lock;
  // _offset
  signed long int _offset;
  // __pad1
  void *__pad1;
  // __pad2
  void *__pad2;
  // __pad3
  void *__pad3;
  // __pad4
  void *__pad4;
  // __pad5
  unsigned long int __pad5;
  // _mode
  signed int _mode;
  // _unused2
  char _unused2[20l /*[[signed int]]*/];
};

struct _IO_FILE$link5
{
  // _flags
  signed int _flags;
  // _IO_read_ptr
  char *_IO_read_ptr;
  // _IO_read_end
  char *_IO_read_end;
  // _IO_read_base
  char *_IO_read_base;
  // _IO_write_base
  char *_IO_write_base;
  // _IO_write_ptr
  char *_IO_write_ptr;
  // _IO_write_end
  char *_IO_write_end;
  // _IO_buf_base
  char *_IO_buf_base;
  // _IO_buf_end
  char *_IO_buf_end;
  // _IO_save_base
  char *_IO_save_base;
  // _IO_backup_base
  char *_IO_backup_base;
  // _IO_save_end
  char *_IO_save_end;
  // _markers
  struct _IO_marker$link7 *_markers;
  // _chain
  struct _IO_FILE$link5 *_chain;
  // _fileno
  signed int _fileno;
  // _flags2
  signed int _flags2;
  // _old_offset
  signed long int _old_offset;
  // _cur_column
  unsigned short int _cur_column;
  // _vtable_offset
  signed char _vtable_offset;
  // _shortbuf
  char _shortbuf[1l];
  // _lock
  void *_lock;
  // _offset
  signed long int _offset;
  // __pad1
  void *__pad1;
  // __pad2
  void *__pad2;
  // __pad3
  void *__pad3;
  // __pad4
  void *__pad4;
  // __pad5
  unsigned long int __pad5;
  // _mode
  signed int _mode;
  // _unused2
  char _unused2[20l /*[[signed int]]*/];
};

struct _IO_FILE$link6
{
  // _flags
  signed int _flags;
  // _IO_read_ptr
  char *_IO_read_ptr;
  // _IO_read_end
  char *_IO_read_end;
  // _IO_read_base
  char *_IO_read_base;
  // _IO_write_base
  char *_IO_write_base;
  // _IO_write_ptr
  char *_IO_write_ptr;
  // _IO_write_end
  char *_IO_write_end;
  // _IO_buf_base
  char *_IO_buf_base;
  // _IO_buf_end
  char *_IO_buf_end;
  // _IO_save_base
  char *_IO_save_base;
  // _IO_backup_base
  char *_IO_backup_base;
  // _IO_save_end
  char *_IO_save_end;
  // _markers
  struct _IO_marker$link8 *_markers;
  // _chain
  struct _IO_FILE$link6 *_chain;
  // _fileno
  signed int _fileno;
  // _flags2
  signed int _flags2;
  // _old_offset
  signed long int _old_offset;
  // _cur_column
  unsigned short int _cur_column;
  // _vtable_offset
  signed char _vtable_offset;
  // _shortbuf
  char _shortbuf[1l];
  // _lock
  void *_lock;
  // _offset
  signed long int _offset;
  // __pad1
  void *__pad1;
  // __pad2
  void *__pad2;
  // __pad3
  void *__pad3;
  // __pad4
  void *__pad4;
  // __pad5
  unsigned long int __pad5;
  // _mode
  signed int _mode;
  // _unused2
  char _unused2[20l /*[[signed int]]*/];
};

struct _IO_FILE$link7
{
  // _flags
  signed int _flags;
  // _IO_read_ptr
  char *_IO_read_ptr;
  // _IO_read_end
  char *_IO_read_end;
  // _IO_read_base
  char *_IO_read_base;
  // _IO_write_base
  char *_IO_write_base;
  // _IO_write_ptr
  char *_IO_write_ptr;
  // _IO_write_end
  char *_IO_write_end;
  // _IO_buf_base
  char *_IO_buf_base;
  // _IO_buf_end
  char *_IO_buf_end;
  // _IO_save_base
  char *_IO_save_base;
  // _IO_backup_base
  char *_IO_backup_base;
  // _IO_save_end
  char *_IO_save_end;
  // _markers
  struct _IO_marker$link9 *_markers;
  // _chain
  struct _IO_FILE$link7 *_chain;
  // _fileno
  signed int _fileno;
  // _flags2
  signed int _flags2;
  // _old_offset
  signed long int _old_offset;
  // _cur_column
  unsigned short int _cur_column;
  // _vtable_offset
  signed char _vtable_offset;
  // _shortbuf
  char _shortbuf[1l];
  // _lock
  void *_lock;
  // _offset
  signed long int _offset;
  // __pad1
  void *__pad1;
  // __pad2
  void *__pad2;
  // __pad3
  void *__pad3;
  // __pad4
  void *__pad4;
  // __pad5
  unsigned long int __pad5;
  // _mode
  signed int _mode;
  // _unused2
  char _unused2[20l /*[[signed int]]*/];
};

struct _IO_FILE$link8
{
  // _flags
  signed int _flags;
  // _IO_read_ptr
  char *_IO_read_ptr;
  // _IO_read_end
  char *_IO_read_end;
  // _IO_read_base
  char *_IO_read_base;
  // _IO_write_base
  char *_IO_write_base;
  // _IO_write_ptr
  char *_IO_write_ptr;
  // _IO_write_end
  char *_IO_write_end;
  // _IO_buf_base
  char *_IO_buf_base;
  // _IO_buf_end
  char *_IO_buf_end;
  // _IO_save_base
  char *_IO_save_base;
  // _IO_backup_base
  char *_IO_backup_base;
  // _IO_save_end
  char *_IO_save_end;
  // _markers
  struct _IO_marker$link10 *_markers;
  // _chain
  struct _IO_FILE$link8 *_chain;
  // _fileno
  signed int _fileno;
  // _flags2
  signed int _flags2;
  // _old_offset
  signed long int _old_offset;
  // _cur_column
  unsigned short int _cur_column;
  // _vtable_offset
  signed char _vtable_offset;
  // _shortbuf
  char _shortbuf[1l];
  // _lock
  void *_lock;
  // _offset
  signed long int _offset;
  // __pad1
  void *__pad1;
  // __pad2
  void *__pad2;
  // __pad3
  void *__pad3;
  // __pad4
  void *__pad4;
  // __pad5
  unsigned long int __pad5;
  // _mode
  signed int _mode;
  // _unused2
  char _unused2[20l /*[[signed int]]*/];
};

struct _IO_FILE$link9
{
  // _flags
  signed int _flags;
  // _IO_read_ptr
  char *_IO_read_ptr;
  // _IO_read_end
  char *_IO_read_end;
  // _IO_read_base
  char *_IO_read_base;
  // _IO_write_base
  char *_IO_write_base;
  // _IO_write_ptr
  char *_IO_write_ptr;
  // _IO_write_end
  char *_IO_write_end;
  // _IO_buf_base
  char *_IO_buf_base;
  // _IO_buf_end
  char *_IO_buf_end;
  // _IO_save_base
  char *_IO_save_base;
  // _IO_backup_base
  char *_IO_backup_base;
  // _IO_save_end
  char *_IO_save_end;
  // _markers
  struct _IO_marker$link11 *_markers;
  // _chain
  struct _IO_FILE$link9 *_chain;
  // _fileno
  signed int _fileno;
  // _flags2
  signed int _flags2;
  // _old_offset
  signed long int _old_offset;
  // _cur_column
  unsigned short int _cur_column;
  // _vtable_offset
  signed char _vtable_offset;
  // _shortbuf
  char _shortbuf[1l];
  // _lock
  void *_lock;
  // _offset
  signed long int _offset;
  // __pad1
  void *__pad1;
  // __pad2
  void *__pad2;
  // __pad3
  void *__pad3;
  // __pad4
  void *__pad4;
  // __pad5
  unsigned long int __pad5;
  // _mode
  signed int _mode;
  // _unused2
  char _unused2[20l /*[[signed int]]*/];
};

struct _IO_marker
{
  // _next
  struct _IO_marker *_next;
  // _sbuf
  struct _IO_FILE *_sbuf;
  // _pos
  signed int _pos;
};

struct _IO_marker$link10
{
  // _next
  struct _IO_marker$link10 *_next;
  // _sbuf
  struct _IO_FILE$link8 *_sbuf;
  // _pos
  signed int _pos;
};

struct _IO_marker$link11
{
  // _next
  struct _IO_marker$link11 *_next;
  // _sbuf
  struct _IO_FILE$link9 *_sbuf;
  // _pos
  signed int _pos;
};

struct _IO_marker$link12
{
  // _next
  struct _IO_marker$link12 *_next;
  // _sbuf
  struct _IO_FILE$link10 *_sbuf;
  // _pos
  signed int _pos;
};

struct _IO_marker$link13
{
  // _next
  struct _IO_marker$link13 *_next;
  // _sbuf
  struct _IO_FILE$link11 *_sbuf;
  // _pos
  signed int _pos;
};

struct _IO_marker$link14
{
  // _next
  struct _IO_marker$link14 *_next;
  // _sbuf
  struct _IO_FILE$link12 *_sbuf;
  // _pos
  signed int _pos;
};

struct _IO_marker$link15
{
  // _next
  struct _IO_marker$link15 *_next;
  // _sbuf
  struct _IO_FILE$link13 *_sbuf;
  // _pos
  signed int _pos;
};

struct _IO_marker$link5
{
  // _next
  struct _IO_marker$link5 *_next;
  // _sbuf
  struct _IO_FILE$link3 *_sbuf;
  // _pos
  signed int _pos;
};

struct _IO_marker$link6
{
  // _next
  struct _IO_marker$link6 *_next;
  // _sbuf
  struct _IO_FILE$link4 *_sbuf;
  // _pos
  signed int _pos;
};

struct _IO_marker$link7
{
  // _next
  struct _IO_marker$link7 *_next;
  // _sbuf
  struct _IO_FILE$link5 *_sbuf;
  // _pos
  signed int _pos;
};

struct _IO_marker$link8
{
  // _next
  struct _IO_marker$link8 *_next;
  // _sbuf
  struct _IO_FILE$link6 *_sbuf;
  // _pos
  signed int _pos;
};

struct _IO_marker$link9
{
  // _next
  struct _IO_marker$link9 *_next;
  // _sbuf
  struct _IO_FILE$link7 *_sbuf;
  // _pos
  signed int _pos;
};

struct layer_data
{
  // Infile
  signed int Infile;
  // Rdbfr
  unsigned char Rdbfr[2048l];
  // Rdptr
  unsigned char *Rdptr;
  // Inbfr
  unsigned char Inbfr[16l];
  // Bfr
  unsigned int Bfr;
  // Rdmax
  unsigned char *Rdmax;
  // Incnt
  signed int Incnt;
  // Bitcnt
  signed int Bitcnt;
  // intra_quantizer_matrix
  signed int intra_quantizer_matrix[64l];
  // non_intra_quantizer_matrix
  signed int non_intra_quantizer_matrix[64l];
  // chroma_intra_quantizer_matrix
  signed int chroma_intra_quantizer_matrix[64l];
  // chroma_non_intra_quantizer_matrix
  signed int chroma_non_intra_quantizer_matrix[64l];
  // load_intra_quantizer_matrix
  signed int load_intra_quantizer_matrix;
  // load_non_intra_quantizer_matrix
  signed int load_non_intra_quantizer_matrix;
  // load_chroma_intra_quantizer_matrix
  signed int load_chroma_intra_quantizer_matrix;
  // load_chroma_non_intra_quantizer_matrix
  signed int load_chroma_non_intra_quantizer_matrix;
  // MPEG2_Flag
  signed int MPEG2_Flag;
  // scalable_mode
  signed int scalable_mode;
  // q_scale_type
  signed int q_scale_type;
  // alternate_scan
  signed int alternate_scan;
  // pict_scal
  signed int pict_scal;
  // priority_breakpoint
  signed int priority_breakpoint;
  // quantizer_scale
  signed int quantizer_scale;
  // intra_slice
  signed int intra_slice;
  // block
  signed short int block[12l][64l];
};

union pthread_attr_t
{
  // __size
  char __size[56l];
  // __align
  signed long int __align;
};

struct thrd_layer_data
{
  // pict_scal
  signed int pict_scal;
  // priority_breakpoint
  signed int priority_breakpoint;
  // quantizer_scale
  signed int quantizer_scale;
  // intra_slice
  signed int intra_slice;
  // block
  signed short int block[12l][64l];
};


// c::Author
// file src/global.h line 234
char Author[41l];
// c::Author
// file src/global.h line 234
char Author[41l] = { 40, 67, 41, 32, 49, 57, 57, 54, 44, 32, 77, 80, 69, 71, 32, 83, 111, 102, 116, 119, 97, 114, 101, 32, 83, 105, 109, 117, 108, 97, 116, 105, 111, 110, 32, 71, 114, 111, 117, 112, 0 };
// c::BMBtab0
// file src/getvlc.h line 118
static struct anon$3 BMBtab0[16l];
// c::BMBtab0
// file src/getvlc.h line 118
static struct anon$3 BMBtab0[16l] = { { .val=(char)-1, .len=(char)0 }, { .val=(char)-1, .len=(char)0 }, { .val=(char)8, .len=(char)4 }, { .val=(char)(8 | 2), .len=(char)4 }, { .val=(char)4, .len=(char)3 }, { .val=(char)4, .len=(char)3 }, { .val=(char)(4 | 2), .len=(char)3 }, { .val=(char)(4 | 2), .len=(char)3 }, { .val=(char)(8 | 4), .len=(char)2 }, { .val=(char)(8 | 4), .len=(char)2 }, { .val=(char)(8 | 4), .len=(char)2 }, { .val=(char)(8 | 4), .len=(char)2 }, { .val=(char)(8 | 4 | 2), .len=(char)2 }, 
    { .val=(char)(8 | 4 | 2), .len=(char)2 }, 
    { .val=(char)(8 | 4 | 2), .len=(char)2 }, 
    { .val=(char)(8 | 4 | 2), .len=(char)2 } };
// c::BMBtab1
// file src/getvlc.h line 138
static struct anon$3 BMBtab1[8l];
// c::BMBtab1
// file src/getvlc.h line 138
static struct anon$3 BMBtab1[8l] = { { .val=(char)-1, .len=(char)0 }, { .val=(char)(16 | 1), .len=(char)6 }, { .val=(char)(16 | 4 | 2), .len=(char)6 }, 
    { .val=(char)(16 | 8 | 2), .len=(char)6 }, 
    { .val=(char)(16 | 8 | 4 | 2), .len=(char)5 }, 
    { .val=(char)(16 | 8 | 4 | 2), .len=(char)5 }, 
    { .val=(char)1, .len=(char)5 }, { .val=(char)1, .len=(char)5 } };
// c::Big_Picture_Flag
// file src/global.h line 351
signed int Big_Picture_Flag;
// c::CBPtab0
// file src/getvlc.h line 278
static struct anon$3 CBPtab0[32l];
// c::CBPtab0
// file src/getvlc.h line 278
static struct anon$3 CBPtab0[32l] = { { .val=(char)-1, .len=(char)0 }, { .val=(char)-1, .len=(char)0 }, { .val=(char)-1, .len=(char)0 }, { .val=(char)-1, .len=(char)0 }, { .val=(char)-1, .len=(char)0 }, { .val=(char)-1, .len=(char)0 }, { .val=(char)-1, .len=(char)0 }, { .val=(char)-1, .len=(char)0 }, { .val=(char)62, .len=(char)5 }, { .val=(char)2, .len=(char)5 }, { .val=(char)61, .len=(char)5 }, { .val=(char)1, .len=(char)5 }, { .val=(char)56, .len=(char)5 }, { .val=(char)52, .len=(char)5 }, { .val=(char)44, .len=(char)5 }, { .val=(char)28, .len=(char)5 }, { .val=(char)40, .len=(char)5 }, { .val=(char)20, .len=(char)5 }, { .val=(char)48, .len=(char)5 }, { .val=(char)12, .len=(char)5 }, { .val=(char)32, .len=(char)4 }, { .val=(char)32, .len=(char)4 }, { .val=(char)16, .len=(char)4 }, { .val=(char)16, .len=(char)4 }, { .val=(char)8, .len=(char)4 }, { .val=(char)8, .len=(char)4 }, { .val=(char)4, .len=(char)4 }, { .val=(char)4, .len=(char)4 }, { .val=(char)60, .len=(char)3 }, { .val=(char)60, .len=(char)3 }, { .val=(char)60, .len=(char)3 }, { .val=(char)60, .len=(char)3 } };
// c::CBPtab1
// file src/getvlc.h line 287
static struct anon$3 CBPtab1[64l];
// c::CBPtab1
// file src/getvlc.h line 287
static struct anon$3 CBPtab1[64l] = { { .val=(char)-1, .len=(char)0 }, { .val=(char)-1, .len=(char)0 }, { .val=(char)-1, .len=(char)0 }, { .val=(char)-1, .len=(char)0 }, { .val=(char)58, .len=(char)8 }, { .val=(char)54, .len=(char)8 }, { .val=(char)46, .len=(char)8 }, { .val=(char)30, .len=(char)8 }, { .val=(char)57, .len=(char)8 }, { .val=(char)53, .len=(char)8 }, { .val=(char)45, .len=(char)8 }, { .val=(char)29, .len=(char)8 }, { .val=(char)38, .len=(char)8 }, { .val=(char)26, .len=(char)8 }, { .val=(char)37, .len=(char)8 }, { .val=(char)25, .len=(char)8 }, { .val=(char)43, .len=(char)8 }, { .val=(char)23, .len=(char)8 }, { .val=(char)51, .len=(char)8 }, { .val=(char)15, .len=(char)8 }, { .val=(char)42, .len=(char)8 }, { .val=(char)22, .len=(char)8 }, { .val=(char)50, .len=(char)8 }, { .val=(char)14, .len=(char)8 }, { .val=(char)41, .len=(char)8 }, { .val=(char)21, .len=(char)8 }, { .val=(char)49, .len=(char)8 }, { .val=(char)13, .len=(char)8 }, { .val=(char)35, .len=(char)8 }, { .val=(char)19, .len=(char)8 }, { .val=(char)11, .len=(char)8 }, { .val=(char)7, .len=(char)8 }, { .val=(char)34, .len=(char)7 }, { .val=(char)34, .len=(char)7 }, { .val=(char)18, .len=(char)7 }, { .val=(char)18, .len=(char)7 }, { .val=(char)10, .len=(char)7 }, { .val=(char)10, .len=(char)7 }, { .val=(char)6, .len=(char)7 }, { .val=(char)6, .len=(char)7 }, { .val=(char)33, .len=(char)7 }, { .val=(char)33, .len=(char)7 }, { .val=(char)17, .len=(char)7 }, { .val=(char)17, .len=(char)7 }, { .val=(char)9, .len=(char)7 }, { .val=(char)9, .len=(char)7 }, { .val=(char)5, .len=(char)7 }, { .val=(char)5, .len=(char)7 }, { .val=(char)63, .len=(char)6 }, { .val=(char)63, .len=(char)6 }, { .val=(char)63, .len=(char)6 }, { .val=(char)63, .len=(char)6 }, { .val=(char)3, .len=(char)6 }, { .val=(char)3, .len=(char)6 }, { .val=(char)3, .len=(char)6 }, { .val=(char)3, .len=(char)6 }, { .val=(char)36, .len=(char)6 }, { .val=(char)36, .len=(char)6 }, { .val=(char)36, .len=(char)6 }, { .val=(char)36, .len=(char)6 }, { .val=(char)24, .len=(char)6 }, { .val=(char)24, .len=(char)6 }, { .val=(char)24, .len=(char)6 }, { .val=(char)24, .len=(char)6 } };
// c::CBPtab2
// file src/getvlc.h line 300
static struct anon$3 CBPtab2[8l];
// c::CBPtab2
// file src/getvlc.h line 300
static struct anon$3 CBPtab2[8l] = { { .val=(char)-1, .len=(char)0 }, { .val=(char)0, .len=(char)9 }, { .val=(char)39, .len=(char)9 }, { .val=(char)27, .len=(char)9 }, { .val=(char)59, .len=(char)9 }, { .val=(char)55, .len=(char)9 }, { .val=(char)47, .len=(char)9 }, { .val=(char)31, .len=(char)9 } };
// c::Chroma_Height
// file src/global.h line 392
signed int Chroma_Height;
// c::Chroma_Width
// file src/global.h line 391
signed int Chroma_Width;
// c::Clip
// file src/global.h line 367
unsigned char *Clip;
// c::Coded_Picture_Height
// file src/global.h line 390
signed int Coded_Picture_Height;
// c::Coded_Picture_Width
// file src/global.h line 389
signed int Coded_Picture_Width;
// c::DCTtab0
// file src/getblk.c line 92
struct anon$1 DCTtab0[60l];
// c::DCTtab0
// file src/getblk.c line 92
struct anon$1 DCTtab0[60l] = { { .run=(char)65, .level=(char)0, .len=(char)6 }, 
    { .run=(char)65, .level=(char)0, .len=(char)6 }, 
    { .run=(char)65, .level=(char)0, .len=(char)6 }, 
    { .run=(char)65, .level=(char)0, .len=(char)6 }, 
    { .run=(char)2, .level=(char)2, .len=(char)7 }, 
    { .run=(char)2, .level=(char)2, .len=(char)7 }, 
    { .run=(char)9, .level=(char)1, .len=(char)7 }, 
    { .run=(char)9, .level=(char)1, .len=(char)7 }, 
    { .run=(char)0, .level=(char)4, .len=(char)7 }, 
    { .run=(char)0, .level=(char)4, .len=(char)7 }, 
    { .run=(char)8, .level=(char)1, .len=(char)7 }, 
    { .run=(char)8, .level=(char)1, .len=(char)7 }, 
    { .run=(char)7, .level=(char)1, .len=(char)6 }, 
    { .run=(char)7, .level=(char)1, .len=(char)6 }, 
    { .run=(char)7, .level=(char)1, .len=(char)6 }, 
    { .run=(char)7, .level=(char)1, .len=(char)6 }, 
    { .run=(char)6, .level=(char)1, .len=(char)6 }, 
    { .run=(char)6, .level=(char)1, .len=(char)6 }, 
    { .run=(char)6, .level=(char)1, .len=(char)6 }, 
    { .run=(char)6, .level=(char)1, .len=(char)6 }, 
    { .run=(char)1, .level=(char)2, .len=(char)6 }, 
    { .run=(char)1, .level=(char)2, .len=(char)6 }, 
    { .run=(char)1, .level=(char)2, .len=(char)6 }, 
    { .run=(char)1, .level=(char)2, .len=(char)6 }, 
    { .run=(char)5, .level=(char)1, .len=(char)6 }, 
    { .run=(char)5, .level=(char)1, .len=(char)6 }, 
    { .run=(char)5, .level=(char)1, .len=(char)6 }, 
    { .run=(char)5, .level=(char)1, .len=(char)6 }, 
    { .run=(char)13, .level=(char)1, .len=(char)8 }, 
    { .run=(char)0, .level=(char)6, .len=(char)8 }, 
    { .run=(char)12, .level=(char)1, .len=(char)8 }, 
    { .run=(char)11, .level=(char)1, .len=(char)8 }, 
    { .run=(char)3, .level=(char)2, .len=(char)8 }, 
    { .run=(char)1, .level=(char)3, .len=(char)8 }, 
    { .run=(char)0, .level=(char)5, .len=(char)8 }, 
    { .run=(char)10, .level=(char)1, .len=(char)8 }, 
    { .run=(char)0, .level=(char)3, .len=(char)5 }, 
    { .run=(char)0, .level=(char)3, .len=(char)5 }, 
    { .run=(char)0, .level=(char)3, .len=(char)5 }, 
    { .run=(char)0, .level=(char)3, .len=(char)5 }, 
    { .run=(char)0, .level=(char)3, .len=(char)5 }, 
    { .run=(char)0, .level=(char)3, .len=(char)5 }, 
    { .run=(char)0, .level=(char)3, .len=(char)5 }, 
    { .run=(char)0, .level=(char)3, .len=(char)5 }, 
    { .run=(char)4, .level=(char)1, .len=(char)5 }, 
    { .run=(char)4, .level=(char)1, .len=(char)5 }, 
    { .run=(char)4, .level=(char)1, .len=(char)5 }, 
    { .run=(char)4, .level=(char)1, .len=(char)5 }, 
    { .run=(char)4, .level=(char)1, .len=(char)5 }, 
    { .run=(char)4, .level=(char)1, .len=(char)5 }, 
    { .run=(char)4, .level=(char)1, .len=(char)5 }, 
    { .run=(char)4, .level=(char)1, .len=(char)5 }, 
    { .run=(char)3, .level=(char)1, .len=(char)5 }, 
    { .run=(char)3, .level=(char)1, .len=(char)5 }, 
    { .run=(char)3, .level=(char)1, .len=(char)5 }, 
    { .run=(char)3, .level=(char)1, .len=(char)5 }, 
    { .run=(char)3, .level=(char)1, .len=(char)5 }, 
    { .run=(char)3, .level=(char)1, .len=(char)5 }, 
    { .run=(char)3, .level=(char)1, .len=(char)5 }, 
    { .run=(char)3, .level=(char)1, .len=(char)5 } };
// c::DCTtab0a
// file src/getblk.c line 94
struct anon$1 DCTtab0a[252l];
// c::DCTtab0a
// file src/getblk.c line 94
struct anon$1 DCTtab0a[252l] = { { .run=(char)65, .level=(char)0, .len=(char)6 }, 
    { .run=(char)65, .level=(char)0, .len=(char)6 }, 
    { .run=(char)65, .level=(char)0, .len=(char)6 }, 
    { .run=(char)65, .level=(char)0, .len=(char)6 }, 
    { .run=(char)7, .level=(char)1, .len=(char)7 }, 
    { .run=(char)7, .level=(char)1, .len=(char)7 }, 
    { .run=(char)8, .level=(char)1, .len=(char)7 }, 
    { .run=(char)8, .level=(char)1, .len=(char)7 }, 
    { .run=(char)6, .level=(char)1, .len=(char)7 }, 
    { .run=(char)6, .level=(char)1, .len=(char)7 }, 
    { .run=(char)2, .level=(char)2, .len=(char)7 }, 
    { .run=(char)2, .level=(char)2, .len=(char)7 }, 
    { .run=(char)0, .level=(char)7, .len=(char)6 }, 
    { .run=(char)0, .level=(char)7, .len=(char)6 }, 
    { .run=(char)0, .level=(char)7, .len=(char)6 }, 
    { .run=(char)0, .level=(char)7, .len=(char)6 }, 
    { .run=(char)0, .level=(char)6, .len=(char)6 }, 
    { .run=(char)0, .level=(char)6, .len=(char)6 }, 
    { .run=(char)0, .level=(char)6, .len=(char)6 }, 
    { .run=(char)0, .level=(char)6, .len=(char)6 }, 
    { .run=(char)4, .level=(char)1, .len=(char)6 }, 
    { .run=(char)4, .level=(char)1, .len=(char)6 }, 
    { .run=(char)4, .level=(char)1, .len=(char)6 }, 
    { .run=(char)4, .level=(char)1, .len=(char)6 }, 
    { .run=(char)5, .level=(char)1, .len=(char)6 }, 
    { .run=(char)5, .level=(char)1, .len=(char)6 }, 
    { .run=(char)5, .level=(char)1, .len=(char)6 }, 
    { .run=(char)5, .level=(char)1, .len=(char)6 }, 
    { .run=(char)1, .level=(char)5, .len=(char)8 }, 
    { .run=(char)11, .level=(char)1, .len=(char)8 }, 
    { .run=(char)0, .level=(char)11, .len=(char)8 }, 
    { .run=(char)0, .level=(char)10, .len=(char)8 }, 
    { .run=(char)13, .level=(char)1, .len=(char)8 }, 
    { .run=(char)12, .level=(char)1, .len=(char)8 }, 
    { .run=(char)3, .level=(char)2, .len=(char)8 }, 
    { .run=(char)1, .level=(char)4, .len=(char)8 }, 
    { .run=(char)2, .level=(char)1, .len=(char)5 }, 
    { .run=(char)2, .level=(char)1, .len=(char)5 }, 
    { .run=(char)2, .level=(char)1, .len=(char)5 }, 
    { .run=(char)2, .level=(char)1, .len=(char)5 }, 
    { .run=(char)2, .level=(char)1, .len=(char)5 }, 
    { .run=(char)2, .level=(char)1, .len=(char)5 }, 
    { .run=(char)2, .level=(char)1, .len=(char)5 }, 
    { .run=(char)2, .level=(char)1, .len=(char)5 }, 
    { .run=(char)1, .level=(char)2, .len=(char)5 }, 
    { .run=(char)1, .level=(char)2, .len=(char)5 }, 
    { .run=(char)1, .level=(char)2, .len=(char)5 }, 
    { .run=(char)1, .level=(char)2, .len=(char)5 }, 
    { .run=(char)1, .level=(char)2, .len=(char)5 }, 
    { .run=(char)1, .level=(char)2, .len=(char)5 }, 
    { .run=(char)1, .level=(char)2, .len=(char)5 }, 
    { .run=(char)1, .level=(char)2, .len=(char)5 }, 
    { .run=(char)3, .level=(char)1, .len=(char)5 }, 
    { .run=(char)3, .level=(char)1, .len=(char)5 }, 
    { .run=(char)3, .level=(char)1, .len=(char)5 }, 
    { .run=(char)3, .level=(char)1, .len=(char)5 }, 
    { .run=(char)3, .level=(char)1, .len=(char)5 }, 
    { .run=(char)3, .level=(char)1, .len=(char)5 }, 
    { .run=(char)3, .level=(char)1, .len=(char)5 }, 
    { .run=(char)3, .level=(char)1, .len=(char)5 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)64, .level=(char)0, .len=(char)4 }, 
    { .run=(char)64, .level=(char)0, .len=(char)4 }, 
    { .run=(char)64, .level=(char)0, .len=(char)4 }, 
    { .run=(char)64, .level=(char)0, .len=(char)4 }, 
    { .run=(char)64, .level=(char)0, .len=(char)4 }, 
    { .run=(char)64, .level=(char)0, .len=(char)4 }, 
    { .run=(char)64, .level=(char)0, .len=(char)4 }, 
    { .run=(char)64, .level=(char)0, .len=(char)4 }, 
    { .run=(char)64, .level=(char)0, .len=(char)4 }, 
    { .run=(char)64, .level=(char)0, .len=(char)4 }, 
    { .run=(char)64, .level=(char)0, .len=(char)4 }, 
    { .run=(char)64, .level=(char)0, .len=(char)4 }, 
    { .run=(char)64, .level=(char)0, .len=(char)4 }, 
    { .run=(char)64, .level=(char)0, .len=(char)4 }, 
    { .run=(char)64, .level=(char)0, .len=(char)4 }, 
    { .run=(char)64, .level=(char)0, .len=(char)4 }, 
    { .run=(char)0, .level=(char)3, .len=(char)4 }, 
    { .run=(char)0, .level=(char)3, .len=(char)4 }, 
    { .run=(char)0, .level=(char)3, .len=(char)4 }, 
    { .run=(char)0, .level=(char)3, .len=(char)4 }, 
    { .run=(char)0, .level=(char)3, .len=(char)4 }, 
    { .run=(char)0, .level=(char)3, .len=(char)4 }, 
    { .run=(char)0, .level=(char)3, .len=(char)4 }, 
    { .run=(char)0, .level=(char)3, .len=(char)4 }, 
    { .run=(char)0, .level=(char)3, .len=(char)4 }, 
    { .run=(char)0, .level=(char)3, .len=(char)4 }, 
    { .run=(char)0, .level=(char)3, .len=(char)4 }, 
    { .run=(char)0, .level=(char)3, .len=(char)4 }, 
    { .run=(char)0, .level=(char)3, .len=(char)4 }, 
    { .run=(char)0, .level=(char)3, .len=(char)4 }, 
    { .run=(char)0, .level=(char)3, .len=(char)4 }, 
    { .run=(char)0, .level=(char)3, .len=(char)4 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)2, .len=(char)3 }, 
    { .run=(char)0, .level=(char)4, .len=(char)5 }, 
    { .run=(char)0, .level=(char)4, .len=(char)5 }, 
    { .run=(char)0, .level=(char)4, .len=(char)5 }, 
    { .run=(char)0, .level=(char)4, .len=(char)5 }, 
    { .run=(char)0, .level=(char)4, .len=(char)5 }, 
    { .run=(char)0, .level=(char)4, .len=(char)5 }, 
    { .run=(char)0, .level=(char)4, .len=(char)5 }, 
    { .run=(char)0, .level=(char)4, .len=(char)5 }, 
    { .run=(char)0, .level=(char)5, .len=(char)5 }, 
    { .run=(char)0, .level=(char)5, .len=(char)5 }, 
    { .run=(char)0, .level=(char)5, .len=(char)5 }, 
    { .run=(char)0, .level=(char)5, .len=(char)5 }, 
    { .run=(char)0, .level=(char)5, .len=(char)5 }, 
    { .run=(char)0, .level=(char)5, .len=(char)5 }, 
    { .run=(char)0, .level=(char)5, .len=(char)5 }, 
    { .run=(char)0, .level=(char)5, .len=(char)5 }, 
    { .run=(char)9, .level=(char)1, .len=(char)7 }, 
    { .run=(char)9, .level=(char)1, .len=(char)7 }, 
    { .run=(char)1, .level=(char)3, .len=(char)7 }, 
    { .run=(char)1, .level=(char)3, .len=(char)7 }, 
    { .run=(char)10, .level=(char)1, .len=(char)7 }, 
    { .run=(char)10, .level=(char)1, .len=(char)7 }, 
    { .run=(char)0, .level=(char)8, .len=(char)7 }, 
    { .run=(char)0, .level=(char)8, .len=(char)7 }, 
    { .run=(char)0, .level=(char)9, .len=(char)7 }, 
    { .run=(char)0, .level=(char)9, .len=(char)7 }, 
    { .run=(char)0, .level=(char)12, .len=(char)8 }, 
    { .run=(char)0, .level=(char)13, .len=(char)8 }, 
    { .run=(char)2, .level=(char)3, .len=(char)8 }, 
    { .run=(char)4, .level=(char)2, .len=(char)8 }, 
    { .run=(char)0, .level=(char)14, .len=(char)8 }, 
    { .run=(char)0, .level=(char)15, .len=(char)8 } };
// c::DCTtab1
// file src/getblk.c line 92
struct anon$1 DCTtab1[8l];
// c::DCTtab1
// file src/getblk.c line 92
struct anon$1 DCTtab1[8l] = { { .run=(char)16, .level=(char)1, .len=(char)10 }, 
    { .run=(char)5, .level=(char)2, .len=(char)10 }, 
    { .run=(char)0, .level=(char)7, .len=(char)10 }, 
    { .run=(char)2, .level=(char)3, .len=(char)10 }, 
    { .run=(char)1, .level=(char)4, .len=(char)10 }, 
    { .run=(char)15, .level=(char)1, .len=(char)10 }, 
    { .run=(char)14, .level=(char)1, .len=(char)10 }, 
    { .run=(char)4, .level=(char)2, .len=(char)10 } };
// c::DCTtab1a
// file src/getblk.c line 94
struct anon$1 DCTtab1a[8l];
// c::DCTtab1a
// file src/getblk.c line 94
struct anon$1 DCTtab1a[8l] = { { .run=(char)5, .level=(char)2, .len=(char)9 }, 
    { .run=(char)5, .level=(char)2, .len=(char)9 }, 
    { .run=(char)14, .level=(char)1, .len=(char)9 }, 
    { .run=(char)14, .level=(char)1, .len=(char)9 }, 
    { .run=(char)2, .level=(char)4, .len=(char)10 }, 
    { .run=(char)16, .level=(char)1, .len=(char)10 }, 
    { .run=(char)15, .level=(char)1, .len=(char)9 }, 
    { .run=(char)15, .level=(char)1, .len=(char)9 } };
// c::DCTtab2
// file src/getblk.c line 93
struct anon$1 DCTtab2[16l];
// c::DCTtab2
// file src/getblk.c line 93
struct anon$1 DCTtab2[16l] = { { .run=(char)0, .level=(char)11, .len=(char)12 }, 
    { .run=(char)8, .level=(char)2, .len=(char)12 }, 
    { .run=(char)4, .level=(char)3, .len=(char)12 }, 
    { .run=(char)0, .level=(char)10, .len=(char)12 }, 
    { .run=(char)2, .level=(char)4, .len=(char)12 }, 
    { .run=(char)7, .level=(char)2, .len=(char)12 }, 
    { .run=(char)21, .level=(char)1, .len=(char)12 }, 
    { .run=(char)20, .level=(char)1, .len=(char)12 }, 
    { .run=(char)0, .level=(char)9, .len=(char)12 }, 
    { .run=(char)19, .level=(char)1, .len=(char)12 }, 
    { .run=(char)18, .level=(char)1, .len=(char)12 }, 
    { .run=(char)1, .level=(char)5, .len=(char)12 }, 
    { .run=(char)3, .level=(char)3, .len=(char)12 }, 
    { .run=(char)0, .level=(char)8, .len=(char)12 }, 
    { .run=(char)6, .level=(char)2, .len=(char)12 }, 
    { .run=(char)17, .level=(char)1, .len=(char)12 } };
// c::DCTtab3
// file src/getblk.c line 93
struct anon$1 DCTtab3[16l];
// c::DCTtab3
// file src/getblk.c line 93
struct anon$1 DCTtab3[16l] = { { .run=(char)10, .level=(char)2, .len=(char)13 }, 
    { .run=(char)9, .level=(char)2, .len=(char)13 }, 
    { .run=(char)5, .level=(char)3, .len=(char)13 }, 
    { .run=(char)3, .level=(char)4, .len=(char)13 }, 
    { .run=(char)2, .level=(char)5, .len=(char)13 }, 
    { .run=(char)1, .level=(char)7, .len=(char)13 }, 
    { .run=(char)1, .level=(char)6, .len=(char)13 }, 
    { .run=(char)0, .level=(char)15, .len=(char)13 }, 
    { .run=(char)0, .level=(char)14, .len=(char)13 }, 
    { .run=(char)0, .level=(char)13, .len=(char)13 }, 
    { .run=(char)0, .level=(char)12, .len=(char)13 }, 
    { .run=(char)26, .level=(char)1, .len=(char)13 }, 
    { .run=(char)25, .level=(char)1, .len=(char)13 }, 
    { .run=(char)24, .level=(char)1, .len=(char)13 }, 
    { .run=(char)23, .level=(char)1, .len=(char)13 }, 
    { .run=(char)22, .level=(char)1, .len=(char)13 } };
// c::DCTtab4
// file src/getblk.c line 93
struct anon$1 DCTtab4[16l];
// c::DCTtab4
// file src/getblk.c line 93
struct anon$1 DCTtab4[16l] = { { .run=(char)0, .level=(char)31, .len=(char)14 }, 
    { .run=(char)0, .level=(char)30, .len=(char)14 }, 
    { .run=(char)0, .level=(char)29, .len=(char)14 }, 
    { .run=(char)0, .level=(char)28, .len=(char)14 }, 
    { .run=(char)0, .level=(char)27, .len=(char)14 }, 
    { .run=(char)0, .level=(char)26, .len=(char)14 }, 
    { .run=(char)0, .level=(char)25, .len=(char)14 }, 
    { .run=(char)0, .level=(char)24, .len=(char)14 }, 
    { .run=(char)0, .level=(char)23, .len=(char)14 }, 
    { .run=(char)0, .level=(char)22, .len=(char)14 }, 
    { .run=(char)0, .level=(char)21, .len=(char)14 }, 
    { .run=(char)0, .level=(char)20, .len=(char)14 }, 
    { .run=(char)0, .level=(char)19, .len=(char)14 }, 
    { .run=(char)0, .level=(char)18, .len=(char)14 }, 
    { .run=(char)0, .level=(char)17, .len=(char)14 }, 
    { .run=(char)0, .level=(char)16, .len=(char)14 } };
// c::DCTtab5
// file src/getblk.c line 93
struct anon$1 DCTtab5[16l];
// c::DCTtab5
// file src/getblk.c line 93
struct anon$1 DCTtab5[16l] = { { .run=(char)0, .level=(char)40, .len=(char)15 }, 
    { .run=(char)0, .level=(char)39, .len=(char)15 }, 
    { .run=(char)0, .level=(char)38, .len=(char)15 }, 
    { .run=(char)0, .level=(char)37, .len=(char)15 }, 
    { .run=(char)0, .level=(char)36, .len=(char)15 }, 
    { .run=(char)0, .level=(char)35, .len=(char)15 }, 
    { .run=(char)0, .level=(char)34, .len=(char)15 }, 
    { .run=(char)0, .level=(char)33, .len=(char)15 }, 
    { .run=(char)0, .level=(char)32, .len=(char)15 }, 
    { .run=(char)1, .level=(char)14, .len=(char)15 }, 
    { .run=(char)1, .level=(char)13, .len=(char)15 }, 
    { .run=(char)1, .level=(char)12, .len=(char)15 }, 
    { .run=(char)1, .level=(char)11, .len=(char)15 }, 
    { .run=(char)1, .level=(char)10, .len=(char)15 }, 
    { .run=(char)1, .level=(char)9, .len=(char)15 }, 
    { .run=(char)1, .level=(char)8, .len=(char)15 } };
// c::DCTtab6
// file src/getblk.c line 93
struct anon$1 DCTtab6[16l];
// c::DCTtab6
// file src/getblk.c line 93
struct anon$1 DCTtab6[16l] = { { .run=(char)1, .level=(char)18, .len=(char)16 }, 
    { .run=(char)1, .level=(char)17, .len=(char)16 }, 
    { .run=(char)1, .level=(char)16, .len=(char)16 }, 
    { .run=(char)1, .level=(char)15, .len=(char)16 }, 
    { .run=(char)6, .level=(char)3, .len=(char)16 }, 
    { .run=(char)16, .level=(char)2, .len=(char)16 }, 
    { .run=(char)15, .level=(char)2, .len=(char)16 }, 
    { .run=(char)14, .level=(char)2, .len=(char)16 }, 
    { .run=(char)13, .level=(char)2, .len=(char)16 }, 
    { .run=(char)12, .level=(char)2, .len=(char)16 }, 
    { .run=(char)11, .level=(char)2, .len=(char)16 }, 
    { .run=(char)31, .level=(char)1, .len=(char)16 }, 
    { .run=(char)30, .level=(char)1, .len=(char)16 }, 
    { .run=(char)29, .level=(char)1, .len=(char)16 }, 
    { .run=(char)28, .level=(char)1, .len=(char)16 }, 
    { .run=(char)27, .level=(char)1, .len=(char)16 } };
// c::DCTtabfirst
// file src/getblk.c line 92
struct anon$1 DCTtabfirst[12l];
// c::DCTtabfirst
// file src/getblk.c line 92
struct anon$1 DCTtabfirst[12l] = { { .run=(char)0, .level=(char)2, .len=(char)4 }, 
    { .run=(char)2, .level=(char)1, .len=(char)4 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)0, .level=(char)1, .len=(char)1 }, 
    { .run=(char)0, .level=(char)1, .len=(char)1 }, 
    { .run=(char)0, .level=(char)1, .len=(char)1 }, 
    { .run=(char)0, .level=(char)1, .len=(char)1 }, 
    { .run=(char)0, .level=(char)1, .len=(char)1 }, 
    { .run=(char)0, .level=(char)1, .len=(char)1 }, 
    { .run=(char)0, .level=(char)1, .len=(char)1 }, 
    { .run=(char)0, .level=(char)1, .len=(char)1 } };
// c::DCTtabnext
// file src/getblk.c line 92
struct anon$1 DCTtabnext[12l];
// c::DCTtabnext
// file src/getblk.c line 92
struct anon$1 DCTtabnext[12l] = { { .run=(char)0, .level=(char)2, .len=(char)4 }, 
    { .run=(char)2, .level=(char)1, .len=(char)4 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)1, .level=(char)1, .len=(char)3 }, 
    { .run=(char)64, .level=(char)0, .len=(char)2 }, 
    { .run=(char)64, .level=(char)0, .len=(char)2 }, 
    { .run=(char)64, .level=(char)0, .len=(char)2 }, 
    { .run=(char)64, .level=(char)0, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 }, 
    { .run=(char)0, .level=(char)1, .len=(char)2 } };
// c::DCchromtab0
// file src/getvlc.h line 343
static struct anon$3 DCchromtab0[32l];
// c::DCchromtab0
// file src/getvlc.h line 343
static struct anon$3 DCchromtab0[32l] = { { .val=(char)0, .len=(char)2 }, { .val=(char)0, .len=(char)2 }, { .val=(char)0, .len=(char)2 }, { .val=(char)0, .len=(char)2 }, { .val=(char)0, .len=(char)2 }, { .val=(char)0, .len=(char)2 }, { .val=(char)0, .len=(char)2 }, { .val=(char)0, .len=(char)2 }, { .val=(char)1, .len=(char)2 }, { .val=(char)1, .len=(char)2 }, { .val=(char)1, .len=(char)2 }, { .val=(char)1, .len=(char)2 }, { .val=(char)1, .len=(char)2 }, { .val=(char)1, .len=(char)2 }, { .val=(char)1, .len=(char)2 }, { .val=(char)1, .len=(char)2 }, { .val=(char)2, .len=(char)2 }, { .val=(char)2, .len=(char)2 }, { .val=(char)2, .len=(char)2 }, { .val=(char)2, .len=(char)2 }, { .val=(char)2, .len=(char)2 }, { .val=(char)2, .len=(char)2 }, { .val=(char)2, .len=(char)2 }, { .val=(char)2, .len=(char)2 }, { .val=(char)3, .len=(char)3 }, { .val=(char)3, .len=(char)3 }, { .val=(char)3, .len=(char)3 }, { .val=(char)3, .len=(char)3 }, { .val=(char)4, .len=(char)4 }, { .val=(char)4, .len=(char)4 }, { .val=(char)5, .len=(char)5 }, { .val=(char)-1, .len=(char)0 } };
// c::DCchromtab1
// file src/getvlc.h line 351
static struct anon$3 DCchromtab1[32l];
// c::DCchromtab1
// file src/getvlc.h line 351
static struct anon$3 DCchromtab1[32l] = { { .val=(char)6, .len=(char)6 }, { .val=(char)6, .len=(char)6 }, { .val=(char)6, .len=(char)6 }, { .val=(char)6, .len=(char)6 }, { .val=(char)6, .len=(char)6 }, { .val=(char)6, .len=(char)6 }, { .val=(char)6, .len=(char)6 }, { .val=(char)6, .len=(char)6 }, { .val=(char)6, .len=(char)6 }, { .val=(char)6, .len=(char)6 }, { .val=(char)6, .len=(char)6 }, { .val=(char)6, .len=(char)6 }, { .val=(char)6, .len=(char)6 }, { .val=(char)6, .len=(char)6 }, { .val=(char)6, .len=(char)6 }, { .val=(char)6, .len=(char)6 }, { .val=(char)7, .len=(char)7 }, { .val=(char)7, .len=(char)7 }, { .val=(char)7, .len=(char)7 }, { .val=(char)7, .len=(char)7 }, { .val=(char)7, .len=(char)7 }, { .val=(char)7, .len=(char)7 }, { .val=(char)7, .len=(char)7 }, { .val=(char)7, .len=(char)7 }, { .val=(char)8, .len=(char)8 }, { .val=(char)8, .len=(char)8 }, { .val=(char)8, .len=(char)8 }, { .val=(char)8, .len=(char)8 }, { .val=(char)9, .len=(char)9 }, { .val=(char)9, .len=(char)9 }, { .val=(char)10, .len=(char)10 }, { .val=(char)11, .len=(char)10 } };
// c::DClumtab0
// file src/getvlc.h line 329
static struct anon$3 DClumtab0[32l];
// c::DClumtab0
// file src/getvlc.h line 329
static struct anon$3 DClumtab0[32l] = { { .val=(char)1, .len=(char)2 }, { .val=(char)1, .len=(char)2 }, { .val=(char)1, .len=(char)2 }, { .val=(char)1, .len=(char)2 }, { .val=(char)1, .len=(char)2 }, { .val=(char)1, .len=(char)2 }, { .val=(char)1, .len=(char)2 }, { .val=(char)1, .len=(char)2 }, { .val=(char)2, .len=(char)2 }, { .val=(char)2, .len=(char)2 }, { .val=(char)2, .len=(char)2 }, { .val=(char)2, .len=(char)2 }, { .val=(char)2, .len=(char)2 }, { .val=(char)2, .len=(char)2 }, { .val=(char)2, .len=(char)2 }, { .val=(char)2, .len=(char)2 }, { .val=(char)0, .len=(char)3 }, { .val=(char)0, .len=(char)3 }, { .val=(char)0, .len=(char)3 }, { .val=(char)0, .len=(char)3 }, { .val=(char)3, .len=(char)3 }, { .val=(char)3, .len=(char)3 }, { .val=(char)3, .len=(char)3 }, { .val=(char)3, .len=(char)3 }, { .val=(char)4, .len=(char)3 }, { .val=(char)4, .len=(char)3 }, { .val=(char)4, .len=(char)3 }, { .val=(char)4, .len=(char)3 }, { .val=(char)5, .len=(char)4 }, { .val=(char)5, .len=(char)4 }, { .val=(char)6, .len=(char)5 }, { .val=(char)-1, .len=(char)0 } };
// c::DClumtab1
// file src/getvlc.h line 337
static struct anon$3 DClumtab1[16l];
// c::DClumtab1
// file src/getvlc.h line 337
static struct anon$3 DClumtab1[16l] = { { .val=(char)7, .len=(char)6 }, { .val=(char)7, .len=(char)6 }, { .val=(char)7, .len=(char)6 }, { .val=(char)7, .len=(char)6 }, { .val=(char)7, .len=(char)6 }, { .val=(char)7, .len=(char)6 }, { .val=(char)7, .len=(char)6 }, { .val=(char)7, .len=(char)6 }, { .val=(char)8, .len=(char)7 }, { .val=(char)8, .len=(char)7 }, { .val=(char)8, .len=(char)7 }, { .val=(char)8, .len=(char)7 }, { .val=(char)9, .len=(char)8 }, { .val=(char)9, .len=(char)8 }, { .val=(char)10, .len=(char)9 }, { .val=(char)11, .len=(char)9 } };
// c::Decode_Layer
// file src/global.h line 571
signed int Decode_Layer;
// c::Display_Progressive_Flag
// file src/global.h line 349
signed int Display_Progressive_Flag;
// c::Enhancement_Layer_Bitstream_Filename
// file src/global.h line 362
char *Enhancement_Layer_Bitstream_Filename;
// c::Error_Text
// file src/global.h line 366
char Error_Text[256l];
// c::Ersatz_Flag
// file src/global.h line 350
signed int Ersatz_Flag;
// c::Fault_Flag
// file src/global.h line 342
signed int Fault_Flag;
// c::Frame_Store_Flag
// file src/global.h line 347
signed int Frame_Store_Flag;
// c::Inverse_Table_6_9
// file src/global.h line 307
signed int Inverse_Table_6_9[8l][4l];
// c::Inverse_Table_6_9
// file src/global.h line 307
signed int Inverse_Table_6_9[8l][4l] = { { 117504, 138453, 13954, 34903 }, { 117504, 138453, 13954, 34903 }, { 104597, 132201, 25675, 53279 }, { 104597, 132201, 25675, 53279 }, { 104448, 132798, 24759, 53109 }, { 104597, 132201, 25675, 53279 }, { 104597, 132201, 25675, 53279 }, { 117579, 136230, 16907, 35559 } };
// c::Lower_Layer_Picture_Filename
// file src/global.h line 383
char *Lower_Layer_Picture_Filename;
// c::MBAtab1
// file src/getvlc.h line 305
static struct anon$3 MBAtab1[16l];
// c::MBAtab1
// file src/getvlc.h line 305
static struct anon$3 MBAtab1[16l] = { { .val=(char)-1, .len=(char)0 }, { .val=(char)-1, .len=(char)0 }, { .val=(char)7, .len=(char)5 }, { .val=(char)6, .len=(char)5 }, { .val=(char)5, .len=(char)4 }, { .val=(char)5, .len=(char)4 }, { .val=(char)4, .len=(char)4 }, { .val=(char)4, .len=(char)4 }, { .val=(char)3, .len=(char)3 }, { .val=(char)3, .len=(char)3 }, { .val=(char)3, .len=(char)3 }, { .val=(char)3, .len=(char)3 }, { .val=(char)2, .len=(char)3 }, { .val=(char)2, .len=(char)3 }, { .val=(char)2, .len=(char)3 }, { .val=(char)2, .len=(char)3 } };
// c::MBAtab2
// file src/getvlc.h line 311
static struct anon$3 MBAtab2[104l];
// c::MBAtab2
// file src/getvlc.h line 311
static struct anon$3 MBAtab2[104l] = { { .val=(char)33, .len=(char)11 }, { .val=(char)32, .len=(char)11 }, { .val=(char)31, .len=(char)11 }, { .val=(char)30, .len=(char)11 }, { .val=(char)29, .len=(char)11 }, { .val=(char)28, .len=(char)11 }, { .val=(char)27, .len=(char)11 }, { .val=(char)26, .len=(char)11 }, { .val=(char)25, .len=(char)11 }, { .val=(char)24, .len=(char)11 }, { .val=(char)23, .len=(char)11 }, { .val=(char)22, .len=(char)11 }, { .val=(char)21, .len=(char)10 }, { .val=(char)21, .len=(char)10 }, { .val=(char)20, .len=(char)10 }, { .val=(char)20, .len=(char)10 }, { .val=(char)19, .len=(char)10 }, { .val=(char)19, .len=(char)10 }, { .val=(char)18, .len=(char)10 }, { .val=(char)18, .len=(char)10 }, { .val=(char)17, .len=(char)10 }, { .val=(char)17, .len=(char)10 }, { .val=(char)16, .len=(char)10 }, { .val=(char)16, .len=(char)10 }, { .val=(char)15, .len=(char)8 }, { .val=(char)15, .len=(char)8 }, { .val=(char)15, .len=(char)8 }, { .val=(char)15, .len=(char)8 }, { .val=(char)15, .len=(char)8 }, { .val=(char)15, .len=(char)8 }, { .val=(char)15, .len=(char)8 }, { .val=(char)15, .len=(char)8 }, { .val=(char)14, .len=(char)8 }, { .val=(char)14, .len=(char)8 }, { .val=(char)14, .len=(char)8 }, { .val=(char)14, .len=(char)8 }, { .val=(char)14, .len=(char)8 }, { .val=(char)14, .len=(char)8 }, { .val=(char)14, .len=(char)8 }, { .val=(char)14, .len=(char)8 }, { .val=(char)13, .len=(char)8 }, { .val=(char)13, .len=(char)8 }, { .val=(char)13, .len=(char)8 }, { .val=(char)13, .len=(char)8 }, { .val=(char)13, .len=(char)8 }, { .val=(char)13, .len=(char)8 }, { .val=(char)13, .len=(char)8 }, { .val=(char)13, .len=(char)8 }, { .val=(char)12, .len=(char)8 }, { .val=(char)12, .len=(char)8 }, { .val=(char)12, .len=(char)8 }, { .val=(char)12, .len=(char)8 }, { .val=(char)12, .len=(char)8 }, { .val=(char)12, .len=(char)8 }, { .val=(char)12, .len=(char)8 }, { .val=(char)12, .len=(char)8 }, { .val=(char)11, .len=(char)8 }, { .val=(char)11, .len=(char)8 }, { .val=(char)11, .len=(char)8 }, { .val=(char)11, .len=(char)8 }, { .val=(char)11, .len=(char)8 }, { .val=(char)11, .len=(char)8 }, { .val=(char)11, .len=(char)8 }, { .val=(char)11, .len=(char)8 }, { .val=(char)10, .len=(char)8 }, { .val=(char)10, .len=(char)8 }, { .val=(char)10, .len=(char)8 }, { .val=(char)10, .len=(char)8 }, { .val=(char)10, .len=(char)8 }, { .val=(char)10, .len=(char)8 }, { .val=(char)10, .len=(char)8 }, { .val=(char)10, .len=(char)8 }, { .val=(char)9, .len=(char)7 }, { .val=(char)9, .len=(char)7 }, { .val=(char)9, .len=(char)7 }, { .val=(char)9, .len=(char)7 }, { .val=(char)9, .len=(char)7 }, { .val=(char)9, .len=(char)7 }, { .val=(char)9, .len=(char)7 }, { .val=(char)9, .len=(char)7 }, { .val=(char)9, .len=(char)7 }, { .val=(char)9, .len=(char)7 }, { .val=(char)9, .len=(char)7 }, { .val=(char)9, .len=(char)7 }, { .val=(char)9, .len=(char)7 }, { .val=(char)9, .len=(char)7 }, { .val=(char)9, .len=(char)7 }, { .val=(char)9, .len=(char)7 }, { .val=(char)8, .len=(char)7 }, { .val=(char)8, .len=(char)7 }, { .val=(char)8, .len=(char)7 }, { .val=(char)8, .len=(char)7 }, { .val=(char)8, .len=(char)7 }, { .val=(char)8, .len=(char)7 }, { .val=(char)8, .len=(char)7 }, { .val=(char)8, .len=(char)7 }, { .val=(char)8, .len=(char)7 }, { .val=(char)8, .len=(char)7 }, { .val=(char)8, .len=(char)7 }, { .val=(char)8, .len=(char)7 }, { .val=(char)8, .len=(char)7 }, { .val=(char)8, .len=(char)7 }, { .val=(char)8, .len=(char)7 }, { .val=(char)8, .len=(char)7 } };
// c::MVtab0
// file src/getvlc.h line 261
static struct anon$3 MVtab0[8l];
// c::MVtab0
// file src/getvlc.h line 261
static struct anon$3 MVtab0[8l] = { { .val=(char)-1, .len=(char)0 }, { .val=(char)3, .len=(char)3 }, { .val=(char)2, .len=(char)2 }, { .val=(char)2, .len=(char)2 }, { .val=(char)1, .len=(char)1 }, { .val=(char)1, .len=(char)1 }, { .val=(char)1, .len=(char)1 }, { .val=(char)1, .len=(char)1 } };
// c::MVtab1
// file src/getvlc.h line 266
static struct anon$3 MVtab1[8l];
// c::MVtab1
// file src/getvlc.h line 266
static struct anon$3 MVtab1[8l] = { { .val=(char)-1, .len=(char)0 }, { .val=(char)-1, .len=(char)0 }, { .val=(char)-1, .len=(char)0 }, { .val=(char)7, .len=(char)6 }, { .val=(char)6, .len=(char)6 }, { .val=(char)5, .len=(char)6 }, { .val=(char)4, .len=(char)5 }, { .val=(char)4, .len=(char)5 } };
// c::MVtab2
// file src/getvlc.h line 271
static struct anon$3 MVtab2[12l];
// c::MVtab2
// file src/getvlc.h line 271
static struct anon$3 MVtab2[12l] = { { .val=(char)16, .len=(char)9 }, { .val=(char)15, .len=(char)9 }, { .val=(char)14, .len=(char)9 }, { .val=(char)13, .len=(char)9 }, { .val=(char)12, .len=(char)9 }, { .val=(char)11, .len=(char)9 }, { .val=(char)10, .len=(char)8 }, { .val=(char)10, .len=(char)8 }, { .val=(char)9, .len=(char)8 }, { .val=(char)9, .len=(char)8 }, { .val=(char)8, .len=(char)8 }, { .val=(char)8, .len=(char)8 } };
// c::Main_Bitstream_Filename
// file src/global.h line 361
char *Main_Bitstream_Filename;
// c::Main_Bitstream_Flag
// file src/global.h line 355
signed int Main_Bitstream_Flag;
// c::Non_Linear_quantizer_scale
// file src/global.h line 280
unsigned char Non_Linear_quantizer_scale[32l];
// c::Non_Linear_quantizer_scale
// file src/global.h line 280
unsigned char Non_Linear_quantizer_scale[32l] = { (unsigned char)0, (unsigned char)1, (unsigned char)2, (unsigned char)3, (unsigned char)4, (unsigned char)5, (unsigned char)6, (unsigned char)7, (unsigned char)8, (unsigned char)10, (unsigned char)12, (unsigned char)14, (unsigned char)16, (unsigned char)18, (unsigned char)20, (unsigned char)22, (unsigned char)24, (unsigned char)28, (unsigned char)32, (unsigned char)36, (unsigned char)40, (unsigned char)44, (unsigned char)48, (unsigned char)52, (unsigned char)56, (unsigned char)64, (unsigned char)72, (unsigned char)80, (unsigned char)88, (unsigned char)96, (unsigned char)104, (unsigned char)112 };
// c::Output_Picture_Filename
// file src/global.h line 359
char *Output_Picture_Filename;
// c::Output_Type
// file src/global.h line 336
signed int Output_Type;
// c::PMBtab0
// file src/getvlc.h line 98
static struct anon$3 PMBtab0[8l];
// c::PMBtab0
// file src/getvlc.h line 98
static struct anon$3 PMBtab0[8l] = { { .val=(char)-1, .len=(char)0 }, { .val=(char)8, .len=(char)3 }, { .val=(char)2, .len=(char)2 }, { .val=(char)2, .len=(char)2 }, { .val=(char)(8 | 2), .len=(char)1 }, { .val=(char)(8 | 2), .len=(char)1 }, { .val=(char)(8 | 2), .len=(char)1 }, { .val=(char)(8 | 2), .len=(char)1 } };
// c::PMBtab1
// file src/getvlc.h line 109
static struct anon$3 PMBtab1[8l];
// c::PMBtab1
// file src/getvlc.h line 109
static struct anon$3 PMBtab1[8l] = { { .val=(char)-1, .len=(char)0 }, { .val=(char)(16 | 1), .len=(char)6 }, { .val=(char)(16 | 2), .len=(char)5 }, { .val=(char)(16 | 2), .len=(char)5 }, { .val=(char)(16 | 8 | 2), .len=(char)5 }, 
    { .val=(char)(16 | 8 | 2), .len=(char)5 }, 
    { .val=(char)1, .len=(char)5 }, { .val=(char)1, .len=(char)5 } };
// c::Quiet_Flag
// file src/global.h line 340
signed int Quiet_Flag;
// c::RND_INV_CORR
// file src/idct.c line 292
const signed short int RND_INV_CORR;
// c::RND_INV_CORR
// file src/idct.c line 292
const signed short int RND_INV_CORR = (const signed short int)(16 * (4 - 3) - 1);
// c::RND_INV_ROW
// file src/idct.c line 290
const signed short int RND_INV_ROW;
// c::RND_INV_ROW
// file src/idct.c line 290
const signed short int RND_INV_ROW = (const signed short int)(1024 * (6 - 4));
// c::Reference_IDCT_Flag
// file src/global.h line 346
signed int Reference_IDCT_Flag;
// c::SNRMBtab
// file src/getvlc.h line 249
static struct anon$3 SNRMBtab[8l];
// c::SNRMBtab
// file src/getvlc.h line 249
static struct anon$3 SNRMBtab[8l] = { { .val=(char)-1, .len=(char)0 }, { .val=(char)0, .len=(char)3 }, { .val=(char)(16 | 2), .len=(char)2 }, { .val=(char)(16 | 2), .len=(char)2 }, { .val=(char)2, .len=(char)1 }, { .val=(char)2, .len=(char)1 }, { .val=(char)2, .len=(char)1 }, { .val=(char)2, .len=(char)1 } };
// c::Second_Field
// file src/global.h line 394
signed int Second_Field;
// c::Spatial_Flag
// file src/global.h line 345
signed int Spatial_Flag;
// c::Stats_Flag
// file src/global.h line 353
signed int Stats_Flag;
// c::Substitute_Picture_Filename
// file src/global.h line 360
char *Substitute_Picture_Filename;
// c::System_Stream_Flag
// file src/global.h line 348
signed int System_Stream_Flag;
// c::Temporal_Reference_Base
// file src/gethdr.c line 114
static signed int Temporal_Reference_Base;
// c::Temporal_Reference_Base
// file src/gethdr.c line 114
static signed int Temporal_Reference_Base = 0;
// c::Temporal_Reference_GOP_Reset
// file src/gethdr.c line 116
static signed int Temporal_Reference_GOP_Reset;
// c::Temporal_Reference_GOP_Reset
// file src/gethdr.c line 116
static signed int Temporal_Reference_GOP_Reset = 0;
// c::Trace_Flag
// file src/global.h line 341
signed int Trace_Flag;
// c::True_Framenum
// file src/global.h line 582
signed int True_Framenum;
// c::True_Framenum_max
// file src/gethdr.c line 115
static signed int True_Framenum_max;
// c::True_Framenum_max
// file src/gethdr.c line 115
static signed int True_Framenum_max = -1;
// c::Two_Streams
// file src/global.h line 344
signed int Two_Streams;
// c::User_Data_Flag
// file src/global.h line 354
signed int User_Data_Flag;
// c::Verbose_Flag
// file src/global.h line 343
signed int Verbose_Flag;
// c::Verify_Flag
// file src/global.h line 352
signed int Verify_Flag;
// c::Version
// file src/global.h line 228
char Version[28l];
// c::Version
// file src/global.h line 228
char Version[28l] = { 109, 112, 101, 103, 50, 100, 101, 99, 111, 100, 101, 32, 86, 49, 46, 50, 97, 44, 32, 57, 54, 47, 48, 55, 47, 49, 57, 0 };
// c::aspect_ratio_information
// file src/global.h line 410
signed int aspect_ratio_information;
// c::auxframe
// file src/global.h line 373
unsigned char *auxframe[3l];
// c::backward_f_code
// file src/global.h line 440
signed int backward_f_code;
// c::backward_reference_frame
// file src/global.h line 370
unsigned char *backward_reference_frame[3l];
// c::base
// file src/global.h line 550
struct layer_data base;
// c::bit_rate
// file src/global.h line 402
double bit_rate;
// c::bit_rate_value
// file src/global.h line 412
signed int bit_rate_value;
// c::block_count
// file src/global.h line 393
signed int block_count;
// c::broken_link
// file src/global.h line 510
signed int broken_link;
// c::burst_amplitude
// file src/global.h line 461
signed int burst_amplitude;
// c::c
// file src/idctref.c line 108
static double c[8l][8l];
// c::chroma_420_type
// file src/global.h line 455
signed int chroma_420_type;
// c::chroma_format
// file src/global.h line 419
signed int chroma_format;
// c::closed_gop
// file src/global.h line 509
signed int closed_gop;
// c::color_description
// file src/global.h line 426
signed int color_description;
// c::color_primaries
// file src/global.h line 427
signed int color_primaries;
// c::composite_display_flag
// file src/global.h line 457
signed int composite_display_flag;
// c::concealment_motion_vectors
// file src/global.h line 449
signed int concealment_motion_vectors;
// c::constrained_parameters_flag
// file src/global.h line 414
signed int constrained_parameters_flag;
// c::copyright_flag
// file src/global.h line 496
signed int copyright_flag;
// c::copyright_identifier
// file src/global.h line 497
signed int copyright_identifier;
// c::copyright_number_1
// file src/global.h line 499
signed int copyright_number_1;
// c::copyright_number_2
// file src/global.h line 500
signed int copyright_number_2;
// c::copyright_number_3
// file src/global.h line 501
signed int copyright_number_3;
// c::current_frame
// file src/global.h line 374
unsigned char *current_frame[3l];
// c::default_intra_quantizer_matrix
// file src/global.h line 263
unsigned char default_intra_quantizer_matrix[64l];
// c::default_intra_quantizer_matrix
// file src/global.h line 263
unsigned char default_intra_quantizer_matrix[64l] = { (unsigned char)8, (unsigned char)16, (unsigned char)19, (unsigned char)22, (unsigned char)26, (unsigned char)27, (unsigned char)29, (unsigned char)34, (unsigned char)16, (unsigned char)16, (unsigned char)22, (unsigned char)24, (unsigned char)27, (unsigned char)29, (unsigned char)34, (unsigned char)37, (unsigned char)19, (unsigned char)22, (unsigned char)26, (unsigned char)27, (unsigned char)29, (unsigned char)34, (unsigned char)34, (unsigned char)38, (unsigned char)22, (unsigned char)22, (unsigned char)26, (unsigned char)27, (unsigned char)29, (unsigned char)34, (unsigned char)37, (unsigned char)40, (unsigned char)22, (unsigned char)26, (unsigned char)27, (unsigned char)29, (unsigned char)32, (unsigned char)35, (unsigned char)40, (unsigned char)48, (unsigned char)26, (unsigned char)27, (unsigned char)29, (unsigned char)32, (unsigned char)35, (unsigned char)40, (unsigned char)48, (unsigned char)58, (unsigned char)26, (unsigned char)27, (unsigned char)29, (unsigned char)34, (unsigned char)38, (unsigned char)46, (unsigned char)56, (unsigned char)69, (unsigned char)27, (unsigned char)29, (unsigned char)35, (unsigned char)38, (unsigned char)46, (unsigned char)56, (unsigned char)69, (unsigned char)83 };
// c::display_horizontal_size
// file src/global.h line 430
signed int display_horizontal_size;
// c::display_vertical_size
// file src/global.h line 431
signed int display_vertical_size;
// c::drop_flag
// file src/global.h line 504
signed int drop_flag;
// c::enhan
// file src/global.h line 550
struct layer_data enhan;
// c::f_code
// file src/global.h line 444
signed int f_code[2l][2l];
// c::field_sequence
// file src/global.h line 459
signed int field_sequence;
// c::forward_f_code
// file src/global.h line 438
signed int forward_f_code;
// c::forward_reference_frame
// file src/global.h line 371
unsigned char *forward_reference_frame[3l];
// c::frame
// file src/global.h line 508
signed int frame;
// c::frame_buf_offset
// file src/global.h line 588
unsigned int frame_buf_offset;
// c::frame_buf_ptr
// file src/global.h line 586
unsigned char *frame_buf_ptr;
// c::frame_buf_size
// file src/global.h line 587
unsigned int frame_buf_size;
// c::frame_buffer
// file src/global.h line 585
unsigned char *frame_buffer;
// c::frame_center_horizontal_offset
// file src/global.h line 467
signed int frame_center_horizontal_offset[3l];
// c::frame_center_vertical_offset
// file src/global.h line 468
signed int frame_center_vertical_offset[3l];
// c::frame_pred_frame_dct
// file src/global.h line 448
signed int frame_pred_frame_dct;
// c::frame_rate
// file src/global.h line 403
double frame_rate;
// c::frame_rate_Table
// file src/gethdr.c line 119
static double frame_rate_Table[16l];
// c::frame_rate_Table
// file src/gethdr.c line 119
static double frame_rate_Table[16l] = { 0.000000, (23.000000 * 1000.000000) / 1001.000000, 
    24.000000, 25.000000, (30.000000 * 1000.000000) / 1001.000000, 
    30.000000, 50.000000, (60.000000 * 1000.000000) / 1001.000000, 
    60.000000, (double)-1, (double)-1, (double)-1, (double)-1, (double)-1, (double)-1, (double)-1 };
// c::frame_rate_code
// file src/global.h line 411
signed int frame_rate_code;
// c::frame_rate_extension_d
// file src/global.h line 422
signed int frame_rate_extension_d;
// c::frame_rate_extension_n
// file src/global.h line 421
signed int frame_rate_extension_n;
// c::full_pel_backward_vector
// file src/global.h line 439
signed int full_pel_backward_vector;
// c::full_pel_forward_vector
// file src/global.h line 437
signed int full_pel_forward_vector;
// c::global_MBA
// file src/global.h line 580
signed int global_MBA;
// c::global_pic
// file src/global.h line 581
signed int global_pic;
// c::hiQdither
// file src/global.h line 337
signed int hiQdither;
// c::horizontal_size
// file src/global.h line 398
signed int horizontal_size;
// c::horizontal_subsampling_factor_m
// file src/global.h line 476
signed int horizontal_subsampling_factor_m;
// c::horizontal_subsampling_factor_n
// file src/global.h line 477
signed int horizontal_subsampling_factor_n;
// c::hour
// file src/global.h line 505
signed int hour;
// c::ic
// file src/idct.c line 145
signed short int ic[8l][8l];
// c::intra_dc_precision
// file src/global.h line 445
signed int intra_dc_precision;
// c::intra_vlc_format
// file src/global.h line 451
signed int intra_vlc_format;
// c::layer_id
// file src/global.h line 473
signed int layer_id;
// c::ld
// file src/global.h line 550
struct layer_data *ld;
// c::level
// file src/global.h line 395
signed int level;
// c::llframe0
// file src/global.h line 379
unsigned char *llframe0[3l];
// c::llframe1
// file src/global.h line 380
unsigned char *llframe1[3l];
// c::lltmp
// file src/global.h line 382
signed short int *lltmp;
// c::low_delay
// file src/global.h line 420
signed int low_delay;
// c::lower_layer_deinterlaced_field_select
// file src/global.h line 488
signed int lower_layer_deinterlaced_field_select;
// c::lower_layer_horizontal_offset
// file src/global.h line 484
signed int lower_layer_horizontal_offset;
// c::lower_layer_prediction_horizontal_size
// file src/global.h line 474
signed int lower_layer_prediction_horizontal_size;
// c::lower_layer_prediction_vertical_size
// file src/global.h line 475
signed int lower_layer_prediction_vertical_size;
// c::lower_layer_progressive_frame
// file src/global.h line 487
signed int lower_layer_progressive_frame;
// c::lower_layer_temporal_reference
// file src/global.h line 483
signed int lower_layer_temporal_reference;
// c::lower_layer_vertical_offset
// file src/global.h line 485
signed int lower_layer_vertical_offset;
// c::matrix_coefficients
// file src/global.h line 429
signed int matrix_coefficients;
// c::mb_height
// file src/global.h line 401
signed int mb_height;
// c::mb_width
// file src/global.h line 400
signed int mb_width;
// c::minute
// file src/global.h line 506
signed int minute;
// c::obfr
// file src/store.c line 110
static unsigned char obfr[8192l];
// c::optr
// file src/store.c line 111
static unsigned char *optr;
// c::original_or_copy
// file src/global.h line 498
signed int original_or_copy;
// c::outfile
// file src/store.c line 112
static signed int outfile;
// c::picture_coding_type
// file src/global.h line 435
signed int picture_coding_type;
// c::picture_structure
// file src/global.h line 446
signed int picture_structure;
// c::profile
// file src/global.h line 395
signed int profile;
// c::profile_and_level_indication
// file src/global.h line 417
signed int profile_and_level_indication;
// c::progressive_frame
// file src/global.h line 456
signed int progressive_frame;
// c::progressive_sequence
// file src/global.h line 418
signed int progressive_sequence;
// c::repeat_first_field
// file src/global.h line 453
signed int repeat_first_field;
// c::scan
// file src/global.h line 242
unsigned char scan[2l][64l];
// c::scan
// file src/global.h line 242
unsigned char scan[2l][64l] = { { (unsigned char)0, (unsigned char)1, (unsigned char)8, (unsigned char)16, (unsigned char)9, (unsigned char)2, (unsigned char)3, (unsigned char)10, (unsigned char)17, (unsigned char)24, (unsigned char)32, (unsigned char)25, (unsigned char)18, (unsigned char)11, (unsigned char)4, (unsigned char)5, (unsigned char)12, (unsigned char)19, (unsigned char)26, (unsigned char)33, (unsigned char)40, (unsigned char)48, (unsigned char)41, (unsigned char)34, (unsigned char)27, (unsigned char)20, (unsigned char)13, (unsigned char)6, (unsigned char)7, (unsigned char)14, (unsigned char)21, (unsigned char)28, (unsigned char)35, (unsigned char)42, (unsigned char)49, (unsigned char)56, (unsigned char)57, (unsigned char)50, (unsigned char)43, (unsigned char)36, (unsigned char)29, (unsigned char)22, (unsigned char)15, (unsigned char)23, (unsigned char)30, (unsigned char)37, (unsigned char)44, (unsigned char)51, (unsigned char)58, (unsigned char)59, (unsigned char)52, (unsigned char)45, (unsigned char)38, (unsigned char)31, (unsigned char)39, (unsigned char)46, (unsigned char)53, (unsigned char)60, (unsigned char)61, (unsigned char)54, (unsigned char)47, (unsigned char)55, (unsigned char)62, (unsigned char)63 }, 
    { (unsigned char)0, (unsigned char)8, (unsigned char)16, (unsigned char)24, (unsigned char)1, (unsigned char)9, (unsigned char)2, (unsigned char)10, (unsigned char)17, (unsigned char)25, (unsigned char)32, (unsigned char)40, (unsigned char)48, (unsigned char)56, (unsigned char)57, (unsigned char)49, (unsigned char)41, (unsigned char)33, (unsigned char)26, (unsigned char)18, (unsigned char)3, (unsigned char)11, (unsigned char)4, (unsigned char)12, (unsigned char)19, (unsigned char)27, (unsigned char)34, (unsigned char)42, (unsigned char)50, (unsigned char)58, (unsigned char)35, (unsigned char)43, (unsigned char)51, (unsigned char)59, (unsigned char)20, (unsigned char)28, (unsigned char)5, (unsigned char)13, (unsigned char)6, (unsigned char)14, (unsigned char)21, (unsigned char)29, (unsigned char)36, (unsigned char)44, (unsigned char)52, (unsigned char)60, (unsigned char)37, (unsigned char)45, (unsigned char)53, (unsigned char)61, (unsigned char)22, (unsigned char)30, (unsigned char)7, (unsigned char)15, (unsigned char)23, (unsigned char)31, (unsigned char)38, (unsigned char)46, (unsigned char)54, (unsigned char)62, (unsigned char)39, (unsigned char)47, (unsigned char)55, (unsigned char)63 } };
// c::sec
// file src/global.h line 507
signed int sec;
// c::spBMBtab0
// file src/getvlc.h line 203
static struct anon$3 spBMBtab0[14l];
// c::spBMBtab0
// file src/getvlc.h line 203
static struct anon$3 spBMBtab0[14l] = { { .val=(char)8, .len=(char)4 }, { .val=(char)(8 | 2), .len=(char)4 }, { .val=(char)4, .len=(char)3 }, { .val=(char)4, .len=(char)3 }, { .val=(char)(4 | 2), .len=(char)3 }, { .val=(char)(4 | 2), .len=(char)3 }, { .val=(char)(8 | 4), .len=(char)2 }, { .val=(char)(8 | 4), .len=(char)2 }, { .val=(char)(8 | 4), .len=(char)2 }, { .val=(char)(8 | 4), .len=(char)2 }, { .val=(char)(8 | 4 | 2), .len=(char)2 }, 
    { .val=(char)(8 | 4 | 2), .len=(char)2 }, 
    { .val=(char)(8 | 4 | 2), .len=(char)2 }, 
    { .val=(char)(8 | 4 | 2), .len=(char)2 } };
// c::spBMBtab1
// file src/getvlc.h line 221
static struct anon$3 spBMBtab1[12l];
// c::spBMBtab1
// file src/getvlc.h line 221
static struct anon$3 spBMBtab1[12l] = { { .val=(char)(16 | 8 | 2), .len=(char)7 }, 
    { .val=(char)(16 | 4 | 2), .len=(char)7 }, 
    { .val=(char)1, .len=(char)7 }, { .val=(char)(16 | 8 | 4 | 2), .len=(char)7 }, 
    { .val=(char)(32 | 8), .len=(char)6 }, { .val=(char)(32 | 8), .len=(char)6 }, { .val=(char)(32 | 8 | 2), .len=(char)6 }, 
    { .val=(char)(32 | 8 | 2), .len=(char)6 }, 
    { .val=(char)(32 | 4), .len=(char)6 }, { .val=(char)(32 | 4), .len=(char)6 }, { .val=(char)(32 | 4 | 2), .len=(char)6 }, 
    { .val=(char)(32 | 4 | 2), .len=(char)6 } };
// c::spBMBtab2
// file src/getvlc.h line 237
static struct anon$3 spBMBtab2[8l];
// c::spBMBtab2
// file src/getvlc.h line 237
static struct anon$3 spBMBtab2[8l] = { { .val=(char)(16 | 1), .len=(char)8 }, { .val=(char)(16 | 1), .len=(char)8 }, { .val=(char)(32 | 16 | 8 | 2), .len=(char)8 }, 
    { .val=(char)(32 | 16 | 8 | 2), .len=(char)8 }, 
    { .val=(char)(32 | 16 | 4 | 2), .len=(char)9 }, 
    { .val=(char)(64 | 16 | 2), .len=(char)9 }, 
    { .val=(char)64, .len=(char)9 }, { .val=(char)(64 | 2), .len=(char)9 } };
// c::spIMBtab
// file src/getvlc.h line 150
static struct anon$3 spIMBtab[16l];
// c::spIMBtab
// file src/getvlc.h line 150
static struct anon$3 spIMBtab[16l] = { { .val=(char)-1, .len=(char)0 }, { .val=(char)64, .len=(char)4 }, { .val=(char)(16 | 1), .len=(char)4 }, { .val=(char)1, .len=(char)4 }, { .val=(char)(64 | 16 | 2), .len=(char)2 }, 
    { .val=(char)(64 | 16 | 2), .len=(char)2 }, 
    { .val=(char)(64 | 16 | 2), .len=(char)2 }, 
    { .val=(char)(64 | 16 | 2), .len=(char)2 }, 
    { .val=(char)(64 | 2), .len=(char)1 }, { .val=(char)(64 | 2), .len=(char)1 }, { .val=(char)(64 | 2), .len=(char)1 }, { .val=(char)(64 | 2), .len=(char)1 }, { .val=(char)(64 | 2), .len=(char)1 }, { .val=(char)(64 | 2), .len=(char)1 }, { .val=(char)(64 | 2), .len=(char)1 }, { .val=(char)(64 | 2), .len=(char)1 } };
// c::spPMBtab0
// file src/getvlc.h line 164
static struct anon$3 spPMBtab0[16l];
// c::spPMBtab0
// file src/getvlc.h line 164
static struct anon$3 spPMBtab0[16l] = { { .val=(char)-1, .len=(char)0 }, { .val=(char)-1, .len=(char)0 }, { .val=(char)8, .len=(char)4 }, { .val=(char)(32 | 8), .len=(char)4 }, { .val=(char)(16 | 8 | 2), .len=(char)3 }, 
    { .val=(char)(16 | 8 | 2), .len=(char)3 }, 
    { .val=(char)(32 | 8 | 2), .len=(char)3 }, 
    { .val=(char)(32 | 8 | 2), .len=(char)3 }, 
    { .val=(char)(8 | 2), .len=(char)2 }, { .val=(char)(8 | 2), .len=(char)2 }, { .val=(char)(8 | 2), .len=(char)2 }, { .val=(char)(8 | 2), .len=(char)2 }, { .val=(char)(32 | 16 | 8 | 2), .len=(char)2 }, 
    { .val=(char)(32 | 16 | 8 | 2), .len=(char)2 }, 
    { .val=(char)(32 | 16 | 8 | 2), .len=(char)2 }, 
    { .val=(char)(32 | 16 | 8 | 2), .len=(char)2 } };
// c::spPMBtab1
// file src/getvlc.h line 183
static struct anon$3 spPMBtab1[16l];
// c::spPMBtab1
// file src/getvlc.h line 183
static struct anon$3 spPMBtab1[16l] = { { .val=(char)-1, .len=(char)0 }, { .val=(char)-1, .len=(char)0 }, { .val=(char)(64 | 16 | 2), .len=(char)7 }, 
    { .val=(char)64, .len=(char)7 }, { .val=(char)2, .len=(char)7 }, { .val=(char)(64 | 2), .len=(char)7 }, { .val=(char)(16 | 1), .len=(char)7 }, { .val=(char)1, .len=(char)7 }, { .val=(char)(16 | 2), .len=(char)6 }, { .val=(char)(16 | 2), .len=(char)6 }, { .val=(char)(32 | 16 | 2), .len=(char)6 }, 
    { .val=(char)(32 | 16 | 2), .len=(char)6 }, 
    { .val=(char)32, .len=(char)6 }, { .val=(char)32, .len=(char)6 }, { .val=(char)(32 | 2), .len=(char)6 }, { .val=(char)(32 | 2), .len=(char)6 } };
// c::spatial_temporal_weight_code_table_index
// file src/global.h line 486
signed int spatial_temporal_weight_code_table_index;
// c::stderr
// file /usr/include/stdio.h line 170
struct _IO_FILE$link3 *stderr;
// c::stdin
// file /usr/include/stdio.h line 168
struct _IO_FILE *stdin;
// c::stdout
// file /usr/include/stdio.h line 169
struct _IO_FILE *stdout;
// c::sub_carrier
// file src/global.h line 460
signed int sub_carrier;
// c::sub_carrier_phase
// file src/global.h line 462
signed int sub_carrier_phase;
// c::substitute_frame
// file src/global.h line 375
unsigned char *substitute_frame[3l];
// c::tab_i_04
// file src/idct.c line 574
signed short int tab_i_04[32l];
// c::tab_i_04
// file src/idct.c line 574
signed short int tab_i_04[32l] = { (signed short int)16384, (signed short int)21407, (signed short int)16384, (signed short int)8867, (signed short int)16384, (signed short int)8867, (signed short int)-16384, (signed short int)-21407, (signed short int)16384, (signed short int)-8867, (signed short int)-16384, (signed short int)21407, (signed short int)16384, (signed short int)-21407, (signed short int)16384, (signed short int)-8867, (signed short int)22725, (signed short int)19266, (signed short int)12873, (signed short int)4520, (signed short int)19266, (signed short int)-4520, (signed short int)-22725, (signed short int)-12873, (signed short int)12873, (signed short int)-22725, (signed short int)4520, (signed short int)19266, (signed short int)4520, (signed short int)-12873, (signed short int)19266, (signed short int)-22725 };
// c::tab_i_17
// file src/idct.c line 588
signed short int tab_i_17[32l];
// c::tab_i_17
// file src/idct.c line 588
signed short int tab_i_17[32l] = { (signed short int)22725, (signed short int)29692, (signed short int)22725, (signed short int)12299, (signed short int)22725, (signed short int)12299, (signed short int)-22725, (signed short int)-29692, (signed short int)22725, (signed short int)-12299, (signed short int)-22725, (signed short int)29692, (signed short int)22725, (signed short int)-29692, (signed short int)22725, (signed short int)-12299, (signed short int)31521, (signed short int)26722, (signed short int)17855, (signed short int)6270, (signed short int)26722, (signed short int)-6270, (signed short int)-31521, (signed short int)-17855, (signed short int)17855, (signed short int)-31521, (signed short int)6270, (signed short int)26722, (signed short int)6270, (signed short int)-17855, (signed short int)26722, (signed short int)-31521 };
// c::tab_i_26
// file src/idct.c line 602
signed short int tab_i_26[32l];
// c::tab_i_26
// file src/idct.c line 602
signed short int tab_i_26[32l] = { (signed short int)21407, (signed short int)27969, (signed short int)21407, (signed short int)11585, (signed short int)21407, (signed short int)11585, (signed short int)-21407, (signed short int)-27969, (signed short int)21407, (signed short int)-11585, (signed short int)-21407, (signed short int)27969, (signed short int)21407, (signed short int)-27969, (signed short int)21407, (signed short int)-11585, (signed short int)29692, (signed short int)25172, (signed short int)16819, (signed short int)5906, (signed short int)25172, (signed short int)-5906, (signed short int)-29692, (signed short int)-16819, (signed short int)16819, (signed short int)-29692, (signed short int)5906, (signed short int)25172, (signed short int)5906, (signed short int)-16819, (signed short int)25172, (signed short int)-29692 };
// c::tab_i_35
// file src/idct.c line 616
signed short int tab_i_35[32l];
// c::tab_i_35
// file src/idct.c line 616
signed short int tab_i_35[32l] = { (signed short int)19266, (signed short int)25172, (signed short int)19266, (signed short int)10426, (signed short int)19266, (signed short int)10426, (signed short int)-19266, (signed short int)-25172, (signed short int)19266, (signed short int)-10426, (signed short int)-19266, (signed short int)25172, (signed short int)19266, (signed short int)-25172, (signed short int)19266, (signed short int)-10426, (signed short int)26722, (signed short int)22654, (signed short int)15137, (signed short int)5315, (signed short int)22654, (signed short int)-5315, (signed short int)-26722, (signed short int)-15137, (signed short int)15137, (signed short int)-26722, (signed short int)5315, (signed short int)22654, (signed short int)5315, (signed short int)-15137, (signed short int)22654, (signed short int)-26722 };
// c::tb
// file src/global.h line 607
struct anon$0 tb[2l];
// c::temporal_reference
// file src/global.h line 434
signed int temporal_reference;
// c::thrd_Incnt
// file src/global.h line 592
signed int thrd_Incnt[2l];
// c::thrd_buf
// file src/global.h line 591
unsigned int thrd_buf[2l];
// c::thrd_ld
// file src/global.h line 632
struct thrd_layer_data thrd_ld[2l];
// c::thrd_ptr
// file src/global.h line 590
unsigned char *thrd_ptr[2l];
// c::thread_data_array
// file src/getpic.c line 1620
struct anon$2 thread_data_array[2l];
// c::top_field_first
// file src/global.h line 447
signed int top_field_first;
// c::transfer_characteristics
// file src/global.h line 428
signed int transfer_characteristics;
// c::v_axis
// file src/global.h line 458
signed int v_axis;
// c::vbv_buffer_size
// file src/global.h line 413
signed int vbv_buffer_size;
// c::vbv_delay
// file src/global.h line 436
signed int vbv_delay;
// c::vertical_size
// file src/global.h line 399
signed int vertical_size;
// c::vertical_subsampling_factor_m
// file src/global.h line 478
signed int vertical_subsampling_factor_m;
// c::vertical_subsampling_factor_n
// file src/global.h line 479
signed int vertical_subsampling_factor_n;
// c::video_format
// file src/global.h line 425
signed int video_format;

// c::Clear_Block
// file src/getpic.c line 727
static void Clear_Block(signed int comp)
{
  signed short int *Block_Ptr;
  signed int i;
  Block_Ptr = ld->block[(signed long int)comp];
  i = 0;
  while(i < 64)
  {
    Block_Ptr[(signed long int)i] = (signed short int)0;
    Block_Ptr[(signed long int)(i + 1)] = (signed short int)0;
    Block_Ptr[(signed long int)(i + 2)] = (signed short int)0;
    Block_Ptr[(signed long int)(i + 3)] = (signed short int)0;
    Block_Ptr[(signed long int)(i + 4)] = (signed short int)0;
    Block_Ptr[(signed long int)(i + 5)] = (signed short int)0;
    Block_Ptr[(signed long int)(i + 6)] = (signed short int)0;
    Block_Ptr[(signed long int)(i + 7)] = (signed short int)0;
    i = i + 8;
  }
}

// c::Clear_Options
// file src/mpeg2dec.c line 791
static void Clear_Options()
{
  Verbose_Flag = 0;
  Output_Type = 0;
  Output_Picture_Filename = " ";
  hiQdither = 0;
  Output_Type = 0;
  Frame_Store_Flag = 0;
  Spatial_Flag = 0;
  Lower_Layer_Picture_Filename = " ";
  Reference_IDCT_Flag = 0;
  Trace_Flag = 0;
  Quiet_Flag = 0;
  Ersatz_Flag = 0;
  Substitute_Picture_Filename = " ";
  Two_Streams = 0;
  Enhancement_Layer_Bitstream_Filename = " ";
  Big_Picture_Flag = 0;
  Main_Bitstream_Flag = 0;
  Main_Bitstream_Filename = " ";
  Verify_Flag = 0;
  Stats_Flag = 0;
  User_Data_Flag = 0;
}

// c::Copy_Frame
// file src/subspic.c line 401
static void Copy_Frame(unsigned char *src, unsigned char *dst, signed int width, signed int height, signed int parity, signed int field_mode)
{
  signed int row;
  signed int col;
  signed int s;
  signed int d;
  signed int incr;
  d = 0;
  s = d;
  if(!(field_mode == 0))
  {
    incr = 2;
    if(parity == 0)
      s = s + width;

  }

  else
    incr = 1;
  row = 0;
  while(!(row >= height))
  {
    col = 0;
    while(!(col >= width))
    {
      dst[(signed long int)(d + col)] = src[(signed long int)(s + col)];
      col = col + 1;
    }
    d = d + width * incr;
    s = s + width * incr;
    row = row + incr;
  }
}

// c::Decode_Bitstream
// file src/mpeg2dec.c line 679
static signed int Decode_Bitstream(void)
{
  signed int ret;
  signed int Bitstream_Framenum = 0;
  do
  {
    ret=Headers();
    if(ret == 1)
      ret=video_sequence(&Bitstream_Framenum);

    else
      return ret;
  }
  while(TRUE);
}

// c::Decode_MPEG1_Intra_Block
// file src/getblk.c line 99
void Decode_MPEG1_Intra_Block(signed int comp, signed int *dc_dct_pred)
{
  signed int val;
  signed int i;
  signed int j;
  signed int sign;
  unsigned int code;
  struct anon$1 *tab;
  signed short int *bp = ld->block[(signed long int)comp];
  signed int return_value_Get_Luma_DC_dct_diff$1;
  signed int return_value_Get_Chroma_DC_dct_diff$2;
  signed int return_value_Get_Chroma_DC_dct_diff$3;
  if(comp < 4)
  {
    return_value_Get_Luma_DC_dct_diff$1=Get_Luma_DC_dct_diff();
    dc_dct_pred[(signed long int)0] = dc_dct_pred[(signed long int)0] + return_value_Get_Luma_DC_dct_diff$1;
    bp[(signed long int)0] = (signed short int)(dc_dct_pred[(signed long int)0] << 3);
  }

  else
    if(comp == 4)
    {
      return_value_Get_Chroma_DC_dct_diff$2=Get_Chroma_DC_dct_diff();
      dc_dct_pred[(signed long int)1] = dc_dct_pred[(signed long int)1] + return_value_Get_Chroma_DC_dct_diff$2;
      bp[(signed long int)0] = (signed short int)(dc_dct_pred[(signed long int)1] << 3);
    }

    else
    {
      return_value_Get_Chroma_DC_dct_diff$3=Get_Chroma_DC_dct_diff();
      dc_dct_pred[(signed long int)2] = dc_dct_pred[(signed long int)2] + return_value_Get_Chroma_DC_dct_diff$3;
      bp[(signed long int)0] = (signed short int)(dc_dct_pred[(signed long int)2] << 3);
    }
  if(!(Fault_Flag == 0))
    return;

  if(picture_coding_type == 4)
    return;

  i = 1;
  unsigned int return_value_Get_Bits$6;
  unsigned int return_value_Get_Bits$7;
  do
  {
    code=Show_Bits(16);
    if(code >= 16384u)
      tab = &DCTtabnext[(signed long int)((code >> 12) - (unsigned int)4)];

    else
      if(code >= 1024u)
        tab = &DCTtab0[(signed long int)((code >> 8) - (unsigned int)4)];

      else
        if(code >= 512u)
          tab = &DCTtab1[(signed long int)((code >> 6) - (unsigned int)8)];

        else
          if(code >= 256u)
            tab = &DCTtab2[(signed long int)((code >> 4) - (unsigned int)16)];

          else
            if(code >= 128u)
              tab = &DCTtab3[(signed long int)((code >> 3) - (unsigned int)16)];

            else
              if(code >= 64u)
                tab = &DCTtab4[(signed long int)((code >> 2) - (unsigned int)16)];

              else
                if(code >= 32u)
                  tab = &DCTtab5[(signed long int)((code >> 1) - (unsigned int)16)];

                else
                  if(code >= 16u)
                    tab = &DCTtab6[(signed long int)(code - (unsigned int)16)];

                  else
                  {
                    if(Quiet_Flag == 0)
                      printf("invalid Huffman code in Decode_MPEG1_Intra_Block()\n");

                    Fault_Flag = 1;
                    return;
                  }
    Flush_Buffer((signed int)tab->len);
    if((signed int)tab->run == 64)
      return;

    if((signed int)tab->run == 65)
    {
      unsigned int return_value_Get_Bits$4;
      return_value_Get_Bits$4=Get_Bits(6);
      i = i + (signed int)return_value_Get_Bits$4;
      unsigned int return_value_Get_Bits$5;
      return_value_Get_Bits$5=Get_Bits(8);
      val = (signed int)return_value_Get_Bits$5;
      if(val == 0)
      {
        return_value_Get_Bits$6=Get_Bits(8);
        val = (signed int)return_value_Get_Bits$6;
      }

      else
        if(val == 128)
        {
          return_value_Get_Bits$7=Get_Bits(8);
          val = (signed int)(return_value_Get_Bits$7 - (unsigned int)256);
        }

        else
          if(val > 128)
            val = val - 256;

      sign = (signed int)(val < 0);
      if(!(sign == 0))
        val = -val;

    }

    else
    {
      i = i + (signed int)tab->run;
      val = (signed int)tab->level;
      unsigned int return_value_Get_Bits$8;
      return_value_Get_Bits$8=Get_Bits(1);
      sign = (signed int)return_value_Get_Bits$8;
    }
    if(i >= 64)
    {
      if(Quiet_Flag == 0)
        fprintf(stderr, "DCT coeff index (i) out of bounds (intra)\n");

      Fault_Flag = 1;
      return;
    }

    j = (signed int)scan[(signed long int)0][(signed long int)i];
    val = val * ld->quantizer_scale * ld->intra_quantizer_matrix[(signed long int)j] >> 3;
    if(!(val == 0))
      val = val - 1 | 1;

    if(sign == 0)
      bp[(signed long int)j] = (signed short int)(val > 2047 ? 2047 : val);

    else
      bp[(signed long int)j] = (signed short int)(val > 2048 ? -2048 : -val);
    i = i + 1;
  }
  while(TRUE);
}

// c::Decode_MPEG1_Non_Intra_Block
// file src/getblk.c line 206
void Decode_MPEG1_Non_Intra_Block(signed int comp)
{
  signed int val;
  signed int i;
  signed int j;
  signed int sign;
  unsigned int code;
  struct anon$1 *tab;
  signed short int *bp = ld->block[(signed long int)comp];
  i = 0;
  unsigned int return_value_Get_Bits$3;
  unsigned int return_value_Get_Bits$4;
  do
  {
    code=Show_Bits(16);
    if(code >= 16384u)
    {
      if(i == 0)
        tab = &DCTtabfirst[(signed long int)((code >> 12) - (unsigned int)4)];

      else
        tab = &DCTtabnext[(signed long int)((code >> 12) - (unsigned int)4)];
    }

    else
      if(code >= 1024u)
        tab = &DCTtab0[(signed long int)((code >> 8) - (unsigned int)4)];

      else
        if(code >= 512u)
          tab = &DCTtab1[(signed long int)((code >> 6) - (unsigned int)8)];

        else
          if(code >= 256u)
            tab = &DCTtab2[(signed long int)((code >> 4) - (unsigned int)16)];

          else
            if(code >= 128u)
              tab = &DCTtab3[(signed long int)((code >> 3) - (unsigned int)16)];

            else
              if(code >= 64u)
                tab = &DCTtab4[(signed long int)((code >> 2) - (unsigned int)16)];

              else
                if(code >= 32u)
                  tab = &DCTtab5[(signed long int)((code >> 1) - (unsigned int)16)];

                else
                  if(code >= 16u)
                    tab = &DCTtab6[(signed long int)(code - (unsigned int)16)];

                  else
                  {
                    if(Quiet_Flag == 0)
                      printf("invalid Huffman code in Decode_MPEG1_Non_Intra_Block()\n");

                    Fault_Flag = 1;
                    return;
                  }
    Flush_Buffer((signed int)tab->len);
    if((signed int)tab->run == 64)
      return;

    if((signed int)tab->run == 65)
    {
      unsigned int return_value_Get_Bits$1;
      return_value_Get_Bits$1=Get_Bits(6);
      i = i + (signed int)return_value_Get_Bits$1;
      unsigned int return_value_Get_Bits$2;
      return_value_Get_Bits$2=Get_Bits(8);
      val = (signed int)return_value_Get_Bits$2;
      if(val == 0)
      {
        return_value_Get_Bits$3=Get_Bits(8);
        val = (signed int)return_value_Get_Bits$3;
      }

      else
        if(val == 128)
        {
          return_value_Get_Bits$4=Get_Bits(8);
          val = (signed int)(return_value_Get_Bits$4 - (unsigned int)256);
        }

        else
          if(val > 128)
            val = val - 256;

      sign = (signed int)(val < 0);
      if(!(sign == 0))
        val = -val;

    }

    else
    {
      i = i + (signed int)tab->run;
      val = (signed int)tab->level;
      unsigned int return_value_Get_Bits$5;
      return_value_Get_Bits$5=Get_Bits(1);
      sign = (signed int)return_value_Get_Bits$5;
    }
    if(i >= 64)
    {
      if(Quiet_Flag == 0)
        fprintf(stderr, "DCT coeff index (i) out of bounds (inter)\n");

      Fault_Flag = 1;
      return;
    }

    j = (signed int)scan[(signed long int)0][(signed long int)i];
    val = ((val << 1) + 1) * ld->quantizer_scale * ld->non_intra_quantizer_matrix[(signed long int)j] >> 4;
    if(!(val == 0))
      val = val - 1 | 1;

    if(sign == 0)
      bp[(signed long int)j] = (signed short int)(val > 2047 ? 2047 : val);

    else
      bp[(signed long int)j] = (signed short int)(val > 2048 ? -2048 : -val);
    i = i + 1;
  }
  while(TRUE);
}

// c::Decode_MPEG2_Intra_Block
// file src/getblk.c line 302
void Decode_MPEG2_Intra_Block(signed int comp, signed int *dc_dct_pred)
{
  signed int val;
  signed int i;
  signed int j;
  signed int sign;
  signed int nc;
  signed int cc;
  signed int run;
  unsigned int code;
  struct anon$1 *tab;
  signed short int *bp;
  signed int *qmat;
  struct layer_data *ld1 = ld->scalable_mode == 1 ? &base : ld;
  bp = ld1->block[(signed long int)comp];
  if(base.scalable_mode == 1)
  {
    if(base.priority_breakpoint < 64)
      ld = &enhan;

    else
      ld = &base;
  }

  cc = comp < 4 ? 0 : (comp & 1) + 1;
  signed int *tmp_if_expr$1;
  if(!(comp < 4))
  {
    if(chroma_format == 1)
      goto __CPROVER_DUMP_L3;

  }

  else
  {

  __CPROVER_DUMP_L3:
    ;
    tmp_if_expr$1 = ld1->intra_quantizer_matrix;
    goto __CPROVER_DUMP_L5;
  }
  tmp_if_expr$1 = ld1->chroma_intra_quantizer_matrix;

__CPROVER_DUMP_L5:
  ;
  qmat = tmp_if_expr$1;
  signed int return_value_Get_Luma_DC_dct_diff$2;
  signed int return_value_Get_Chroma_DC_dct_diff$3;
  signed int return_value_Get_Chroma_DC_dct_diff$4;
  if(cc == 0)
  {
    return_value_Get_Luma_DC_dct_diff$2=Get_Luma_DC_dct_diff();
    dc_dct_pred[(signed long int)0] = dc_dct_pred[(signed long int)0] + return_value_Get_Luma_DC_dct_diff$2;
    val = dc_dct_pred[(signed long int)0];
  }

  else
    if(cc == 1)
    {
      return_value_Get_Chroma_DC_dct_diff$3=Get_Chroma_DC_dct_diff();
      dc_dct_pred[(signed long int)1] = dc_dct_pred[(signed long int)1] + return_value_Get_Chroma_DC_dct_diff$3;
      val = dc_dct_pred[(signed long int)1];
    }

    else
    {
      return_value_Get_Chroma_DC_dct_diff$4=Get_Chroma_DC_dct_diff();
      dc_dct_pred[(signed long int)2] = dc_dct_pred[(signed long int)2] + return_value_Get_Chroma_DC_dct_diff$4;
      val = dc_dct_pred[(signed long int)2];
    }
  if(!(Fault_Flag == 0))
    return;

  bp[(signed long int)0] = (signed short int)(val << 3 - intra_dc_precision);
  nc = 0;
  i = 1;
  do
  {
    code=Show_Bits(16);
    if(code >= 16384u)
    {
      if(intra_vlc_format != 0)
        goto __CPROVER_DUMP_L11;

      tab = &DCTtabnext[(signed long int)((code >> 12) - (unsigned int)4)];
    }

    else
    {

    __CPROVER_DUMP_L11:
      ;
      if(code >= 1024u)
      {
        if(!(intra_vlc_format == 0))
          tab = &DCTtab0a[(signed long int)((code >> 8) - (unsigned int)4)];

        else
          tab = &DCTtab0[(signed long int)((code >> 8) - (unsigned int)4)];
      }

      else
        if(code >= 512u)
        {
          if(!(intra_vlc_format == 0))
            tab = &DCTtab1a[(signed long int)((code >> 6) - (unsigned int)8)];

          else
            tab = &DCTtab1[(signed long int)((code >> 6) - (unsigned int)8)];
        }

        else
          if(code >= 256u)
            tab = &DCTtab2[(signed long int)((code >> 4) - (unsigned int)16)];

          else
            if(code >= 128u)
              tab = &DCTtab3[(signed long int)((code >> 3) - (unsigned int)16)];

            else
              if(code >= 64u)
                tab = &DCTtab4[(signed long int)((code >> 2) - (unsigned int)16)];

              else
                if(code >= 32u)
                  tab = &DCTtab5[(signed long int)((code >> 1) - (unsigned int)16)];

                else
                  if(code >= 16u)
                    tab = &DCTtab6[(signed long int)(code - (unsigned int)16)];

                  else
                  {
                    if(Quiet_Flag == 0)
                      printf("invalid Huffman code in Decode_MPEG2_Intra_Block()\n");

                    Fault_Flag = 1;
                    return;
                  }
    }
    Flush_Buffer((signed int)tab->len);
    if((signed int)tab->run == 64)
      return;

    if((signed int)tab->run == 65)
    {
      unsigned int return_value_Get_Bits$5;
      return_value_Get_Bits$5=Get_Bits(6);
      run = (signed int)return_value_Get_Bits$5;
      i = i + run;
      unsigned int return_value_Get_Bits$6;
      return_value_Get_Bits$6=Get_Bits(12);
      val = (signed int)return_value_Get_Bits$6;
      if((2047 & val) == 0)
      {
        if(Quiet_Flag == 0)
          printf("invalid escape in Decode_MPEG2_Intra_Block()\n");

        Fault_Flag = 1;
        return;
      }

      sign = (signed int)(val >= 2048);
      if(!(sign == 0))
        val = 4096 - val;

    }

    else
    {
      run = (signed int)tab->run;
      i = i + run;
      val = (signed int)tab->level;
      unsigned int return_value_Get_Bits$7;
      return_value_Get_Bits$7=Get_Bits(1);
      sign = (signed int)return_value_Get_Bits$7;
    }
    if(i >= 64)
    {
      if(Quiet_Flag == 0)
        fprintf(stderr, "DCT coeff index (i) out of bounds (intra2)\n");

      Fault_Flag = 1;
      return;
    }

    j = (signed int)scan[(signed long int)ld1->alternate_scan][(signed long int)i];
    val = val * ld1->quantizer_scale * qmat[(signed long int)j] >> 4;
    bp[(signed long int)j] = (signed short int)(sign != 0 ? -val : val);
    nc = nc + 1;
    if(base.scalable_mode == 1)
    {
      if(nc == -63 + base.priority_breakpoint)
        ld = &enhan;

    }

    i = i + 1;
  }
  while(TRUE);
}

// c::Decode_MPEG2_Non_Intra_Block
// file src/getblk.c line 475
void Decode_MPEG2_Non_Intra_Block(signed int comp)
{
  signed int val;
  signed int i;
  signed int j;
  signed int sign;
  signed int nc;
  signed int run;
  unsigned int code;
  struct anon$1 *tab;
  signed short int *bp;
  signed int *qmat;
  struct layer_data *ld1 = ld->scalable_mode == 1 ? &base : ld;
  bp = ld1->block[(signed long int)comp];
  if(base.scalable_mode == 1)
  {
    if(base.priority_breakpoint < 64)
      ld = &enhan;

    else
      ld = &base;
  }

  signed int *tmp_if_expr$1;
  if(!(comp < 4))
  {
    if(chroma_format == 1)
      goto __CPROVER_DUMP_L3;

  }

  else
  {

  __CPROVER_DUMP_L3:
    ;
    tmp_if_expr$1 = ld1->non_intra_quantizer_matrix;
    goto __CPROVER_DUMP_L5;
  }
  tmp_if_expr$1 = ld1->chroma_non_intra_quantizer_matrix;

__CPROVER_DUMP_L5:
  ;
  qmat = tmp_if_expr$1;
  nc = 0;
  i = 0;
  do
  {
    code=Show_Bits(16);
    if(code >= 16384u)
    {
      if(i == 0)
        tab = &DCTtabfirst[(signed long int)((code >> 12) - (unsigned int)4)];

      else
        tab = &DCTtabnext[(signed long int)((code >> 12) - (unsigned int)4)];
    }

    else
      if(code >= 1024u)
        tab = &DCTtab0[(signed long int)((code >> 8) - (unsigned int)4)];

      else
        if(code >= 512u)
          tab = &DCTtab1[(signed long int)((code >> 6) - (unsigned int)8)];

        else
          if(code >= 256u)
            tab = &DCTtab2[(signed long int)((code >> 4) - (unsigned int)16)];

          else
            if(code >= 128u)
              tab = &DCTtab3[(signed long int)((code >> 3) - (unsigned int)16)];

            else
              if(code >= 64u)
                tab = &DCTtab4[(signed long int)((code >> 2) - (unsigned int)16)];

              else
                if(code >= 32u)
                  tab = &DCTtab5[(signed long int)((code >> 1) - (unsigned int)16)];

                else
                  if(code >= 16u)
                    tab = &DCTtab6[(signed long int)(code - (unsigned int)16)];

                  else
                  {
                    if(Quiet_Flag == 0)
                      printf("invalid Huffman code in Decode_MPEG2_Non_Intra_Block()\n");

                    Fault_Flag = 1;
                    return;
                  }
    Flush_Buffer((signed int)tab->len);
    if((signed int)tab->run == 64)
      return;

    if((signed int)tab->run == 65)
    {
      unsigned int return_value_Get_Bits$2;
      return_value_Get_Bits$2=Get_Bits(6);
      run = (signed int)return_value_Get_Bits$2;
      i = i + run;
      unsigned int return_value_Get_Bits$3;
      return_value_Get_Bits$3=Get_Bits(12);
      val = (signed int)return_value_Get_Bits$3;
      if((2047 & val) == 0)
      {
        if(Quiet_Flag == 0)
          printf("invalid escape in Decode_MPEG2_Intra_Block()\n");

        Fault_Flag = 1;
        return;
      }

      sign = (signed int)(val >= 2048);
      if(!(sign == 0))
        val = 4096 - val;

    }

    else
    {
      run = (signed int)tab->run;
      i = i + run;
      val = (signed int)tab->level;
      unsigned int return_value_Get_Bits$4;
      return_value_Get_Bits$4=Get_Bits(1);
      sign = (signed int)return_value_Get_Bits$4;
    }
    if(i >= 64)
    {
      if(Quiet_Flag == 0)
        fprintf(stderr, "DCT coeff index (i) out of bounds (inter2)\n");

      Fault_Flag = 1;
      return;
    }

    j = (signed int)scan[(signed long int)ld1->alternate_scan][(signed long int)i];
    val = ((val << 1) + 1) * ld1->quantizer_scale * qmat[(signed long int)j] >> 5;
    bp[(signed long int)j] = (signed short int)(sign != 0 ? -val : val);
    nc = nc + 1;
    if(base.scalable_mode == 1)
    {
      if(nc == -63 + base.priority_breakpoint)
        ld = &enhan;

    }

    i = i + 1;
  }
  while(TRUE);
}

// c::Decode_Picture
// file src/getpic.c line 155
void Decode_Picture(signed int bitstream_framenum, signed int sequence_framenum)
{
  if(picture_structure == 3)
  {
    if(!(Second_Field == 0))
    {
      printf("odd number of field pictures\n");
      Second_Field = 0;
    }

  }

  Update_Picture_Buffers();
  if(!(Ersatz_Flag == 0))
    Substitute_Frame_Buffer(bitstream_framenum, sequence_framenum);

  if(!(base.pict_scal == 0))
  {
    if(Second_Field == 0)
      Spatial_Prediction();

  }

  picture_data(bitstream_framenum);
  frame_reorder(bitstream_framenum, sequence_framenum);
  if(!(picture_structure == 3))
    Second_Field = (signed int)!(Second_Field != 0);

}

// c::Decode_SNR_Macroblock
// file src/getpic.c line 616
static void Decode_SNR_Macroblock(signed int *SNRMBA, signed int *SNRMBAinc, signed int MBA, signed int MBAmax, signed int *dct_type)
{
  signed int SNRmacroblock_type;
  signed int SNRcoded_block_pattern;
  signed int SNRdct_type;
  signed int dummy;
  signed int slice_vert_pos_ext;
  signed int quantizer_scale_code;
  signed int comp;
  signed int code;
  ld = &enhan;
  if(*SNRMBAinc == 0)
  {
    unsigned int return_value_Show_Bits$2;
    return_value_Show_Bits$2=Show_Bits(23);
    if(return_value_Show_Bits$2 == 0u)
    {
      next_start_code();
      unsigned int return_value_Show_Bits$1;
      return_value_Show_Bits$1=Show_Bits(32);
      code = (signed int)return_value_Show_Bits$1;
      if(!(code < 257))
      {
        if(code > 431)
          goto __CPROVER_DUMP_L1;

      }

      else
      {

      __CPROVER_DUMP_L1:
        ;
        if(Quiet_Flag == 0)
          printf("SNR: Premature end of picture\n");

        return;
      }
      Flush_Buffer32();
      slice_vert_pos_ext=slice_header();
      *SNRMBAinc=Get_macroblock_address_increment();
      *SNRMBA = ((((slice_vert_pos_ext << 7) + (code & 255)) - 1) * mb_width + *SNRMBAinc) - 1;
      *SNRMBAinc = 1;
    }

    else
    {
      if(*SNRMBA >= MBAmax)
      {
        if(Quiet_Flag == 0)
          printf("Too many macroblocks in picture\n");

        return;
      }

      *SNRMBAinc=Get_macroblock_address_increment();
    }
  }

  if(!(*SNRMBA == MBA))
  {
    if(Quiet_Flag == 0)
      printf("Cant't synchronize streams\n");

    return;
  }

  signed int tmp_if_expr$4;
  unsigned int return_value_Get_Bits$5;
  unsigned int return_value_Get_Bits$6;
  if(*SNRMBAinc == 1)
  {
    macroblock_modes(&SNRmacroblock_type, &dummy, &dummy, &dummy, &dummy, &dummy, &dummy, &dummy, &SNRdct_type);
    if(!((2 & SNRmacroblock_type) == 0))
      *dct_type = SNRdct_type;

    if(!((16 & SNRmacroblock_type) == 0))
    {
      unsigned int return_value_Get_Bits$3;
      return_value_Get_Bits$3=Get_Bits(5);
      quantizer_scale_code = (signed int)return_value_Get_Bits$3;
      if(!(ld->q_scale_type == 0))
        tmp_if_expr$4 = (signed int)Non_Linear_quantizer_scale[(signed long int)quantizer_scale_code];

      else
        tmp_if_expr$4 = quantizer_scale_code << 1;
      ld->quantizer_scale = tmp_if_expr$4;
    }

    if(!((2 & SNRmacroblock_type) == 0))
    {
      SNRcoded_block_pattern=Get_coded_block_pattern();
      if(chroma_format == 2)
      {
        return_value_Get_Bits$5=Get_Bits(2);
        SNRcoded_block_pattern = (signed int)((unsigned int)(SNRcoded_block_pattern << 2) | return_value_Get_Bits$5);
      }

      else
        if(chroma_format == 3)
        {
          return_value_Get_Bits$6=Get_Bits(6);
          SNRcoded_block_pattern = (signed int)((unsigned int)(SNRcoded_block_pattern << 6) | return_value_Get_Bits$6);
        }

    }

    else
      SNRcoded_block_pattern = 0;
    comp = 0;
    while(!(comp >= block_count))
    {
      Clear_Block(comp);
      if(!((1 << -1 + block_count + -comp & SNRcoded_block_pattern) == 0))
        Decode_MPEG2_Non_Intra_Block(comp);

      comp = comp + 1;
    }
  }

  else
  {
    comp = 0;
    while(!(comp >= block_count))
    {
      Clear_Block(comp);
      comp = comp + 1;
    }
  }
  ld = &base;
}

// c::Deinitialize_Sequence
// file src/mpeg2dec.c line 706
static void Deinitialize_Sequence(void)
{
  signed int i;
  base.MPEG2_Flag = 0;
  i = 0;
  while(i < 3)
  {
    free((void *)backward_reference_frame[(signed long int)i]);
    free((void *)forward_reference_frame[(signed long int)i]);
    free((void *)auxframe[(signed long int)i]);
    if(base.scalable_mode == 2)
    {
      free((void *)llframe0[(signed long int)i]);
      free((void *)llframe1[(signed long int)i]);
    }

    i = i + 1;
  }
  if(base.scalable_mode == 2)
    free((void *)lltmp);

}

// c::Deinterlace
// file src/spatscal.c line 298
static void Deinterlace(unsigned char *fld0, unsigned char *fld1, signed int j0, signed int lx, signed int ly, signed int aperture)
{
  signed int i;
  signed int j;
  signed int v;
  unsigned char *p0;
  unsigned char *p0m1;
  unsigned char *p0p1;
  unsigned char *p1;
  unsigned char *p1m2;
  unsigned char *p1p2;
  j = j0;
  while(!(j >= ly))
  {
    p0 = fld0 + (signed long int)(lx * j);
    p0m1 = j == 0 ? p0 + (signed long int)lx : p0 - (signed long int)lx;
    p0p1 = j == ly - 1 ? p0 - (signed long int)lx : p0 + (signed long int)lx;
    if(!(aperture == 0))
    {
      i = 0;
      while(!(i >= lx))
      {
        p0[(signed long int)i] = (unsigned char)((unsigned int)((signed int)p0m1[(signed long int)i] + (signed int)p0p1[(signed long int)i] + 1) >> 1);
        i = i + 1;
      }
    }

    else
    {
      p1 = fld1 + (signed long int)(lx * j);
      p1m2 = j < 2 ? p1 : p1 - (signed long int)(2 * lx);
      p1p2 = j >= ly - 2 ? p1 : p1 + (signed long int)(2 * lx);
      i = 0;
      while(!(i >= lx))
      {
        v = ((8 * ((signed int)p0m1[(signed long int)i] + (signed int)p0p1[(signed long int)i]) + 2 * (signed int)p1[(signed long int)i]) - (signed int)p1m2[(signed long int)i]) - (signed int)p1p2[(signed long int)i];
        p0[(signed long int)i] = Clip[(signed long int)(v + (v >= 0 ? 8 : 7) >> 4)];
        i = i + 1;
      }
    }
    j = j + 2;
  }
}

// c::Dual_Prime_Arithmetic
// file src/motion.c line 246
void Dual_Prime_Arithmetic(signed int (*DMV)[2l], signed int *dmvector, signed int mvx, signed int mvy)
{
  if(picture_structure == 3)
  {
    if(!(top_field_first == 0))
    {
      DMV[(signed long int)0][(signed long int)0] = (mvx + (signed int)(mvx > 0) >> 1) + dmvector[(signed long int)0];
      DMV[(signed long int)0][(signed long int)1] = ((mvy + (signed int)(mvy > 0) >> 1) + dmvector[(signed long int)1]) - 1;
      DMV[(signed long int)1][(signed long int)0] = (3 * mvx + (signed int)(mvx > 0) >> 1) + dmvector[(signed long int)0];
      DMV[(signed long int)1][(signed long int)1] = (3 * mvy + (signed int)(mvy > 0) >> 1) + dmvector[(signed long int)1] + 1;
    }

    else
    {
      DMV[(signed long int)0][(signed long int)0] = (3 * mvx + (signed int)(mvx > 0) >> 1) + dmvector[(signed long int)0];
      DMV[(signed long int)0][(signed long int)1] = ((3 * mvy + (signed int)(mvy > 0) >> 1) + dmvector[(signed long int)1]) - 1;
      DMV[(signed long int)1][(signed long int)0] = (mvx + (signed int)(mvx > 0) >> 1) + dmvector[(signed long int)0];
      DMV[(signed long int)1][(signed long int)1] = (mvy + (signed int)(mvy > 0) >> 1) + dmvector[(signed long int)1] + 1;
    }
  }

  else
  {
    DMV[(signed long int)0][(signed long int)0] = (mvx + (signed int)(mvx > 0) >> 1) + dmvector[(signed long int)0];
    DMV[(signed long int)0][(signed long int)1] = (mvy + (signed int)(mvy > 0) >> 1) + dmvector[(signed long int)1];
    if(picture_structure == 1)
      DMV[(signed long int)0][(signed long int)1] = DMV[(signed long int)0][(signed long int)1] - 1;

    else
      DMV[(signed long int)0][(signed long int)1] = DMV[(signed long int)0][(signed long int)1] + 1;
  }
}

// c::Error
// file src/global.h line 181
void Error(char *text)
{
  fprintf(stderr, text);
  exit(1);
}

// c::Extract_Components
// file src/subspic.c line 334
static signed int Extract_Components(char *filename, unsigned char **frame, signed int framenum)
{
  struct _IO_FILE$link12 *fd;
  signed int line;
  signed int size;
  signed int offset;
  fd=fopen(filename, "rb");
  if(fd == ((struct _IO_FILE$link12 *)NULL))
  {
    sprintf(Error_Text, "Couldn't open %s\n", filename);
    return -1;
  }

  size = Coded_Picture_Width * Coded_Picture_Height;
  if(chroma_format == 3)
    size = size * 3;

  else
    if(chroma_format == 2)
      size = size * 2;

    else
      if(chroma_format == 1)
        size = size * 3 >> 1;

      else
        printf("ERROR: chroma_format (%d) not recognized\n", chroma_format);
  offset = size * framenum;
  fseek(fd, (signed long int)offset, 0);
  line = 0;
  while(!(line >= Coded_Picture_Height))
  {
    fread((void *)(frame[(signed long int)0] + (signed long int)(line * Coded_Picture_Width)), (unsigned long int)1, (unsigned long int)Coded_Picture_Width, fd);
    line = line + 1;
  }
  line = 0;
  while(!(line >= Chroma_Height))
  {
    fread((void *)(frame[(signed long int)1] + (signed long int)(line * Chroma_Width)), (unsigned long int)1, (unsigned long int)Chroma_Width, fd);
    line = line + 1;
  }
  line = 0;
  while(!(line >= Chroma_Height))
  {
    fread((void *)(frame[(signed long int)2] + (signed long int)(line * Chroma_Width)), (unsigned long int)1, (unsigned long int)Chroma_Width, fd);
    line = line + 1;
  }
  fclose(fd);
  return 0;
}

// c::Fast_IDCT
// file src/global.h line 158
void Fast_IDCT(signed short int *block)
{
  idct_M128ASM_scalar(block);
}

// c::Fill_Buffer
// file src/getbits.c line 115
void Fill_Buffer(void)
{
  signed int Buffer_Level;
  signed long int return_value_read$1;
  return_value_read$1=read(ld->Infile, (void *)ld->Rdbfr, (unsigned long int)2048);
  Buffer_Level = (signed int)return_value_read$1;
  ld->Rdptr = ld->Rdbfr;
  if(!(System_Stream_Flag == 0))
    ld->Rdmax = ld->Rdmax - (signed long int)2048;

  signed int tmp_post$2;
  signed int tmp_post$3;
  signed int tmp_post$4;
  signed int tmp_post$5;
  signed int tmp_post$6;
  if(Buffer_Level < 2048)
  {
    if(Buffer_Level < 0)
      Buffer_Level = 0;

    while(!((3 & Buffer_Level) == 0))
    {
      tmp_post$2 = Buffer_Level;
      Buffer_Level = Buffer_Level + 1;
      ld->Rdbfr[(signed long int)tmp_post$2] = (unsigned char)0;
    }
    while(Buffer_Level < 2048)
    {
      tmp_post$3 = Buffer_Level;
      Buffer_Level = Buffer_Level + 1;
      ld->Rdbfr[(signed long int)tmp_post$3] = (unsigned char)(439 >> 24);
      tmp_post$4 = Buffer_Level;
      Buffer_Level = Buffer_Level + 1;
      ld->Rdbfr[(signed long int)tmp_post$4] = (unsigned char)(439 >> 16);
      tmp_post$5 = Buffer_Level;
      Buffer_Level = Buffer_Level + 1;
      ld->Rdbfr[(signed long int)tmp_post$5] = (unsigned char)(439 >> 8);
      tmp_post$6 = Buffer_Level;
      Buffer_Level = Buffer_Level + 1;
      ld->Rdbfr[(signed long int)tmp_post$6] = (unsigned char)(439 & 255);
    }
  }

}

// c::Flush_Buffer
// file src/getbits.c line 191
void Flush_Buffer(signed int N)
{
  signed int Incnt;
  ld->Bfr = ld->Bfr << N;
  ld->Incnt = ld->Incnt - N;
  Incnt = ld->Incnt;
  _Bool tmp_if_expr$4;
  unsigned char *tmp_post$2;
  unsigned char *tmp_post$3;
  if(Incnt <= 24)
  {
    if(!(System_Stream_Flag == 0))
      tmp_if_expr$4 = ld->Rdptr >= ld->Rdmax - (signed long int)4 ? TRUE : FALSE;

    else
      tmp_if_expr$4 = FALSE;
    if(tmp_if_expr$4)
      while(TRUE)
      {
        if(!(ld->Rdptr >= ld->Rdmax))
          goto __CPROVER_DUMP_L4;

        Next_Packet();

      __CPROVER_DUMP_L4:
        ;
        signed int return_value_Get_Byte$1;
        return_value_Get_Byte$1=Get_Byte();
        ld->Bfr = ld->Bfr | (unsigned int)(return_value_Get_Byte$1 << 24 - Incnt);
        Incnt = Incnt + 8;
        if(!(Incnt <= 24))
          break;

      }

    else
      if(!(ld->Rdptr >= ld->Rdbfr + 2044l))
        do
        {
          tmp_post$2 = ld->Rdptr;
          ld->Rdptr = ld->Rdptr + 1l;
          ld->Bfr = ld->Bfr | (unsigned int)((signed int)*tmp_post$2 << 24 - Incnt);
          Incnt = Incnt + 8;
        }
        while(Incnt <= 24);

      else
        while(TRUE)
        {
          if(!(ld->Rdptr >= ld->Rdbfr + 2048l))
            goto __CPROVER_DUMP_L8;

          Fill_Buffer();

        __CPROVER_DUMP_L8:
          ;
          tmp_post$3 = ld->Rdptr;
          ld->Rdptr = ld->Rdptr + 1l;
          ld->Bfr = ld->Bfr | (unsigned int)((signed int)*tmp_post$3 << 24 - Incnt);
          Incnt = Incnt + 8;
          if(!(Incnt <= 24))
            break;

        }
    ld->Incnt = Incnt;
  }

}

// c::Flush_Buffer32
// file src/global.h line 121
void Flush_Buffer32(void)
{
  signed int Incnt;
  ld->Bfr = (unsigned int)0;
  Incnt = ld->Incnt;
  Incnt = Incnt - 32;
  _Bool tmp_if_expr$3;
  if(!(System_Stream_Flag == 0))
    tmp_if_expr$3 = ld->Rdptr >= ld->Rdmax - (signed long int)4 ? TRUE : FALSE;

  else
    tmp_if_expr$3 = FALSE;
  unsigned char *tmp_post$2;
  if(tmp_if_expr$3)
    while(Incnt <= 24)
    {
      if(ld->Rdptr >= ld->Rdmax)
        Next_Packet();

      signed int return_value_Get_Byte$1;
      return_value_Get_Byte$1=Get_Byte();
      ld->Bfr = ld->Bfr | (unsigned int)(return_value_Get_Byte$1 << 24 - Incnt);
      Incnt = Incnt + 8;
    }

  else
    while(Incnt <= 24)
    {
      if(ld->Rdptr >= ld->Rdbfr + 2048l)
        Fill_Buffer();

      tmp_post$2 = ld->Rdptr;
      ld->Rdptr = ld->Rdptr + 1l;
      ld->Bfr = ld->Bfr | (unsigned int)((signed int)*tmp_post$2 << 24 - Incnt);
      Incnt = Incnt + 8;
    }
  ld->Incnt = Incnt;
}

// c::Get_B_Spatial_macroblock_type
// file src/getvlc.c line 364
static signed int Get_B_Spatial_macroblock_type(void)
{
  signed int code;
  struct anon$3 *p;
  unsigned int return_value_Show_Bits$1;
  return_value_Show_Bits$1=Show_Bits(9);
  code = (signed int)return_value_Show_Bits$1;
  if(code >= 64)
    p = &spBMBtab0[(signed long int)((code >> 5) - 2)];

  else
    if(code >= 16)
      p = &spBMBtab1[(signed long int)((code >> 2) - 4)];

    else
      if(code >= 8)
        p = &spBMBtab2[(signed long int)(code - 8)];

      else
      {
        if(Quiet_Flag == 0)
          printf("Invalid macroblock_type code\n");

        Fault_Flag = 1;
        return 0;
      }
  Flush_Buffer((signed int)p->len);
  return (signed int)p->val;
}

// c::Get_B_macroblock_type
// file src/getvlc.c line 226
static signed int Get_B_macroblock_type(void)
{
  signed int code;
  unsigned int return_value_Show_Bits$1;
  return_value_Show_Bits$1=Show_Bits(6);
  code = (signed int)return_value_Show_Bits$1;
  if(code >= 8)
  {
    code = code >> 2;
    Flush_Buffer((signed int)BMBtab0[(signed long int)code].len);
    return (signed int)BMBtab0[(signed long int)code].val;
  }

  if(code == 0)
  {
    if(Quiet_Flag == 0)
      printf("Invalid macroblock_type code\n");

    Fault_Flag = 1;
    return 0;
  }

  Flush_Buffer((signed int)BMBtab1[(signed long int)code].len);
  return (signed int)BMBtab1[(signed long int)code].val;
}

// c::Get_Bits
// file src/getbits.c line 245
unsigned int Get_Bits(signed int N)
{
  unsigned int Val;
  Val=Show_Bits(N);
  Flush_Buffer(N);
  return Val;
}

// c::Get_Bits1
// file src/getbits.c line 183
unsigned int Get_Bits1(void)
{
  unsigned int return_value_Get_Bits$1;
  return_value_Get_Bits$1=Get_Bits(1);
  return return_value_Get_Bits$1;
}

// c::Get_Bits32
// file src/global.h line 122
unsigned int Get_Bits32(void)
{
  unsigned int l;
  l=Show_Bits(32);
  Flush_Buffer32();
  return l;
}

// c::Get_Byte
// file src/getbits.c line 151
signed int Get_Byte(void)
{
  while(ld->Rdptr >= ld->Rdbfr + 2048l)
  {
    read(ld->Infile, (void *)ld->Rdbfr, (unsigned long int)2048);
    ld->Rdptr = ld->Rdptr - (signed long int)2048;
    ld->Rdmax = ld->Rdmax - (signed long int)2048;
  }
  unsigned char *tmp_post$1 = ld->Rdptr;
  ld->Rdptr = ld->Rdptr + 1l;
  return (signed int)*tmp_post$1;
}

// c::Get_Chroma_DC_dct_diff
// file src/global.h line 155
signed int Get_Chroma_DC_dct_diff(void)
{
  signed int code;
  signed int size;
  signed int dct_diff;
  unsigned int return_value_Show_Bits$1;
  return_value_Show_Bits$1=Show_Bits(5);
  code = (signed int)return_value_Show_Bits$1;
  if(code < 31)
  {
    size = (signed int)DCchromtab0[(signed long int)code].val;
    Flush_Buffer((signed int)DCchromtab0[(signed long int)code].len);
  }

  else
  {
    unsigned int return_value_Show_Bits$2;
    return_value_Show_Bits$2=Show_Bits(10);
    code = (signed int)(return_value_Show_Bits$2 - (unsigned int)992);
    size = (signed int)DCchromtab1[(signed long int)code].val;
    Flush_Buffer((signed int)DCchromtab1[(signed long int)code].len);
  }
  if(size == 0)
    dct_diff = 0;

  else
  {
    unsigned int return_value_Get_Bits$3;
    return_value_Get_Bits$3=Get_Bits(size);
    dct_diff = (signed int)return_value_Get_Bits$3;
    if((1 << -1 + size & dct_diff) == 0)
      dct_diff = dct_diff - ((1 << size) - 1);

  }
  return dct_diff;
}

// c::Get_D_macroblock_type
// file src/getvlc.c line 272
static signed int Get_D_macroblock_type(void)
{
  unsigned int return_value_Get_Bits1$1;
  return_value_Get_Bits1$1=Get_Bits1();
  if(return_value_Get_Bits1$1 == 0u)
  {
    if(Quiet_Flag == 0)
      printf("Invalid macroblock_type code\n");

    Fault_Flag = 1;
  }

  return 1;
}

// c::Get_Hdr
// file src/gethdr.c line 145
signed int Get_Hdr(void)
{
  unsigned int code;
  do
  {
    next_start_code();
    code=Get_Bits32();
    switch(code)
    {

      case (unsigned int)435:
        {
          sequence_header();
          goto __CPROVER_DUMP_L7;
        }
      case (unsigned int)440:
        {
          group_of_pictures_header();
          goto __CPROVER_DUMP_L7;
        }
      case (unsigned int)256:
        {
          picture_header();
          return 1;
        }
      case (unsigned int)439:
        return 0;
      default:
        if(Quiet_Flag == 0)
          fprintf(stderr, "Unexpected next_start_code %08x (ignored)\n", code);

    }

  __CPROVER_DUMP_L7:
    ;
  }
  while(TRUE);
}

// c::Get_I_Spatial_macroblock_type
// file src/getvlc.c line 285
static signed int Get_I_Spatial_macroblock_type(void)
{
  signed int code;
  unsigned int return_value_Show_Bits$1;
  return_value_Show_Bits$1=Show_Bits(4);
  code = (signed int)return_value_Show_Bits$1;
  if(code == 0)
  {
    if(Quiet_Flag == 0)
      printf("Invalid macroblock_type code\n");

    Fault_Flag = 1;
    return 0;
  }

  Flush_Buffer((signed int)spIMBtab[(signed long int)code].len);
  return (signed int)spIMBtab[(signed long int)code].val;
}

// c::Get_I_macroblock_type
// file src/getvlc.c line 138
static signed int Get_I_macroblock_type(void)
{
  unsigned int return_value_Get_Bits1$1;
  return_value_Get_Bits1$1=Get_Bits1();
  if(!(return_value_Get_Bits1$1 == 0u))
    return 1;

  unsigned int return_value_Get_Bits1$2;
  return_value_Get_Bits1$2=Get_Bits1();
  if(return_value_Get_Bits1$2 == 0u)
  {
    if(Quiet_Flag == 0)
      printf("Invalid macroblock_type code\n");

    Fault_Flag = 1;
  }

  return 17;
}

// c::Get_Long
// file src/systems.c line 243
signed int Get_Long(void)
{
  signed int i;
  i=Get_Word();
  signed int return_value_Get_Word$1;
  return_value_Get_Word$1=Get_Word();
  return i << 16 | return_value_Get_Word$1;
}

// c::Get_Luma_DC_dct_diff
// file src/global.h line 154
signed int Get_Luma_DC_dct_diff(void)
{
  signed int code;
  signed int size;
  signed int dct_diff;
  unsigned int return_value_Show_Bits$1;
  return_value_Show_Bits$1=Show_Bits(5);
  code = (signed int)return_value_Show_Bits$1;
  if(code < 31)
  {
    size = (signed int)DClumtab0[(signed long int)code].val;
    Flush_Buffer((signed int)DClumtab0[(signed long int)code].len);
  }

  else
  {
    unsigned int return_value_Show_Bits$2;
    return_value_Show_Bits$2=Show_Bits(9);
    code = (signed int)(return_value_Show_Bits$2 - (unsigned int)496);
    size = (signed int)DClumtab1[(signed long int)code].val;
    Flush_Buffer((signed int)DClumtab1[(signed long int)code].len);
  }
  if(size == 0)
    dct_diff = 0;

  else
  {
    unsigned int return_value_Get_Bits$3;
    return_value_Get_Bits$3=Get_Bits(size);
    dct_diff = (signed int)return_value_Get_Bits$3;
    if((1 << -1 + size & dct_diff) == 0)
      dct_diff = dct_diff - ((1 << size) - 1);

  }
  return dct_diff;
}

// c::Get_P_Spatial_macroblock_type
// file src/getvlc.c line 316
static signed int Get_P_Spatial_macroblock_type(void)
{
  signed int code;
  unsigned int return_value_Show_Bits$1;
  return_value_Show_Bits$1=Show_Bits(7);
  code = (signed int)return_value_Show_Bits$1;
  if(code < 2)
  {
    if(Quiet_Flag == 0)
      printf("Invalid macroblock_type code\n");

    Fault_Flag = 1;
    return 0;
  }

  if(code >= 16)
  {
    code = code >> 3;
    Flush_Buffer((signed int)spPMBtab0[(signed long int)code].len);
    return (signed int)spPMBtab0[(signed long int)code].val;
  }

  Flush_Buffer((signed int)spPMBtab1[(signed long int)code].len);
  return (signed int)spPMBtab1[(signed long int)code].val;
}

// c::Get_P_macroblock_type
// file src/getvlc.c line 182
static signed int Get_P_macroblock_type(void)
{
  signed int code;
  unsigned int return_value_Show_Bits$1;
  return_value_Show_Bits$1=Show_Bits(6);
  code = (signed int)return_value_Show_Bits$1;
  if(code >= 8)
  {
    code = code >> 3;
    Flush_Buffer((signed int)PMBtab0[(signed long int)code].len);
    return (signed int)PMBtab0[(signed long int)code].val;
  }

  if(code == 0)
  {
    if(Quiet_Flag == 0)
      printf("Invalid macroblock_type code\n");

    Fault_Flag = 1;
    return 0;
  }

  Flush_Buffer((signed int)PMBtab1[(signed long int)code].len);
  return (signed int)PMBtab1[(signed long int)code].val;
}

// c::Get_SNR_macroblock_type
// file src/getvlc.c line 403
static signed int Get_SNR_macroblock_type(void)
{
  signed int code;
  unsigned int return_value_Show_Bits$1;
  return_value_Show_Bits$1=Show_Bits(3);
  code = (signed int)return_value_Show_Bits$1;
  if(code == 0)
  {
    if(Quiet_Flag == 0)
      printf("Invalid macroblock_type code\n");

    Fault_Flag = 1;
    return 0;
  }

  Flush_Buffer((signed int)SNRMBtab[(signed long int)code].len);
  return (signed int)SNRMBtab[(signed long int)code].val;
}

// c::Get_Word
// file src/getbits.c line 163
signed int Get_Word(void)
{
  signed int Val;
  Val=Get_Byte();
  signed int return_value_Get_Byte$1;
  return_value_Get_Byte$1=Get_Byte();
  return Val << 8 | return_value_Get_Byte$1;
}

// c::Get_coded_block_pattern
// file src/global.h line 152
signed int Get_coded_block_pattern(void)
{
  signed int code;
  unsigned int return_value_Show_Bits$1;
  return_value_Show_Bits$1=Show_Bits(9);
  code = (signed int)return_value_Show_Bits$1;
  if(code >= 128)
  {
    code = code >> 4;
    Flush_Buffer((signed int)CBPtab0[(signed long int)code].len);
    return (signed int)CBPtab0[(signed long int)code].val;
  }

  if(code >= 8)
  {
    code = code >> 1;
    Flush_Buffer((signed int)CBPtab1[(signed long int)code].len);
    return (signed int)CBPtab1[(signed long int)code].val;
  }

  if(code < 1)
  {
    if(Quiet_Flag == 0)
      printf("Invalid coded_block_pattern code\n");

    Fault_Flag = 1;
    return 0;
  }

  Flush_Buffer((signed int)CBPtab2[(signed long int)code].len);
  return (signed int)CBPtab2[(signed long int)code].val;
}

// c::Get_dmvector
// file src/getvlc.c line 512
signed int Get_dmvector(void)
{
  unsigned int return_value_Get_Bits$2;
  return_value_Get_Bits$2=Get_Bits(1);
  if(!(return_value_Get_Bits$2 == 0u))
  {
    unsigned int return_value_Get_Bits$1;
    return_value_Get_Bits$1=Get_Bits(1);
    return return_value_Get_Bits$1 != 0u ? -1 : 1;
  }

  else
    return 0;
}

// c::Get_macroblock_address_increment
// file src/global.h line 153
signed int Get_macroblock_address_increment(void)
{
  signed int code;
  signed int val = 0;
  unsigned int return_value_Show_Bits$1;
  do
  {
    return_value_Show_Bits$1=Show_Bits(11);
    code = (signed int)return_value_Show_Bits$1;
    if(!(code < 24))
      goto __CPROVER_DUMP_L6;

    if(!(code == 15))
    {
      if(code == 8)
        val = val + 33;

      else
      {
        if(Quiet_Flag == 0)
          printf("Invalid macroblock_address_increment code\n");

        Fault_Flag = 1;
        return 1;
      }
    }

    Flush_Buffer(11);
  }
  while(TRUE);

__CPROVER_DUMP_L6:
  ;
  if(code >= 1024)
  {
    Flush_Buffer(1);
    return val + 1;
  }

  if(code >= 128)
  {
    code = code >> 6;
    Flush_Buffer((signed int)MBAtab1[(signed long int)code].len);
    return val + (signed int)MBAtab1[(signed long int)code].val;
  }

  code = code - 24;
  Flush_Buffer((signed int)MBAtab2[(signed long int)code].len);
  return val + (signed int)MBAtab2[(signed long int)code].val;
}

// c::Get_macroblock_type
// file src/global.h line 149
signed int Get_macroblock_type(void)
{
  signed int macroblock_type = 0;
  signed int tmp_if_expr$3;
  signed int return_value_Get_I_Spatial_macroblock_type$1;
  signed int return_value_Get_I_macroblock_type$2;
  signed int tmp_if_expr$6;
  signed int return_value_Get_P_Spatial_macroblock_type$4;
  signed int return_value_Get_P_macroblock_type$5;
  signed int tmp_if_expr$9;
  signed int return_value_Get_B_Spatial_macroblock_type$7;
  signed int return_value_Get_B_macroblock_type$8;
  if(ld->scalable_mode == 3)
    macroblock_type=Get_SNR_macroblock_type();

  else
    switch(picture_coding_type)
    {

      case 1:
        {
          if(!(ld->pict_scal == 0))
          {
            return_value_Get_I_Spatial_macroblock_type$1=Get_I_Spatial_macroblock_type();
            tmp_if_expr$3 = return_value_Get_I_Spatial_macroblock_type$1;
          }

          else
          {
            return_value_Get_I_macroblock_type$2=Get_I_macroblock_type();
            tmp_if_expr$3 = return_value_Get_I_macroblock_type$2;
          }
          macroblock_type = tmp_if_expr$3;
          goto __CPROVER_DUMP_L13;
        }
      case 2:
        {
          if(!(ld->pict_scal == 0))
          {
            return_value_Get_P_Spatial_macroblock_type$4=Get_P_Spatial_macroblock_type();
            tmp_if_expr$6 = return_value_Get_P_Spatial_macroblock_type$4;
          }

          else
          {
            return_value_Get_P_macroblock_type$5=Get_P_macroblock_type();
            tmp_if_expr$6 = return_value_Get_P_macroblock_type$5;
          }
          macroblock_type = tmp_if_expr$6;
          goto __CPROVER_DUMP_L13;
        }
      case 3:
        {
          if(!(ld->pict_scal == 0))
          {
            return_value_Get_B_Spatial_macroblock_type$7=Get_B_Spatial_macroblock_type();
            tmp_if_expr$9 = return_value_Get_B_Spatial_macroblock_type$7;
          }

          else
          {
            return_value_Get_B_macroblock_type$8=Get_B_macroblock_type();
            tmp_if_expr$9 = return_value_Get_B_macroblock_type$8;
          }
          macroblock_type = tmp_if_expr$9;
          goto __CPROVER_DUMP_L13;
        }
      case 4:
        {
          macroblock_type=Get_D_macroblock_type();
          goto __CPROVER_DUMP_L13;
        }
      default:
        {
          printf("Get_macroblock_type(): unrecognized picture coding type\n");
          goto __CPROVER_DUMP_L13;
        }
    }

__CPROVER_DUMP_L13:
  ;
  return macroblock_type;
}

// c::Get_motion_code
// file src/getvlc.c line 436
signed int Get_motion_code(void)
{
  signed int code;
  unsigned int return_value_Get_Bits1$1;
  return_value_Get_Bits1$1=Get_Bits1();
  if(!(return_value_Get_Bits1$1 == 0u))
    return 0;

  unsigned int return_value_Show_Bits$4;
  return_value_Show_Bits$4=Show_Bits(9);
  code = (signed int)return_value_Show_Bits$4;
  signed int tmp_if_expr$3;
  if(code >= 64)
  {
    code = code >> 6;
    Flush_Buffer((signed int)MVtab0[(signed long int)code].len);
    unsigned int return_value_Get_Bits1$2;
    return_value_Get_Bits1$2=Get_Bits1();
    if(!(return_value_Get_Bits1$2 == 0u))
      tmp_if_expr$3 = -((signed int)MVtab0[(signed long int)code].val);

    else
      tmp_if_expr$3 = (signed int)MVtab0[(signed long int)code].val;
    return tmp_if_expr$3;
  }

  signed int tmp_if_expr$6;
  if(code >= 24)
  {
    code = code >> 3;
    Flush_Buffer((signed int)MVtab1[(signed long int)code].len);
    unsigned int return_value_Get_Bits1$5;
    return_value_Get_Bits1$5=Get_Bits1();
    if(!(return_value_Get_Bits1$5 == 0u))
      tmp_if_expr$6 = -((signed int)MVtab1[(signed long int)code].val);

    else
      tmp_if_expr$6 = (signed int)MVtab1[(signed long int)code].val;
    return tmp_if_expr$6;
  }

  code = code - 12;
  if(code < 0)
  {
    if(Quiet_Flag == 0)
      printf("Invalid motion_vector code (MBA %d, pic %d)\n", global_MBA, global_pic);

    Fault_Flag = 1;
    return 0;
  }

  Flush_Buffer((signed int)MVtab2[(signed long int)code].len);
  unsigned int return_value_Get_Bits1$7;
  return_value_Get_Bits1$7=Get_Bits1();
  signed int tmp_if_expr$8;
  if(!(return_value_Get_Bits1$7 == 0u))
    tmp_if_expr$8 = -((signed int)MVtab2[(signed long int)code].val);

  else
    tmp_if_expr$8 = (signed int)MVtab2[(signed long int)code].val;
  return tmp_if_expr$8;
}

// c::Headers
// file src/mpeg2dec.c line 653
static signed int Headers(void)
{
  signed int ret;
  ld = &base;
  ret=Get_Hdr();
  if(!(Two_Streams == 0))
  {
    ld = &enhan;
    signed int return_value_Get_Hdr$1;
    return_value_Get_Hdr$1=Get_Hdr();
    if(!(return_value_Get_Hdr$1 == ret))
    {
      if(Quiet_Flag == 0)
        fprintf(stderr, "streams out of sync\n");

    }

    ld = &base;
  }

  return ret;
}

// c::Initialize_Buffer
// file src/getbits.c line 96
void Initialize_Buffer(void)
{
  ld->Incnt = 0;
  ld->Rdptr = ld->Rdbfr + (signed long int)2048;
  ld->Rdmax = ld->Rdptr;
  ld->Bfr = (unsigned int)0;
  Flush_Buffer(0);
}

// c::Initialize_Decoder
// file src/mpeg2dec.c line 232
static void Initialize_Decoder(void)
{
  signed int i;
  void *return_value_malloc$1;
  return_value_malloc$1=malloc((unsigned long int)1024);
  Clip = (unsigned char *)return_value_malloc$1;
  if(Clip == ((unsigned char *)NULL))
    Error("Clip[] malloc failed\n");

  Clip = Clip + (signed long int)384;
  i = -384;
  while(i < 640)
  {
    Clip[(signed long int)i] = (unsigned char)(i < 0 ? 0 : (i > 255 ? 255 : i));
    i = i + 1;
  }
  if(!(Reference_IDCT_Flag == 0))
    Initialize_Reference_IDCT();

  else
    Initialize_Fast_IDCT();
}

// c::Initialize_Fast_IDCT
// file src/idct.c line 1020
void Initialize_Fast_IDCT(void)
{
  signed int i;
  signed int j;
  double s;
}

// c::Initialize_Frame_Buffer
// file src/mpeg2dec.c line 215
static void Initialize_Frame_Buffer(void)
{
  signed int i = 0;
  while(i < 2)
  {
    tb[(signed long int)i].frame_buf_size = (unsigned int)2048;
    void *return_value_malloc$1;
    return_value_malloc$1=malloc(1ul /*[[unsigned char]]*/ * (unsigned long int)2048);
    tb[(signed long int)i].frame_buf = (unsigned char *)return_value_malloc$1;
    i = i + 1;
  }
}

// c::Initialize_Reference_IDCT
// file src/idctref.c line 112
void Initialize_Reference_IDCT()
{
  signed int freq;
  signed int time;
  double scale;
  freq = 0;
  double tmp_if_expr$2;
  double return_value_sqrt$1;
  double return_value_cos$3;
  while(freq < 8)
  {
    if(freq == 0)
    {
      return_value_sqrt$1=sqrt(1.250000e-1);
      tmp_if_expr$2 = return_value_sqrt$1;
    }

    else
      tmp_if_expr$2 = 5.000000e-1;
    scale = tmp_if_expr$2;
    time = 0;
    while(time < 8)
    {
      return_value_cos$3=cos((3.141593e+0 / 8.000000) * (double)freq * ((double)time + 5.000000e-1));
      c[(signed long int)freq][(signed long int)time] = scale * return_value_cos$3;
      time = time + 1;
    }
    freq = freq + 1;
  }
}

// c::Initialize_Sequence
// file src/mpeg2dec.c line 254
static void Initialize_Sequence(void)
{
  static signed int Table_6_20[3l] = { 6, 8, 12 };
  signed int cc;
  signed int size;
  if(!(Two_Streams == 0))
  {
    if(!(enhan.scalable_mode == 3))
    {
      if(!(base.scalable_mode == 1))
        Error("unsupported scalability mode\n");

    }

  }

  if(base.MPEG2_Flag == 0)
  {
    progressive_sequence = 1;
    progressive_frame = 1;
    picture_structure = 3;
    frame_pred_frame_dct = 1;
    chroma_format = 1;
    matrix_coefficients = 5;
  }

  mb_width = (horizontal_size + 15) / 16;
  mb_height = base.MPEG2_Flag != 0 && !(progressive_sequence != 0) ? 2 * ((vertical_size + 31) / 32) : (vertical_size + 15) / 16;
  Coded_Picture_Width = 16 * mb_width;
  Coded_Picture_Height = 16 * mb_height;
  printf("height %d width %d\n", Coded_Picture_Height, Coded_Picture_Width);
  Chroma_Width = chroma_format == 3 ? Coded_Picture_Width : Coded_Picture_Width >> 1;
  Chroma_Height = chroma_format != 1 ? Coded_Picture_Height : Coded_Picture_Height >> 1;
  block_count = Table_6_20[(signed long int)(chroma_format - 1)];
  cc = 0;
  void *return_value_malloc$4;
  while(cc < 3)
  {
    if(cc == 0)
      size = Coded_Picture_Width * Coded_Picture_Height;

    else
      size = Chroma_Width * Chroma_Height;
    void *return_value_malloc$1;
    return_value_malloc$1=malloc((unsigned long int)size);
    backward_reference_frame[(signed long int)cc] = (unsigned char *)return_value_malloc$1;
    if(backward_reference_frame[(signed long int)cc] == ((unsigned char *)NULL))
      Error("backward_reference_frame[] malloc failed\n");

    void *return_value_malloc$2;
    return_value_malloc$2=malloc((unsigned long int)size);
    forward_reference_frame[(signed long int)cc] = (unsigned char *)return_value_malloc$2;
    if(forward_reference_frame[(signed long int)cc] == ((unsigned char *)NULL))
      Error("forward_reference_frame[] malloc failed\n");

    void *return_value_malloc$3;
    return_value_malloc$3=malloc((unsigned long int)size);
    auxframe[(signed long int)cc] = (unsigned char *)return_value_malloc$3;
    if(auxframe[(signed long int)cc] == ((unsigned char *)NULL))
      Error("auxframe[] malloc failed\n");

    if(!(Ersatz_Flag == 0))
    {
      return_value_malloc$4=malloc((unsigned long int)size);
      substitute_frame[(signed long int)cc] = (unsigned char *)return_value_malloc$4;
      if(substitute_frame[(signed long int)cc] == ((unsigned char *)NULL))
        Error("substitute_frame[] malloc failed\n");

    }

    if(base.scalable_mode == 2)
    {
      void *return_value_malloc$5;
      return_value_malloc$5=malloc((unsigned long int)((lower_layer_prediction_horizontal_size * lower_layer_prediction_vertical_size) / (cc != 0 ? 4 : 1)));
      llframe0[(signed long int)cc] = (unsigned char *)return_value_malloc$5;
      if(llframe0[(signed long int)cc] == ((unsigned char *)NULL))
        Error("llframe0 malloc failed\n");

      void *return_value_malloc$6;
      return_value_malloc$6=malloc((unsigned long int)((lower_layer_prediction_horizontal_size * lower_layer_prediction_vertical_size) / (cc != 0 ? 4 : 1)));
      llframe1[(signed long int)cc] = (unsigned char *)return_value_malloc$6;
      if(llframe1[(signed long int)cc] == ((unsigned char *)NULL))
        Error("llframe1 malloc failed\n");

    }

    cc = cc + 1;
  }
  if(base.scalable_mode == 2)
  {
    void *return_value_malloc$7;
    return_value_malloc$7=malloc((unsigned long int)(lower_layer_prediction_horizontal_size * ((lower_layer_prediction_vertical_size * vertical_subsampling_factor_n) / vertical_subsampling_factor_m)) * 2ul /*[[signed short int]]*/);
    lltmp = (signed short int *)return_value_malloc$7;
    if(lltmp == ((signed short int *)NULL))
      Error("lltmp malloc failed\n");

  }

}

// c::Make_Spatial_Prediction_Frame
// file src/spatscal.c line 204
static void Make_Spatial_Prediction_Frame(signed int progressive_frame, signed int llprogressive_frame, unsigned char *fld0, unsigned char *fld1, signed short int *tmp, unsigned char *dst, signed int llx0, signed int lly0, signed int llw, signed int llh, signed int horizontal_size, signed int vertical_size, signed int vm, signed int vn, signed int hm, signed int hn, signed int aperture)
{
  signed int w;
  signed int h;
  signed int x0;
  signed int llw2;
  signed int llh2;
  llw2 = (llw * hn) / hm;
  llh2 = (llh * vn) / vm;
  if(!(llprogressive_frame == 0))
    Subsample_Vertical(fld0, tmp, llw, llh, llh2, vm, vn, 0, 1);

  else
    if(!(progressive_frame == 0))
    {
      if(!(lower_layer_deinterlaced_field_select == 0))
      {
        Deinterlace(fld1, fld0, 0, llw, llh, aperture);
        Subsample_Vertical(fld1, tmp, llw, llh, llh2, vm, vn, 0, 1);
      }

      else
      {
        Deinterlace(fld0, fld1, 1, llw, llh, aperture);
        Subsample_Vertical(fld0, tmp, llw, llh, llh2, vm, vn, 0, 1);
      }
    }

    else
    {
      Deinterlace(fld0, fld1, 1, llw, llh, aperture);
      Deinterlace(fld1, fld0, 0, llw, llh, aperture);
      Subsample_Vertical(fld0, tmp, llw, llh, llh2, vm, vn, 0, 2);
      Subsample_Vertical(fld1, tmp, llw, llh, llh2, vm, vn, 1, 2);
    }
  if(lly0 < 0)
  {
    tmp = tmp - (signed long int)(llw * lly0);
    llh2 = llh2 + lly0;
    if(llh2 < 0)
      llh2 = 0;

    h = vertical_size < llh2 ? vertical_size : llh2;
  }

  else
  {
    dst = dst + (signed long int)(horizontal_size * lly0);
    h = vertical_size - lly0;
    if(!(llh2 >= h))
      h = llh2;

  }
  if(llx0 < 0)
  {
    x0 = -llx0;
    llw2 = llw2 + llx0;
    if(llw2 < 0)
      llw2 = 0;

    w = horizontal_size < llw2 ? horizontal_size : llw2;
  }

  else
  {
    dst = dst + (signed long int)llx0;
    x0 = 0;
    w = horizontal_size - llx0;
    if(!(llw2 >= w))
      w = llw2;

  }
  Subsample_Horizontal(tmp, dst, x0, w, llw, horizontal_size, h, hm, hn);
}

// c::Next_Packet
// file src/global.h line 119
void Next_Packet(void)
{
  unsigned int code;
  signed int l;
  signed int return_value_Get_Byte$2;
  signed int return_value_Get_Word$3;
  signed int return_value_Get_Byte$4;
  signed int return_value_Get_Byte$6;
  signed int tmp_post$8;
  signed int tmp_post$9;
  signed int tmp_post$10;
  signed int tmp_post$11;
  do
  {
    signed int return_value_Get_Long$1;
    return_value_Get_Long$1=Get_Long();
    code = (unsigned int)return_value_Get_Long$1;
    while(!((4294967040u & code) == 256u))
    {
      return_value_Get_Byte$2=Get_Byte();
      code = code << 8 | (unsigned int)return_value_Get_Byte$2;
    }
    switch(code)
    {

      case (unsigned int)442:
        {
          ld->Rdptr = ld->Rdptr + (signed long int)8;
          goto __CPROVER_DUMP_L22;
        }
      case (unsigned int)480:
        {
          return_value_Get_Word$3=Get_Word();
          code = (unsigned int)return_value_Get_Word$3;
          ld->Rdmax = ld->Rdptr + (signed long int)code;
          return_value_Get_Byte$4=Get_Byte();
          code = (unsigned int)return_value_Get_Byte$4;
          if(code >> 6 == 2u)
          {
            ld->Rdptr = ld->Rdptr + 1l;
            signed int return_value_Get_Byte$5;
            return_value_Get_Byte$5=Get_Byte();
            code = (unsigned int)return_value_Get_Byte$5;
            ld->Rdptr = ld->Rdptr + (signed long int)code;
            printf("MPEG-2 PES packet\n");
            return;
          }

          else
            if(code == 255u)
              do
              {
                return_value_Get_Byte$6=Get_Byte();
                code = (unsigned int)return_value_Get_Byte$6;
                if(!(code == 255u))
                  goto __CPROVER_DUMP_L8;

              }
              while(TRUE);


        __CPROVER_DUMP_L8:
          ;
          if(code >= 64u)
          {
            if(code >= 128u)
            {
              fprintf(stderr, "Error in packet header\n");
              exit(1);
            }

            ld->Rdptr = ld->Rdptr + 1l;
            signed int return_value_Get_Byte$7;
            return_value_Get_Byte$7=Get_Byte();
            code = (unsigned int)return_value_Get_Byte$7;
          }

          if(code >= 48u)
          {
            if(code >= 64u)
            {
              fprintf(stderr, "Error in packet header\n");
              exit(1);
            }

            ld->Rdptr = ld->Rdptr + (signed long int)9;
          }

          else
            if(code >= 32u)
              ld->Rdptr = ld->Rdptr + (signed long int)4;

            else
              if(!(code == 15u))
              {
                fprintf(stderr, "Error in packet header\n");
                exit(1);
              }

          return;
        }
      case (unsigned int)441:
        {
          l = 0;
          while(l < 2048)
          {
            tmp_post$8 = l;
            l = l + 1;
            ld->Rdbfr[(signed long int)tmp_post$8] = (unsigned char)(439 >> 24);
            tmp_post$9 = l;
            l = l + 1;
            ld->Rdbfr[(signed long int)tmp_post$9] = (unsigned char)(439 >> 16);
            tmp_post$10 = l;
            l = l + 1;
            ld->Rdbfr[(signed long int)tmp_post$10] = (unsigned char)(439 >> 8);
            tmp_post$11 = l;
            l = l + 1;
            ld->Rdbfr[(signed long int)tmp_post$11] = (unsigned char)(439 & 255);
          }
          ld->Rdptr = ld->Rdbfr;
          ld->Rdmax = ld->Rdbfr + (signed long int)2048;
          return;
        }
      default:
        {
          if(code >= 443u)
          {
            signed int return_value_Get_Word$12;
            return_value_Get_Word$12=Get_Word();
            code = (unsigned int)return_value_Get_Word$12;
            ld->Rdptr = ld->Rdptr + (signed long int)code;
          }

          else
          {
            fprintf(stderr, "Unexpected startcode %08x in system layer\n", code);
            exit(1);
          }
          goto __CPROVER_DUMP_L22;
        }
    }

  __CPROVER_DUMP_L22:
    ;
  }
  while(TRUE);
}

// c::Output_Last_Frame_of_Sequence
// file src/getpic.c line 944
void Output_Last_Frame_of_Sequence(signed int Framenum)
{
  if(!(Second_Field == 0))
    printf("last frame incomplete, not stored\n");

  else
    Write_Frame(backward_reference_frame, Framenum - 1);
}

// c::Print_Bits
// file src/mpeg2dec.c line 351
void Print_Bits(signed int code, signed int bits, signed int len)
{
  signed int i = 0;
  while(!(i >= len))
  {
    printf("%d", code >> (bits - 1) - i & 1);
    i = i + 1;
  }
}

// c::Process_Options
// file src/mpeg2dec.c line 362
static void Process_Options(signed int argc, char **argv)
{
  signed int i;
  signed int LastArg;
  signed int NextArg;
  if(argc < 2)
  {
    printf("\n%s, %s\n", (const void *)Version, (const void *)Author);
    printf("Usage:  mpeg2decode {options}\nOptions: -b  file  main bitstream (base or spatial enhancement layer)\n         -cn file  conformance report (n: level)\n         -e  file  enhancement layer bitstream (SNR or Data Partitioning)\n         -f        store/display interlaced video in frame format\n         -g        concatenated file format for substitution method (-x)\n         -in file  information & statistics report  (n: level)\n         -l  file  file name pattern for lower layer sequence\n                   (for spatial scalability)\n         -on file  output format (0:YUV 1:SIF 2:TGA 3:PPM 4:X11 5:X11HiQ)\n         -q        disable warnings to stderr\n         -r        use double precision reference IDCT\n         -t        enable low level tracing to stdout\n         -u  file  print user_data to stdio or file\n         -vn       verbose output (n: level)\n         -x  file  filename pattern of picture substitution sequence\n\nFile patterns:  for sequential filenames, \"printf\" style, e.g. rec%%d\n                 or rec%%d%%c for fieldwise storage\nLevels:        0:none 1:sequence 2:picture 3:slice 4:macroblock 5:block\n\nExample:       mpeg2decode -b bitstream.mpg -f -r -o0 rec%%d\n         \n");
    exit(0);
  }

  Output_Type = -1;
  i = 1;
  signed int tmp_statement_expression$1;
  signed int tmp_if_expr$3;
  const signed int **return_value___ctype_toupper_loc$4;
  while(!(i >= argc))
  {
    LastArg = (signed int)(argc - i == 1);
    if(LastArg == 0)
      NextArg = (signed int)((signed int)argv[(signed long int)(i + 1)][(signed long int)0] == 45);

    else
      NextArg = 0;
    if((signed int)*argv[(signed long int)i] == 45)
    {
      signed int __res;
      if(FALSE)
      {
        if(FALSE)
        {
          signed int __c = (signed int)argv[(signed long int)i][(signed long int)1];
          if(!(__c < -128))
          {
            if(__c > 255)
              goto __CPROVER_DUMP_L5;

          }

          else
          {

          __CPROVER_DUMP_L5:
            ;
            tmp_if_expr$3 = __c;
            goto __CPROVER_DUMP_L7;
          }
          const signed int **return_value___ctype_toupper_loc$2;
          return_value___ctype_toupper_loc$2=__ctype_toupper_loc();
          tmp_if_expr$3 = (*return_value___ctype_toupper_loc$2)[(signed long int)__c];

        __CPROVER_DUMP_L7:
          ;
          __res = tmp_if_expr$3;
        }

        else
          __res=toupper((signed int)argv[(signed long int)i][(signed long int)1]);
      }

      else
      {
        return_value___ctype_toupper_loc$4=__ctype_toupper_loc();
        __res = (*return_value___ctype_toupper_loc$4)[(signed long int)(signed int)argv[(signed long int)i][(signed long int)1]];
      }
      tmp_statement_expression$1 = __res;
      switch(tmp_statement_expression$1)
      {

        case 66:
          {
            Main_Bitstream_Flag = 1;
            if(NextArg == 0)
            {
              if(LastArg != 0)
                goto __CPROVER_DUMP_L13;

            }

            else
            {

            __CPROVER_DUMP_L13:
              ;
              printf("ERROR: -b must be followed the main bitstream filename\n");
              goto __CPROVER_DUMP_L15;
            }
            i = i + 1;
            Main_Bitstream_Filename = argv[(signed long int)i];

          __CPROVER_DUMP_L15:
            ;
            goto __CPROVER_DUMP_L44;
          }
        case 67:
          {
            printf("This program not compiled for Verify_Flag option\n");
            goto __CPROVER_DUMP_L44;
          }
        case 69:
          {
            Two_Streams = 1;
            if(NextArg == 0)
            {
              if(LastArg != 0)
                goto __CPROVER_DUMP_L18;

            }

            else
            {

            __CPROVER_DUMP_L18:
              ;
              printf("ERROR: -e must be followed by filename\n");
              exit(-1);
              goto __CPROVER_DUMP_L20;
            }
            i = i + 1;
            Enhancement_Layer_Bitstream_Filename = argv[(signed long int)i];

          __CPROVER_DUMP_L20:
            ;
            goto __CPROVER_DUMP_L44;
          }
        case 70:
          {
            Frame_Store_Flag = 1;
            goto __CPROVER_DUMP_L44;
          }
        case 71:
          {
            Big_Picture_Flag = 1;
            goto __CPROVER_DUMP_L44;
          }
        case 73:
          {
            printf("WARNING: This program not compiled for -i option\n");
            goto __CPROVER_DUMP_L44;
          }
        case 76:
          {
            Spatial_Flag = 1;
            if(NextArg == 0)
            {
              if(LastArg != 0)
                goto __CPROVER_DUMP_L25;

            }

            else
            {

            __CPROVER_DUMP_L25:
              ;
              printf("ERROR: -l must be followed by filename\n");
              exit(-1);
              goto __CPROVER_DUMP_L27;
            }
            i = i + 1;
            Lower_Layer_Picture_Filename = argv[(signed long int)i];

          __CPROVER_DUMP_L27:
            ;
            goto __CPROVER_DUMP_L44;
          }
        case 79:
          {
            Output_Type=atoi(&argv[(signed long int)i][(signed long int)2]);
            if(!(Output_Type == 4))
            {
              if(Output_Type == 5)
                goto __CPROVER_DUMP_L29;

            }

            else
            {

            __CPROVER_DUMP_L29:
              ;
              Output_Picture_Filename = "";
              goto __CPROVER_DUMP_L33;
            }
            if(NextArg == 0)
            {
              if(LastArg != 0)
                goto __CPROVER_DUMP_L31;

            }

            else
            {

            __CPROVER_DUMP_L31:
              ;
              printf("ERROR: -o must be followed by filename\n");
              exit(-1);
              goto __CPROVER_DUMP_L33;
            }
            i = i + 1;
            Output_Picture_Filename = argv[(signed long int)i];

          __CPROVER_DUMP_L33:
            ;
            goto __CPROVER_DUMP_L44;
          }
        case 81:
          {
            Quiet_Flag = 1;
            goto __CPROVER_DUMP_L44;
          }
        case 82:
          {
            Reference_IDCT_Flag = 1;
            goto __CPROVER_DUMP_L44;
          }
        case 84:
          {
            printf("WARNING: This program not compiled for -t option\n");
            goto __CPROVER_DUMP_L44;
          }
        case 85:
          User_Data_Flag = 1;
        case 86:
          {
            printf("This program not compiled for -v option\n");
            goto __CPROVER_DUMP_L44;
          }
        case 88:
          {
            Ersatz_Flag = 1;
            if(NextArg == 0)
            {
              if(LastArg != 0)
                goto __CPROVER_DUMP_L40;

            }

            else
            {

            __CPROVER_DUMP_L40:
              ;
              printf("ERROR: -x must be followed by filename\n");
              exit(-1);
              goto __CPROVER_DUMP_L42;
            }
            i = i + 1;
            Substitute_Picture_Filename = argv[(signed long int)i];

          __CPROVER_DUMP_L42:
            ;
            goto __CPROVER_DUMP_L44;
          }
        default:
          {
            fprintf(stderr, "undefined option -%c ignored. Exiting program\n", argv[(signed long int)i][(signed long int)1]);
            exit(-1);
          }
      }
    }


  __CPROVER_DUMP_L44:
    ;
    i = i + 1;
  }
  if(!(Main_Bitstream_Flag == 1))
    printf("There must be a main bitstream specified (-b filename)\n");

  if(!(Output_Type == 4))
  {
    if(Output_Type == 5)
      goto __CPROVER_DUMP_L47;

  }

  else
  {

  __CPROVER_DUMP_L47:
    ;
    if(Frame_Store_Flag == 0)
      goto __CPROVER_DUMP_L48;

    Display_Progressive_Flag = 1;
    goto __CPROVER_DUMP_L49;
  }

__CPROVER_DUMP_L48:
  ;
  Display_Progressive_Flag = 0;

__CPROVER_DUMP_L49:
  ;
  if(Output_Type == -1)
  {
    Output_Type = 9;
    Output_Picture_Filename = "";
  }

}

// c::Read_Component
// file src/subspic.c line 293
static signed int Read_Component(char *Filename, unsigned char *Frame, signed int Width, signed int Height)
{
  signed int Size;
  signed int Bytes_Read;
  signed int Infile;
  Size = Width * Height;
  Infile=open(Filename, 0 | 0);
  if((signed int)(Infile == 0) < 0)
  {
    printf("ERROR: unable to open reference filename (%s)\n", Filename);
    return -1;
  }

  signed long int return_value_read$1;
  return_value_read$1=read(Infile, (void *)Frame, (unsigned long int)Size);
  Bytes_Read = (signed int)return_value_read$1;
  if(!(Bytes_Read == Size))
    printf("was able to read only %d bytes of %d of file %s\n", Bytes_Read, Size, Filename);

  close(Infile);
  return 0;
}

// c::Read_Components
// file src/subspic.c line 267
static signed int Read_Components(char *filename, unsigned char **frame, signed int framenum)
{
  signed int err = 0;
  char outname[256l];
  char name[256l];
  sprintf(outname, filename, framenum);
  sprintf(name, "%s.Y", (const void *)outname);
  signed int return_value_Read_Component$1;
  return_value_Read_Component$1=Read_Component(name, frame[(signed long int)0], Coded_Picture_Width, Coded_Picture_Height);
  err = err + return_value_Read_Component$1;
  sprintf(name, "%s.U", (const void *)outname);
  signed int return_value_Read_Component$2;
  return_value_Read_Component$2=Read_Component(name, frame[(signed long int)1], Chroma_Width, Chroma_Height);
  err = err + return_value_Read_Component$2;
  sprintf(name, "%s.V", (const void *)outname);
  signed int return_value_Read_Component$3;
  return_value_Read_Component$3=Read_Component(name, frame[(signed long int)2], Chroma_Width, Chroma_Height);
  err = err + return_value_Read_Component$3;
  return err;
}

// c::Read_Frame
// file src/subspic.c line 207
static void Read_Frame(char *fname, unsigned char **frame, signed int framenum)
{
  signed int parity;
  signed int rerr = 0;
  signed int field_mode;
  if(framenum < 0)
    printf("ERROR: framenum (%d) is less than zero\n", framenum);

  if(!(Big_Picture_Flag == 0))
    rerr=Extract_Components(fname, substitute_frame, framenum);

  else
    rerr=Read_Components(fname, substitute_frame, framenum);
  if(!(rerr == 0))
    printf("was unable to substitute frame\n");

  if(!(Second_Field == 0))
  {
    if(!(picture_coding_type == 2))
      goto __CPROVER_DUMP_L5;

    parity = picture_structure == 1 ? 1 : 0;
    field_mode = picture_structure == 3 ? 0 : 1;
  }

  else
  {

  __CPROVER_DUMP_L5:
    ;
    parity = 0;
    field_mode = 0;
  }
  Copy_Frame(substitute_frame[(signed long int)0], frame[(signed long int)0], Coded_Picture_Width, Coded_Picture_Height, parity, field_mode);
  Copy_Frame(substitute_frame[(signed long int)1], frame[(signed long int)1], Chroma_Width, Chroma_Height, parity, field_mode);
  Copy_Frame(substitute_frame[(signed long int)2], frame[(signed long int)2], Chroma_Width, Chroma_Height, parity, field_mode);
}

// c::Read_Lower_Layer_Component_Fieldwise
// file src/spatscal.c line 163
static void Read_Lower_Layer_Component_Fieldwise(signed int comp, signed int lw, signed int lh)
{
  struct _IO_FILE$link10 *fd;
  char fname[256l];
  char ext[3l][3l] = { { 46, 89, 0 }, { 46, 85, 0 }, { 46, 86, 0 } };
  signed int i;
  signed int j;
  sprintf(fname, Lower_Layer_Picture_Filename, True_Framenum, lower_layer_progressive_frame != 0 ? 102 : 97);
  strcat((const void *)fname, (const void *)ext[(signed long int)comp]);
  fd=fopen(fname, "rb");
  if(fd == ((struct _IO_FILE$link10 *)NULL))
    exit(-1);

  j = 0;
  signed int return_value_fgetc$1;
  while(!(j >= lh))
  {
    i = 0;
    while(!(i >= lw))
    {
      return_value_fgetc$1=fgetc(fd);
      llframe0[(signed long int)comp][(signed long int)(lw * j + i)] = (unsigned char)return_value_fgetc$1;
      i = i + 1;
    }
    j = j + (lower_layer_progressive_frame != 0 ? 1 : 2);
  }
  fclose(fd);
  signed int return_value_fgetc$2;
  if(lower_layer_progressive_frame == 0)
  {
    sprintf(fname, Lower_Layer_Picture_Filename, True_Framenum, 98);
    strcat((const void *)fname, (const void *)ext[(signed long int)comp]);
    fd=fopen(fname, "rb");
    if(fd == ((struct _IO_FILE$link10 *)NULL))
      exit(-1);

    j = 1;
    while(!(j >= lh))
    {
      i = 0;
      while(!(i >= lw))
      {
        return_value_fgetc$2=fgetc(fd);
        llframe1[(signed long int)comp][(signed long int)(lw * j + i)] = (unsigned char)return_value_fgetc$2;
        i = i + 1;
      }
      j = j + 2;
    }
    fclose(fd);
  }

}

// c::Read_Lower_Layer_Component_Framewise
// file src/spatscal.c line 132
static void Read_Lower_Layer_Component_Framewise(signed int comp, signed int lw, signed int lh)
{
  struct _IO_FILE$link10 *fd;
  char fname[256l];
  char ext[3l][3l] = { { 46, 89, 0 }, { 46, 85, 0 }, { 46, 86, 0 } };
  signed int i;
  signed int j;
  sprintf(fname, Lower_Layer_Picture_Filename, True_Framenum);
  strcat((const void *)fname, (const void *)ext[(signed long int)comp]);
  fd=fopen(fname, "rb");
  if(fd == ((struct _IO_FILE$link10 *)NULL))
    exit(-1);

  j = 0;
  signed int return_value_fgetc$1;
  signed int return_value_fgetc$2;
  while(!(j >= lh))
  {
    i = 0;
    while(!(i >= lw))
    {
      return_value_fgetc$1=fgetc(fd);
      llframe0[(signed long int)comp][(signed long int)(lw * j + i)] = (unsigned char)return_value_fgetc$1;
      i = i + 1;
    }
    if(lower_layer_progressive_frame == 0)
    {
      j = j + 1;
      i = 0;
      while(!(i >= lw))
      {
        return_value_fgetc$2=fgetc(fd);
        llframe1[(signed long int)comp][(signed long int)(lw * j + i)] = (unsigned char)return_value_fgetc$2;
        i = i + 1;
      }
    }

    j = j + 1;
  }
  fclose(fd);
}

// c::Reference_IDCT
// file src/global.h line 163
void Reference_IDCT(signed short int *block)
{
  signed int i;
  signed int j;
  signed int k;
  signed int v;
  double partial_product;
  double tmp[64l];
  i = 0;
  while(i < 8)
  {
    j = 0;
    while(j < 8)
    {
      partial_product = 0.000000;
      k = 0;
      while(k < 8)
      {
        partial_product = partial_product + c[(signed long int)k][(signed long int)j] * (double)block[(signed long int)(8 * i + k)];
        k = k + 1;
      }
      tmp[(signed long int)(8 * i + j)] = partial_product;
      j = j + 1;
    }
    i = i + 1;
  }
  j = 0;
  while(j < 8)
  {
    i = 0;
    while(i < 8)
    {
      partial_product = 0.000000;
      k = 0;
      while(k < 8)
      {
        partial_product = partial_product + c[(signed long int)k][(signed long int)i] * tmp[(signed long int)(8 * k + j)];
        k = k + 1;
      }
      double return_value_floor$1;
      return_value_floor$1=floor(partial_product + 5.000000e-1);
      v = (signed int)return_value_floor$1;
      block[(signed long int)(8 * i + j)] = (signed short int)(v < -256 ? -256 : (v > 255 ? 255 : v));
      i = i + 1;
    }
    j = j + 1;
  }
}

// c::Saturate
// file src/getpic.c line 783
static void Saturate(signed short int *Block_Ptr)
{
  signed int i;
  signed int sum;
  signed int val;
  signed int j;
  sum = 0;
  i = 0;
  while(i < 64)
  {
    j = 0;
    while(j < 8)
    {
      val = (signed int)Block_Ptr[(signed long int)i];
      if(val > 2047)
        val = 2047;

      else
        if(val < -2048)
          val = -2048;

      Block_Ptr[(signed long int)i] = (signed short int)val;
      sum = sum + val;
      j = j + 1;
      i = i + 1;
    }
  }
  if((1 & sum) == 0)
    Block_Ptr[(signed long int)63] = Block_Ptr[(signed long int)63] ^ (signed short int)1;

}

// c::Show_Bits
// file src/getbits.c line 174
unsigned int Show_Bits(signed int N)
{
  return ld->Bfr >> 32 - N;
}

// c::Spatial_Prediction
// file src/global.h line 191
void Spatial_Prediction(void)
{
  if(!(Frame_Store_Flag == 0))
  {
    Read_Lower_Layer_Component_Framewise(0, lower_layer_prediction_horizontal_size, lower_layer_prediction_vertical_size);
    Read_Lower_Layer_Component_Framewise(1, lower_layer_prediction_horizontal_size >> 1, lower_layer_prediction_vertical_size >> 1);
    Read_Lower_Layer_Component_Framewise(2, lower_layer_prediction_horizontal_size >> 1, lower_layer_prediction_vertical_size >> 1);
  }

  else
  {
    Read_Lower_Layer_Component_Fieldwise(0, lower_layer_prediction_horizontal_size, lower_layer_prediction_vertical_size);
    Read_Lower_Layer_Component_Fieldwise(1, lower_layer_prediction_horizontal_size >> 1, lower_layer_prediction_vertical_size >> 1);
    Read_Lower_Layer_Component_Fieldwise(2, lower_layer_prediction_horizontal_size >> 1, lower_layer_prediction_vertical_size >> 1);
  }
  Make_Spatial_Prediction_Frame(progressive_frame, lower_layer_progressive_frame, llframe0[(signed long int)0], llframe1[(signed long int)0], lltmp, current_frame[(signed long int)0], lower_layer_horizontal_offset, lower_layer_vertical_offset, lower_layer_prediction_horizontal_size, lower_layer_prediction_vertical_size, horizontal_size, vertical_size, vertical_subsampling_factor_m, vertical_subsampling_factor_n, horizontal_subsampling_factor_m, horizontal_subsampling_factor_n, (signed int)(picture_structure != 3));
  Make_Spatial_Prediction_Frame(progressive_frame, lower_layer_progressive_frame, llframe0[(signed long int)1], llframe1[(signed long int)1], lltmp, current_frame[(signed long int)1], lower_layer_horizontal_offset / 2, lower_layer_vertical_offset / 2, lower_layer_prediction_horizontal_size >> 1, lower_layer_prediction_vertical_size >> 1, horizontal_size >> 1, vertical_size >> 1, vertical_subsampling_factor_m, vertical_subsampling_factor_n, horizontal_subsampling_factor_m, horizontal_subsampling_factor_n, 1);
  Make_Spatial_Prediction_Frame(progressive_frame, lower_layer_progressive_frame, llframe0[(signed long int)2], llframe1[(signed long int)2], lltmp, current_frame[(signed long int)2], lower_layer_horizontal_offset / 2, lower_layer_vertical_offset / 2, lower_layer_prediction_horizontal_size >> 1, lower_layer_prediction_vertical_size >> 1, horizontal_size >> 1, vertical_size >> 1, vertical_subsampling_factor_m, vertical_subsampling_factor_n, horizontal_subsampling_factor_m, horizontal_subsampling_factor_n, 1);
}

// c::Subsample_Horizontal
// file src/spatscal.c line 354
static void Subsample_Horizontal(signed short int *s, unsigned char *d, signed int x0, signed int lx, signed int lxs, signed int lxd, signed int ly, signed int m, signed int n)
{
  signed int i;
  signed int i1;
  signed int j;
  signed int id;
  signed int c1;
  signed int c2;
  signed int v;
  signed short int *s1;
  signed short int *s2;
  unsigned char *d1;
  i1 = 0;
  while(!(i1 >= lx))
  {
    d1 = d + (signed long int)i1;
    i = x0 + i1;
    id = (i * m) / n;
    s1 = s + (signed long int)id;
    s2 = id < lxs - 1 ? s1 + (signed long int)1 : s1;
    c2 = (16 * ((i * m) % n) + (n >> 1)) / n;
    c1 = 16 - c2;
    j = 0;
    while(!(j >= ly))
    {
      v = c1 * (signed int)*s1 + c2 * (signed int)*s2;
      *d1 = (unsigned char)(v + (v >= 0 ? 128 : 127) >> 8);
      d1 = d1 + (signed long int)lxd;
      s1 = s1 + (signed long int)lxs;
      s2 = s2 + (signed long int)lxs;
      j = j + 1;
    }
    i1 = i1 + 1;
  }
}

// c::Subsample_Vertical
// file src/spatscal.c line 331
static void Subsample_Vertical(unsigned char *s, signed short int *d, signed int lx, signed int lys, signed int lyd, signed int m, signed int n, signed int j0, signed int dj)
{
  signed int i;
  signed int j;
  signed int c1;
  signed int c2;
  signed int jd;
  unsigned char *s1;
  unsigned char *s2;
  signed short int *d1;
  j = j0;
  while(!(j >= lyd))
  {
    d1 = d + (signed long int)(lx * j);
    jd = (j * m) / n;
    s1 = s + (signed long int)(lx * jd);
    s2 = jd < lys - 1 ? s1 + (signed long int)lx : s1;
    c2 = (16 * ((j * m) % n) + (n >> 1)) / n;
    c1 = 16 - c2;
    i = 0;
    while(!(i >= lx))
    {
      d1[(signed long int)i] = (signed short int)(c1 * (signed int)s1[(signed long int)i] + c2 * (signed int)s2[(signed long int)i]);
      i = i + 1;
    }
    j = j + dj;
  }
}

// c::Substitute_Frame_Buffer
// file src/global.h line 96
void Substitute_Frame_Buffer(signed int bitstream_framenum, signed int sequence_framenum)
{
  static signed int bgate;
  static signed int previous_anchor_bitstream_framenum;
  static signed int previous_anchor_temporal_reference;
  static signed int previous_bitstream_framenum;
  static signed int previous_picture_coding_type;
  static signed int previous_temporal_reference;
  signed int substitute_display_framenum;
  if(sequence_framenum == 0)
  {
    if(Second_Field != 0)
      goto __CPROVER_DUMP_L1;

  }

  else
  {

  __CPROVER_DUMP_L1:
    ;
    if(!(picture_structure == 3))
    {
      if(Second_Field == 0)
        goto __CPROVER_DUMP_L2;

    }

    else
    {

    __CPROVER_DUMP_L2:
      ;
      if(picture_coding_type == 2)
      {
        substitute_display_framenum = bitstream_framenum - 1;
        Read_Frame(Substitute_Picture_Filename, forward_reference_frame, substitute_display_framenum);
      }

      else
        if(picture_coding_type == 3)
        {
          if(!(bgate == 1))
          {
            substitute_display_framenum = ((previous_temporal_reference - temporal_reference) + bitstream_framenum) - 1;
            Read_Frame(Substitute_Picture_Filename, backward_reference_frame, substitute_display_framenum);
          }

        }

      goto __CPROVER_DUMP_L8;
    }
    if(!(Second_Field == 0))
    {
      if(picture_coding_type == 2)
      {
        if(previous_picture_coding_type == 1)
        {
          if(!(picture_coding_type == 2))
            goto __CPROVER_DUMP_L6;

          substitute_display_framenum = bitstream_framenum;
        }

        else
        {

        __CPROVER_DUMP_L6:
          ;
          substitute_display_framenum = ((temporal_reference - previous_anchor_temporal_reference) + bitstream_framenum) - 1;
        }
        Read_Frame(Substitute_Picture_Filename, current_frame, substitute_display_framenum);
      }

    }

  }

__CPROVER_DUMP_L8:
  ;
  if(picture_coding_type == 3)
    bgate = 1;

  else
    bgate = 0;
  if(!(picture_structure == 3))
  {
    if(Second_Field == 0)
      goto __CPROVER_DUMP_L11;

  }

  else
  {

  __CPROVER_DUMP_L11:
    ;
    previous_temporal_reference = temporal_reference;
    previous_bitstream_framenum = bitstream_framenum;
  }
  if(!(picture_coding_type == 3))
  {
    if(!(picture_structure == 3))
    {
      if(Second_Field != 0)
        goto __CPROVER_DUMP_L13;

    }

    else
    {

    __CPROVER_DUMP_L13:
      ;
      previous_anchor_temporal_reference = temporal_reference;
      previous_anchor_bitstream_framenum = bitstream_framenum;
    }
  }

  previous_picture_coding_type = picture_coding_type;
}

// c::Sum_Block
// file src/getpic.c line 766
static void Sum_Block(signed int comp)
{
  signed short int *Block_Ptr1;
  signed short int *Block_Ptr2;
  signed int i;
  Block_Ptr1 = base.block[(signed long int)comp];
  Block_Ptr2 = enhan.block[(signed long int)comp];
  i = 0;
  signed short int *tmp_post$1;
  signed short int *tmp_post$2;
  while(i < 64)
  {
    tmp_post$1 = Block_Ptr1;
    Block_Ptr1 = Block_Ptr1 + 1l;
    tmp_post$2 = Block_Ptr2;
    Block_Ptr2 = Block_Ptr2 + 1l;
    *tmp_post$1 = *tmp_post$1 + *tmp_post$2;
    i = i + 1;
  }
}

// c::Thrd_Add_Block
// file src/getpic.c line 2302
static void Thrd_Add_Block(signed int t, signed int comp, signed int bx, signed int by, signed int dct_type, signed int addflag)
{
  signed int cc;
  signed int i;
  signed int j;
  signed int iincr;
  unsigned char *rfp;
  signed short int *bptr;
  signed short int tmp;
  cc = comp < 4 ? 0 : (comp & 1) + 1;
  if(cc == 0)
  {
    if(picture_structure == 3)
    {
      if(!(dct_type == 0))
      {
        rfp = current_frame[(signed long int)0] + (signed long int)(Coded_Picture_Width * (by + ((comp & 2) >> 1))) + (signed long int)bx + (signed long int)((comp & 1) << 3);
        iincr = (Coded_Picture_Width << 1) - 8;
      }

      else
      {
        rfp = current_frame[(signed long int)0] + (signed long int)(Coded_Picture_Width * (by + ((comp & 2) << 2))) + (signed long int)bx + (signed long int)((comp & 1) << 3);
        iincr = Coded_Picture_Width - 8;
      }
    }

    else
    {
      rfp = current_frame[(signed long int)0] + (signed long int)((Coded_Picture_Width << 1) * (by + ((comp & 2) << 2))) + (signed long int)bx + (signed long int)((comp & 1) << 3);
      iincr = (Coded_Picture_Width << 1) - 8;
    }
  }

  else
  {
    if(!(chroma_format == 3))
      bx = bx >> 1;

    if(chroma_format == 1)
      by = by >> 1;

    if(picture_structure == 3)
    {
      if(!(dct_type == 0))
      {
        if(chroma_format == 1)
          goto __CPROVER_DUMP_L8;

        rfp = current_frame[(signed long int)cc] + (signed long int)(Chroma_Width * (by + ((comp & 2) >> 1))) + (signed long int)bx + (signed long int)(comp & 8);
        iincr = (Chroma_Width << 1) - 8;
      }

      else
      {

      __CPROVER_DUMP_L8:
        ;
        rfp = current_frame[(signed long int)cc] + (signed long int)(Chroma_Width * (by + ((comp & 2) << 2))) + (signed long int)bx + (signed long int)(comp & 8);
        iincr = Chroma_Width - 8;
      }
    }

    else
    {
      rfp = current_frame[(signed long int)cc] + (signed long int)((Chroma_Width << 1) * (by + ((comp & 2) << 2))) + (signed long int)bx + (signed long int)(comp & 8);
      iincr = (Chroma_Width << 1) - 8;
    }
  }
  bptr = thrd_ld[(signed long int)t].block[(signed long int)comp];
  if(!(addflag == 0))
  {
    i = 0;
    while(i < 4)
    {
      j = 0;
      while(j < 8)
      {
        tmp = (signed short int)((signed int)*bptr + (signed int)*rfp);
        tmp = (signed short int)((signed int)tmp < 0 ? 0 : ((signed int)tmp > 255 ? 255 : (signed int)tmp));
        *rfp = (unsigned char)tmp;
        bptr = bptr + 1l;
        rfp = rfp + 1l;
        j = j + 1;
      }
      rfp = rfp + (signed long int)iincr;
      j = 0;
      while(j < 8)
      {
        tmp = (signed short int)((signed int)*bptr + (signed int)*rfp);
        tmp = (signed short int)((signed int)tmp < 0 ? 0 : ((signed int)tmp > 255 ? 255 : (signed int)tmp));
        *rfp = (unsigned char)tmp;
        bptr = bptr + 1l;
        rfp = rfp + 1l;
        j = j + 1;
      }
      rfp = rfp + (signed long int)iincr;
      i = i + 1;
    }
  }

  else
  {
    i = 0;
    while(i < 4)
    {
      j = 0;
      while(j < 8)
      {
        tmp = (signed short int)((signed int)*bptr + 128);
        tmp = (signed short int)((signed int)tmp < 0 ? 0 : ((signed int)tmp > 255 ? 255 : (signed int)tmp));
        *rfp = (unsigned char)tmp;
        rfp = rfp + 1l;
        bptr = bptr + 1l;
        j = j + 1;
      }
      rfp = rfp + (signed long int)iincr;
      j = 0;
      while(j < 8)
      {
        tmp = (signed short int)((signed int)*bptr + 128);
        tmp = (signed short int)((signed int)tmp < 0 ? 0 : ((signed int)tmp > 255 ? 255 : (signed int)tmp));
        *rfp = (unsigned char)tmp;
        rfp = rfp + 1l;
        bptr = bptr + 1l;
        j = j + 1;
      }
      rfp = rfp + (signed long int)iincr;
      i = i + 1;
    }
  }
}

// c::Thrd_Clear_Block
// file src/getpic.c line 2263
static void Thrd_Clear_Block(signed int t, signed int comp)
{
  signed short int *Block_Ptr;
  signed int i;
  signed int j;
  Block_Ptr = thrd_ld[(signed long int)t].block[(signed long int)comp];
  i = 0;
  while(i < 64)
  {
    Block_Ptr[(signed long int)i] = (signed short int)0;
    Block_Ptr[(signed long int)(i + 1)] = (signed short int)0;
    Block_Ptr[(signed long int)(i + 2)] = (signed short int)0;
    Block_Ptr[(signed long int)(i + 3)] = (signed short int)0;
    Block_Ptr[(signed long int)(i + 4)] = (signed short int)0;
    Block_Ptr[(signed long int)(i + 5)] = (signed short int)0;
    Block_Ptr[(signed long int)(i + 6)] = (signed short int)0;
    Block_Ptr[(signed long int)(i + 7)] = (signed short int)0;
    i = i + 8;
  }
}

// c::Thrd_Decode_MPEG2_Intra_Block
// file src/getblk.c line 626
void Thrd_Decode_MPEG2_Intra_Block(signed int t, signed int comp, signed int *dc_dct_pred)
{
  signed int val;
  signed int i;
  signed int j;
  signed int sign;
  signed int nc;
  signed int cc;
  signed int run;
  unsigned int code;
  struct anon$1 *tab;
  signed short int *bp;
  signed int *qmat;
  struct layer_data *ld1;
  bp = thrd_ld[(signed long int)t].block[(signed long int)comp];
  ld1 = ld;
  cc = comp < 4 ? 0 : (comp & 1) + 1;
  signed int *tmp_if_expr$1;
  if(!(comp < 4))
  {
    if(chroma_format == 1)
      goto __CPROVER_DUMP_L1;

  }

  else
  {

  __CPROVER_DUMP_L1:
    ;
    tmp_if_expr$1 = ld1->intra_quantizer_matrix;
    goto __CPROVER_DUMP_L3;
  }
  tmp_if_expr$1 = ld1->chroma_intra_quantizer_matrix;

__CPROVER_DUMP_L3:
  ;
  qmat = tmp_if_expr$1;
  signed int return_value_Thrd_Get_Luma_DC_dct_diff$2;
  signed int return_value_Thrd_Get_Chroma_DC_dct_diff$3;
  signed int return_value_Thrd_Get_Chroma_DC_dct_diff$4;
  if(cc == 0)
  {
    return_value_Thrd_Get_Luma_DC_dct_diff$2=Thrd_Get_Luma_DC_dct_diff(t);
    dc_dct_pred[(signed long int)0] = dc_dct_pred[(signed long int)0] + return_value_Thrd_Get_Luma_DC_dct_diff$2;
    val = dc_dct_pred[(signed long int)0];
  }

  else
    if(cc == 1)
    {
      return_value_Thrd_Get_Chroma_DC_dct_diff$3=Thrd_Get_Chroma_DC_dct_diff(t);
      dc_dct_pred[(signed long int)1] = dc_dct_pred[(signed long int)1] + return_value_Thrd_Get_Chroma_DC_dct_diff$3;
      val = dc_dct_pred[(signed long int)1];
    }

    else
    {
      return_value_Thrd_Get_Chroma_DC_dct_diff$4=Thrd_Get_Chroma_DC_dct_diff(t);
      dc_dct_pred[(signed long int)2] = dc_dct_pred[(signed long int)2] + return_value_Thrd_Get_Chroma_DC_dct_diff$4;
      val = dc_dct_pred[(signed long int)2];
    }
  if(!(Fault_Flag == 0))
    return;

  bp[(signed long int)0] = (signed short int)(val << 3 - intra_dc_precision);
  nc = 0;
  i = 1;
  do
  {
    code=Thrd_Show_Bits(t, 16);
    if(code >= 16384u)
    {
      if(intra_vlc_format != 0)
        goto __CPROVER_DUMP_L9;

      tab = &DCTtabnext[(signed long int)((code >> 12) - (unsigned int)4)];
    }

    else
    {

    __CPROVER_DUMP_L9:
      ;
      if(code >= 1024u)
      {
        if(!(intra_vlc_format == 0))
          tab = &DCTtab0a[(signed long int)((code >> 8) - (unsigned int)4)];

        else
          tab = &DCTtab0[(signed long int)((code >> 8) - (unsigned int)4)];
      }

      else
        if(code >= 512u)
        {
          if(!(intra_vlc_format == 0))
            tab = &DCTtab1a[(signed long int)((code >> 6) - (unsigned int)8)];

          else
            tab = &DCTtab1[(signed long int)((code >> 6) - (unsigned int)8)];
        }

        else
          if(code >= 256u)
            tab = &DCTtab2[(signed long int)((code >> 4) - (unsigned int)16)];

          else
            if(code >= 128u)
              tab = &DCTtab3[(signed long int)((code >> 3) - (unsigned int)16)];

            else
              if(code >= 64u)
                tab = &DCTtab4[(signed long int)((code >> 2) - (unsigned int)16)];

              else
                if(code >= 32u)
                  tab = &DCTtab5[(signed long int)((code >> 1) - (unsigned int)16)];

                else
                  if(code >= 16u)
                    tab = &DCTtab6[(signed long int)(code - (unsigned int)16)];

                  else
                  {
                    if(Quiet_Flag == 0)
                      printf("invalid Huffman code in Decode_MPEG2_Intra_Block()\n");

                    Fault_Flag = 1;
                    return;
                  }
    }
    Thrd_Flush_Buffer(t, (signed int)tab->len);
    if((signed int)tab->run == 64)
      return;

    if((signed int)tab->run == 65)
    {
      unsigned int return_value_Thrd_Get_Bits$5;
      return_value_Thrd_Get_Bits$5=Thrd_Get_Bits(t, 6);
      run = (signed int)return_value_Thrd_Get_Bits$5;
      i = i + run;
      unsigned int return_value_Thrd_Get_Bits$6;
      return_value_Thrd_Get_Bits$6=Thrd_Get_Bits(t, 12);
      val = (signed int)return_value_Thrd_Get_Bits$6;
      if((2047 & val) == 0)
      {
        if(Quiet_Flag == 0)
          printf("invalid escape in Decode_MPEG2_Intra_Block()\n");

        Fault_Flag = 1;
        return;
      }

      sign = (signed int)(val >= 2048);
      if(!(sign == 0))
        val = 4096 - val;

    }

    else
    {
      run = (signed int)tab->run;
      i = i + run;
      val = (signed int)tab->level;
      unsigned int return_value_Thrd_Get_Bits$7;
      return_value_Thrd_Get_Bits$7=Thrd_Get_Bits(t, 1);
      sign = (signed int)return_value_Thrd_Get_Bits$7;
    }
    if(i >= 64)
    {
      if(Quiet_Flag == 0)
        fprintf(stderr, "DCT coeff index (i) out of bounds (intra2)\n");

      Fault_Flag = 1;
      return;
    }

    j = (signed int)scan[(signed long int)ld1->alternate_scan][(signed long int)i];
    val = val * thrd_ld[(signed long int)t].quantizer_scale * qmat[(signed long int)j] >> 4;
    bp[(signed long int)j] = (signed short int)(sign != 0 ? -val : val);
    nc = nc + 1;
    if(base.scalable_mode == 1)
    {
      if(nc == -63 + base.priority_breakpoint)
        ld = &enhan;

    }

    i = i + 1;
  }
  while(TRUE);
}

// c::Thrd_Decode_MPEG2_Non_Intra_Block
// file src/getblk.c line 751
void Thrd_Decode_MPEG2_Non_Intra_Block(signed int t, signed int comp)
{
  signed int val;
  signed int i;
  signed int j;
  signed int sign;
  signed int nc;
  signed int run;
  unsigned int code;
  struct anon$1 *tab;
  signed short int *bp;
  signed int *qmat;
  struct layer_data *ld1 = ld;
  bp = thrd_ld[(signed long int)t].block[(signed long int)comp];
  if(base.scalable_mode == 1)
  {
    if(base.priority_breakpoint < 64)
      ld = &enhan;

    else
      ld = &base;
  }

  signed int *tmp_if_expr$1;
  if(!(comp < 4))
  {
    if(chroma_format == 1)
      goto __CPROVER_DUMP_L3;

  }

  else
  {

  __CPROVER_DUMP_L3:
    ;
    tmp_if_expr$1 = ld1->non_intra_quantizer_matrix;
    goto __CPROVER_DUMP_L5;
  }
  tmp_if_expr$1 = ld1->chroma_non_intra_quantizer_matrix;

__CPROVER_DUMP_L5:
  ;
  qmat = tmp_if_expr$1;
  nc = 0;
  i = 0;
  do
  {
    code=Thrd_Show_Bits(t, 16);
    if(code >= 16384u)
    {
      if(i == 0)
        tab = &DCTtabfirst[(signed long int)((code >> 12) - (unsigned int)4)];

      else
        tab = &DCTtabnext[(signed long int)((code >> 12) - (unsigned int)4)];
    }

    else
      if(code >= 1024u)
        tab = &DCTtab0[(signed long int)((code >> 8) - (unsigned int)4)];

      else
        if(code >= 512u)
          tab = &DCTtab1[(signed long int)((code >> 6) - (unsigned int)8)];

        else
          if(code >= 256u)
            tab = &DCTtab2[(signed long int)((code >> 4) - (unsigned int)16)];

          else
            if(code >= 128u)
              tab = &DCTtab3[(signed long int)((code >> 3) - (unsigned int)16)];

            else
              if(code >= 64u)
                tab = &DCTtab4[(signed long int)((code >> 2) - (unsigned int)16)];

              else
                if(code >= 32u)
                  tab = &DCTtab5[(signed long int)((code >> 1) - (unsigned int)16)];

                else
                  if(code >= 16u)
                    tab = &DCTtab6[(signed long int)(code - (unsigned int)16)];

                  else
                  {
                    if(Quiet_Flag == 0)
                      printf("invalid Huffman code in Decode_MPEG2_Non_Intra_Block()\n");

                    Fault_Flag = 1;
                    return;
                  }
    Thrd_Flush_Buffer(t, (signed int)tab->len);
    if((signed int)tab->run == 64)
      return;

    if((signed int)tab->run == 65)
    {
      unsigned int return_value_Thrd_Get_Bits$2;
      return_value_Thrd_Get_Bits$2=Thrd_Get_Bits(t, 6);
      run = (signed int)return_value_Thrd_Get_Bits$2;
      i = i + run;
      unsigned int return_value_Thrd_Get_Bits$3;
      return_value_Thrd_Get_Bits$3=Thrd_Get_Bits(t, 12);
      val = (signed int)return_value_Thrd_Get_Bits$3;
      if((2047 & val) == 0)
      {
        if(Quiet_Flag == 0)
          printf("invalid escape in Decode_MPEG2_Intra_Block()\n");

        Fault_Flag = 1;
        return;
      }

      sign = (signed int)(val >= 2048);
      if(!(sign == 0))
        val = 4096 - val;

    }

    else
    {
      run = (signed int)tab->run;
      i = i + run;
      val = (signed int)tab->level;
      unsigned int return_value_Thrd_Get_Bits$4;
      return_value_Thrd_Get_Bits$4=Thrd_Get_Bits(t, 1);
      sign = (signed int)return_value_Thrd_Get_Bits$4;
    }
    if(i >= 64)
    {
      if(Quiet_Flag == 0)
        fprintf(stderr, "DCT coeff index (i) out of bounds (inter2)\n");

      Fault_Flag = 1;
      return;
    }

    j = (signed int)scan[(signed long int)ld1->alternate_scan][(signed long int)i];
    val = ((val << 1) + 1) * thrd_ld[(signed long int)t].quantizer_scale * qmat[(signed long int)j] >> 5;
    bp[(signed long int)j] = (signed short int)(sign != 0 ? -val : val);
    nc = nc + 1;
    if(base.scalable_mode == 1)
    {
      if(nc == -63 + base.priority_breakpoint)
        ld = &enhan;

    }

    i = i + 1;
  }
  while(TRUE);
}

// c::Thrd_Flush_Buffer
// file src/getbits.c line 306
void Thrd_Flush_Buffer(signed int t, signed int N)
{
  signed int Incnt;
  thrd_buf[(signed long int)t] = thrd_buf[(signed long int)t] << N;
  thrd_Incnt[(signed long int)t] = thrd_Incnt[(signed long int)t] - N;
  Incnt = thrd_Incnt[(signed long int)t];
  _Bool tmp_if_expr$3;
  unsigned char *tmp_post$2;
  if(Incnt <= 24)
  {
    if(!(System_Stream_Flag == 0))
      tmp_if_expr$3 = ld->Rdptr >= ld->Rdmax - (signed long int)4 ? TRUE : FALSE;

    else
      tmp_if_expr$3 = FALSE;
    if(tmp_if_expr$3)
    {
    /* assertion 0&&"System_Strem_Flag is 1\n" */

    __CPROVER_DUMP_L3:
      ;
      /* assertion 0&&"System_Strem_Flag is 1\n" */
      assert(FALSE);
      while(TRUE)
      {
        if(!(ld->Rdptr >= ld->Rdmax))
          goto __CPROVER_DUMP_L5;

        Next_Packet();

      __CPROVER_DUMP_L5:
        ;
        signed int return_value_Get_Byte$1;
        return_value_Get_Byte$1=Get_Byte();
        ld->Bfr = ld->Bfr | (unsigned int)(return_value_Get_Byte$1 << 24 - Incnt);
        Incnt = Incnt + 8;
        if(!(Incnt <= 24))
          break;

      }
    }

    else
      do
      {
        tmp_post$2 = thrd_ptr[(signed long int)t];
        thrd_ptr[(signed long int)t] = thrd_ptr[(signed long int)t] + 1l;
        thrd_buf[(signed long int)t] = thrd_buf[(signed long int)t] | (unsigned int)((signed int)*tmp_post$2 << 24 - Incnt);
        Incnt = Incnt + 8;
      }
      while(Incnt <= 24);
    thrd_Incnt[(signed long int)t] = Incnt;
  }

}

// c::Thrd_Flush_Buffer32
// file src/global.h line 125
void Thrd_Flush_Buffer32(signed int t)
{
  signed int Incnt;
  thrd_buf[(signed long int)t] = (unsigned int)0;
  Incnt = thrd_Incnt[(signed long int)t];
  Incnt = Incnt - 32;
  _Bool tmp_if_expr$3;
  if(!(System_Stream_Flag == 0))
    tmp_if_expr$3 = ld->Rdptr >= ld->Rdmax - (signed long int)4 ? TRUE : FALSE;

  else
    tmp_if_expr$3 = FALSE;
  unsigned char *tmp_post$2;
  if(tmp_if_expr$3)
  {
    if(!(System_Stream_Flag == 0))
    {
      printf("System_Stream_Flag is 1\n");
      exit(1);
    }

    while(Incnt <= 24)
    {
      if(ld->Rdptr >= ld->Rdmax)
        Next_Packet();

      signed int return_value_Get_Byte$1;
      return_value_Get_Byte$1=Get_Byte();
      ld->Bfr = ld->Bfr | (unsigned int)(return_value_Get_Byte$1 << 24 - Incnt);
      Incnt = Incnt + 8;
    }
  }

  else
    while(Incnt <= 24)
    {
      tmp_post$2 = thrd_ptr[(signed long int)t];
      thrd_ptr[(signed long int)t] = thrd_ptr[(signed long int)t] + 1l;
      thrd_buf[(signed long int)t] = thrd_buf[(signed long int)t] | (unsigned int)((signed int)*tmp_post$2 << 24 - Incnt);
      Incnt = Incnt + 8;
    }
  thrd_Incnt[(signed long int)t] = Incnt;
}

// c::Thrd_Get_B_macroblock_type
// file src/getvlc.c line 939
static signed int Thrd_Get_B_macroblock_type(signed int t)
{
  signed int code;
  unsigned int return_value_Thrd_Show_Bits$1;
  return_value_Thrd_Show_Bits$1=Thrd_Show_Bits(t, 6);
  code = (signed int)return_value_Thrd_Show_Bits$1;
  if(code >= 8)
  {
    code = code >> 2;
    Thrd_Flush_Buffer(t, (signed int)BMBtab0[(signed long int)code].len);
    return (signed int)BMBtab0[(signed long int)code].val;
  }

  if(code == 0)
  {
    if(Quiet_Flag == 0)
      printf("Invalid macroblock_type code\n");

    Fault_Flag = 1;
    return 0;
  }

  Thrd_Flush_Buffer(t, (signed int)BMBtab1[(signed long int)code].len);
  return (signed int)BMBtab1[(signed long int)code].val;
}

// c::Thrd_Get_Bits
// file src/getbits.c line 339
unsigned int Thrd_Get_Bits(signed int t, signed int N)
{
  unsigned int Val;
  Val=Thrd_Show_Bits(t, N);
  Thrd_Flush_Buffer(t, N);
  return Val;
}

// c::Thrd_Get_Bits1
// file src/getbits.c line 298
unsigned int Thrd_Get_Bits1(signed int t)
{
  unsigned int return_value_Thrd_Get_Bits$1;
  return_value_Thrd_Get_Bits$1=Thrd_Get_Bits(t, 1);
  return return_value_Thrd_Get_Bits$1;
}

// c::Thrd_Get_Bits32
// file src/systems.c line 286
unsigned int Thrd_Get_Bits32(signed int t)
{
  unsigned int l;
  l=Thrd_Show_Bits(t, 32);
  Thrd_Flush_Buffer32(t);
  return l;
}

// c::Thrd_Get_Byte
// file src/getbits.c line 271
signed int Thrd_Get_Byte(signed int t)
{
  unsigned char *tmp_post$1 = thrd_ptr[(signed long int)t];
  thrd_ptr[(signed long int)t] = thrd_ptr[(signed long int)t] + 1l;
  return (signed int)*tmp_post$1;
}

// c::Thrd_Get_Chroma_DC_dct_diff
// file src/global.h line 210
signed int Thrd_Get_Chroma_DC_dct_diff(signed int t)
{
  signed int code;
  signed int size;
  signed int dct_diff;
  unsigned int return_value_Thrd_Show_Bits$1;
  return_value_Thrd_Show_Bits$1=Thrd_Show_Bits(t, 5);
  code = (signed int)return_value_Thrd_Show_Bits$1;
  if(code < 31)
  {
    size = (signed int)DCchromtab0[(signed long int)code].val;
    Thrd_Flush_Buffer(t, (signed int)DCchromtab0[(signed long int)code].len);
  }

  else
  {
    unsigned int return_value_Thrd_Show_Bits$2;
    return_value_Thrd_Show_Bits$2=Thrd_Show_Bits(t, 10);
    code = (signed int)(return_value_Thrd_Show_Bits$2 - (unsigned int)992);
    size = (signed int)DCchromtab1[(signed long int)code].val;
    Thrd_Flush_Buffer(t, (signed int)DCchromtab1[(signed long int)code].len);
  }
  if(size == 0)
    dct_diff = 0;

  else
  {
    unsigned int return_value_Thrd_Get_Bits$3;
    return_value_Thrd_Get_Bits$3=Thrd_Get_Bits(t, size);
    dct_diff = (signed int)return_value_Thrd_Get_Bits$3;
    if((1 << -1 + size & dct_diff) == 0)
      dct_diff = dct_diff - ((1 << size) - 1);

  }
  return dct_diff;
}

// c::Thrd_Get_D_macroblock_type
// file src/getvlc.c line 965
static signed int Thrd_Get_D_macroblock_type(signed int t)
{
  unsigned int return_value_Thrd_Get_Bits1$1;
  return_value_Thrd_Get_Bits1$1=Thrd_Get_Bits1(t);
  if(return_value_Thrd_Get_Bits1$1 == 0u)
  {
    if(Quiet_Flag == 0)
      printf("Invalid macroblock_type code\n");

    Fault_Flag = 1;
  }

  return 1;
}

// c::Thrd_Get_I_macroblock_type
// file src/getvlc.c line 895
static signed int Thrd_Get_I_macroblock_type(signed int t)
{
  unsigned int return_value_Thrd_Get_Bits1$1;
  return_value_Thrd_Get_Bits1$1=Thrd_Get_Bits1(t);
  if(!(return_value_Thrd_Get_Bits1$1 == 0u))
    return 1;

  unsigned int return_value_Thrd_Get_Bits1$2;
  return_value_Thrd_Get_Bits1$2=Thrd_Get_Bits1(t);
  if(return_value_Thrd_Get_Bits1$2 == 0u)
  {
    if(Quiet_Flag == 0)
      printf("Invalid macroblock_type code\n");

    Fault_Flag = 1;
  }

  return 17;
}

// c::Thrd_Get_Long
// file src/systems.c line 297
signed int Thrd_Get_Long(signed int t)
{
  signed int i;
  i=Thrd_Get_Word(t);
  signed int return_value_Thrd_Get_Word$1;
  return_value_Thrd_Get_Word$1=Thrd_Get_Word(t);
  return i << 16 | return_value_Thrd_Get_Word$1;
}

// c::Thrd_Get_Luma_DC_dct_diff
// file src/global.h line 209
signed int Thrd_Get_Luma_DC_dct_diff(signed int t)
{
  signed int code;
  signed int size;
  signed int dct_diff;
  unsigned int return_value_Thrd_Show_Bits$1;
  return_value_Thrd_Show_Bits$1=Thrd_Show_Bits(t, 5);
  code = (signed int)return_value_Thrd_Show_Bits$1;
  if(code < 31)
  {
    size = (signed int)DClumtab0[(signed long int)code].val;
    Thrd_Flush_Buffer(t, (signed int)DClumtab0[(signed long int)code].len);
  }

  else
  {
    unsigned int return_value_Thrd_Show_Bits$2;
    return_value_Thrd_Show_Bits$2=Thrd_Show_Bits(t, 9);
    code = (signed int)(return_value_Thrd_Show_Bits$2 - (unsigned int)496);
    size = (signed int)DClumtab1[(signed long int)code].val;
    Thrd_Flush_Buffer(t, (signed int)DClumtab1[(signed long int)code].len);
  }
  if(size == 0)
    dct_diff = 0;

  else
  {
    unsigned int return_value_Thrd_Get_Bits$3;
    return_value_Thrd_Get_Bits$3=Thrd_Get_Bits(t, size);
    dct_diff = (signed int)return_value_Thrd_Get_Bits$3;
    if((1 << -1 + size & dct_diff) == 0)
      dct_diff = dct_diff - ((1 << size) - 1);

  }
  return dct_diff;
}

// c::Thrd_Get_P_macroblock_type
// file src/getvlc.c line 913
static signed int Thrd_Get_P_macroblock_type(signed int t)
{
  signed int code;
  unsigned int return_value_Thrd_Show_Bits$1;
  return_value_Thrd_Show_Bits$1=Thrd_Show_Bits(t, 6);
  code = (signed int)return_value_Thrd_Show_Bits$1;
  if(code >= 8)
  {
    code = code >> 3;
    Thrd_Flush_Buffer(t, (signed int)PMBtab0[(signed long int)code].len);
    return (signed int)PMBtab0[(signed long int)code].val;
  }

  if(code == 0)
  {
    if(Quiet_Flag == 0)
      printf("Invalid macroblock_type code\n");

    Fault_Flag = 1;
    return 0;
  }

  Thrd_Flush_Buffer(t, (signed int)PMBtab1[(signed long int)code].len);
  return (signed int)PMBtab1[(signed long int)code].val;
}

// c::Thrd_Get_Word
// file src/getbits.c line 277
signed int Thrd_Get_Word(signed int t)
{
  signed int Val;
  Val=Thrd_Get_Byte(t);
  signed int return_value_Thrd_Get_Byte$1;
  return_value_Thrd_Get_Byte$1=Thrd_Get_Byte(t);
  return Val << 8 | return_value_Thrd_Get_Byte$1;
}

// c::Thrd_Get_coded_block_pattern
// file src/global.h line 211
signed int Thrd_Get_coded_block_pattern(signed int t)
{
  signed int code;
  unsigned int return_value_Thrd_Show_Bits$1;
  return_value_Thrd_Show_Bits$1=Thrd_Show_Bits(t, 9);
  code = (signed int)return_value_Thrd_Show_Bits$1;
  if(code >= 128)
  {
    code = code >> 4;
    Thrd_Flush_Buffer(t, (signed int)CBPtab0[(signed long int)code].len);
    return (signed int)CBPtab0[(signed long int)code].val;
  }

  if(code >= 8)
  {
    code = code >> 1;
    Thrd_Flush_Buffer(t, (signed int)CBPtab1[(signed long int)code].len);
    return (signed int)CBPtab1[(signed long int)code].val;
  }

  if(code < 1)
  {
    if(Quiet_Flag == 0)
      printf("Invalid coded_block_pattern code\n");

    Fault_Flag = 1;
    return 0;
  }

  Thrd_Flush_Buffer(t, (signed int)CBPtab2[(signed long int)code].len);
  return (signed int)CBPtab2[(signed long int)code].val;
}

// c::Thrd_Get_dmvector
// file src/getvlc.c line 1073
signed int Thrd_Get_dmvector(signed int t)
{
  unsigned int return_value_Thrd_Get_Bits$2;
  return_value_Thrd_Get_Bits$2=Thrd_Get_Bits(t, 1);
  if(!(return_value_Thrd_Get_Bits$2 == 0u))
  {
    unsigned int return_value_Thrd_Get_Bits$1;
    return_value_Thrd_Get_Bits$1=Thrd_Get_Bits(t, 1);
    return return_value_Thrd_Get_Bits$1 != 0u ? -1 : 1;
  }

  else
    return 0;
}

// c::Thrd_Get_macroblock_address_increment
// file src/global.h line 215
signed int Thrd_Get_macroblock_address_increment(signed int t)
{
  signed int code;
  signed int val = 0;
  unsigned int return_value_Thrd_Show_Bits$1;
  do
  {
    return_value_Thrd_Show_Bits$1=Thrd_Show_Bits(t, 11);
    code = (signed int)return_value_Thrd_Show_Bits$1;
    if(!(code < 24))
      goto __CPROVER_DUMP_L5;

    if(!(code == 15))
    {
      if(code == 8)
        val = val + 33;

      else
      {
        if(Quiet_Flag == 0)
          printf("Invalid macroblock_address_increment code\n");

        Fault_Flag = 1;
        return 1;
      }
    }

    Thrd_Flush_Buffer(t, 11);
  }
  while(TRUE);

__CPROVER_DUMP_L5:
  ;
  if(code >= 1024)
  {
    Thrd_Flush_Buffer(t, 1);
    return val + 1;
  }

  if(code >= 128)
  {
    code = code >> 6;
    Thrd_Flush_Buffer(t, (signed int)MBAtab1[(signed long int)code].len);
    return val + (signed int)MBAtab1[(signed long int)code].val;
  }

  code = code - 24;
  Thrd_Flush_Buffer(t, (signed int)MBAtab2[(signed long int)code].len);
  return val + (signed int)MBAtab2[(signed long int)code].val;
}

// c::Thrd_Get_macroblock_type
// file src/global.h line 208
signed int Thrd_Get_macroblock_type(signed int t)
{
  signed int macroblock_type = 0;
  _Bool tmp_if_expr$1;
  if(ld->scalable_mode == 3)
    tmp_if_expr$1 = TRUE;

  else
    tmp_if_expr$1 = ld->pict_scal != 0 ? TRUE : FALSE;
  if(tmp_if_expr$1)
  {
    printf("not supported macroblock type");
    exit(-1);
  }

  switch(picture_coding_type)
  {

    case 1:
      {
        macroblock_type=Thrd_Get_I_macroblock_type(t);
        goto __CPROVER_DUMP_L9;
      }
    case 2:
      {
        macroblock_type=Thrd_Get_P_macroblock_type(t);
        goto __CPROVER_DUMP_L9;
      }
    case 3:
      {
        macroblock_type=Thrd_Get_B_macroblock_type(t);
        goto __CPROVER_DUMP_L9;
      }
    case 4:
      {
        macroblock_type=Thrd_Get_D_macroblock_type(t);
        goto __CPROVER_DUMP_L9;
      }
    default:
      printf("Get_macroblock_type(): unrecognized picture coding type\n");
  }

__CPROVER_DUMP_L9:
  ;
  return macroblock_type;
}

// c::Thrd_Get_motion_code
// file src/getvlc.c line 1032
signed int Thrd_Get_motion_code(signed int t)
{
  signed int code;
  unsigned int return_value_Thrd_Get_Bits1$1;
  return_value_Thrd_Get_Bits1$1=Thrd_Get_Bits1(t);
  if(!(return_value_Thrd_Get_Bits1$1 == 0u))
    return 0;

  unsigned int return_value_Thrd_Show_Bits$4;
  return_value_Thrd_Show_Bits$4=Thrd_Show_Bits(t, 9);
  code = (signed int)return_value_Thrd_Show_Bits$4;
  signed int tmp_if_expr$3;
  if(code >= 64)
  {
    code = code >> 6;
    Thrd_Flush_Buffer(t, (signed int)MVtab0[(signed long int)code].len);
    unsigned int return_value_Thrd_Get_Bits1$2;
    return_value_Thrd_Get_Bits1$2=Thrd_Get_Bits1(t);
    if(!(return_value_Thrd_Get_Bits1$2 == 0u))
      tmp_if_expr$3 = -((signed int)MVtab0[(signed long int)code].val);

    else
      tmp_if_expr$3 = (signed int)MVtab0[(signed long int)code].val;
    return tmp_if_expr$3;
  }

  signed int tmp_if_expr$6;
  if(code >= 24)
  {
    code = code >> 3;
    Thrd_Flush_Buffer(t, (signed int)MVtab1[(signed long int)code].len);
    unsigned int return_value_Thrd_Get_Bits1$5;
    return_value_Thrd_Get_Bits1$5=Thrd_Get_Bits1(t);
    if(!(return_value_Thrd_Get_Bits1$5 == 0u))
      tmp_if_expr$6 = -((signed int)MVtab1[(signed long int)code].val);

    else
      tmp_if_expr$6 = (signed int)MVtab1[(signed long int)code].val;
    return tmp_if_expr$6;
  }

  code = code - 12;
  if(code < 0)
  {
    if(Quiet_Flag == 0)
      printf("Invalid motion_vector code (MBA %d, pic %d)\n", global_MBA, global_pic);

    Fault_Flag = 1;
    return 0;
  }

  Thrd_Flush_Buffer(t, (signed int)MVtab2[(signed long int)code].len);
  unsigned int return_value_Thrd_Get_Bits1$7;
  return_value_Thrd_Get_Bits1$7=Thrd_Get_Bits1(t);
  signed int tmp_if_expr$8;
  if(!(return_value_Thrd_Get_Bits1$7 == 0u))
    tmp_if_expr$8 = -((signed int)MVtab2[(signed long int)code].val);

  else
    tmp_if_expr$8 = (signed int)MVtab2[(signed long int)code].val;
  return tmp_if_expr$8;
}

// c::Thrd_Initialize_Buffer
// file src/getbits.c line 261
void Thrd_Initialize_Buffer(signed int t)
{
  thrd_buf[(signed long int)t] = (unsigned int)0;
  Thrd_Flush_Buffer(t, 0);
}

// c::Thrd_Show_Bits
// file src/getbits.c line 288
unsigned int Thrd_Show_Bits(signed int t, signed int N)
{
  return thrd_buf[(signed long int)t] >> 32 - N;
}

// c::Thrd_Work
// file src/getpic.c line 1459
void * Thrd_Work(void *thrd_args)
{
  struct anon$2 *mydata = (struct anon$2 *)thrd_args;
  signed int id = mydata->id;
  signed int num_slices = mydata->num_slices;
  signed int MBAmax = mydata->MBAmax;
  signed int MBA;
  signed int MBAinc;
  signed int macroblock_type;
  signed int motion_type;
  signed int dct_type;
  signed int dc_dct_pred[3l];
  signed int PMV[2l][2l][2l];
  signed int motion_vertical_field_select[2l][2l];
  signed int dmvector[2l];
  signed int stwtype;
  signed int stwclass;
  signed int SNRMBA;
  signed int SNRMBAinc;
  signed int localMBA;
  signed int localMBAmax;
  signed int ret;
  MBA = 0;
  MBAinc = 0;
  localMBA = 0;
  localMBAmax = num_slices * mb_width;
  unsigned int return_value_Thrd_Show_Bits$1;
  do
  {

  next_slice:
    ;
    ret=Thrd_start_of_slice(id, MBAmax, &MBA, &MBAinc, dc_dct_pred, PMV);
    if(!(ret == 1))
    {
      if(localMBA >= localMBAmax)
        return NULL;

    }

    if(!(Two_Streams == 0))
    {
      if(enhan.scalable_mode == 3)
      {
        SNRMBA = 0;
        SNRMBAinc = 0;
      }

    }

    Fault_Flag = 0;

  __CPROVER_DUMP_L5:
    ;
    if(localMBA >= localMBAmax)
      return NULL;

    ld = &base;
    if(!(MBAinc == 0))
      goto __CPROVER_DUMP_L14;

    if(base.scalable_mode == 1)
    {
      if(base.priority_breakpoint == 1)
        ld = &enhan;

    }

    return_value_Thrd_Show_Bits$1=Thrd_Show_Bits(id, 23);
    if(!(return_value_Thrd_Show_Bits$1 == 0u) && Fault_Flag == 0)
      goto __CPROVER_DUMP_L11;


  resync:
    ;
    Fault_Flag = 0;
  }
  while(TRUE);
  return NULL;
  goto __CPROVER_DUMP_L13;

__CPROVER_DUMP_L11:
  ;
  if(base.scalable_mode == 1)
  {
    if(base.priority_breakpoint == 1)
      ld = &enhan;

  }

  MBAinc=Thrd_Get_macroblock_address_increment(id);
  if(Fault_Flag != 0)
    goto resync;


__CPROVER_DUMP_L13:
  ;

__CPROVER_DUMP_L14:
  ;
  if(MBA >= MBAmax)
  {
    if(Quiet_Flag == 0)
      printf("Too many macroblocks in picture\n");

    return NULL;
  }

  if(MBAinc == 1)
  {
    ret=Thrd_decode_macroblock(id, &macroblock_type, &stwtype, &stwclass, &motion_type, &dct_type, PMV, dc_dct_pred, motion_vertical_field_select, dmvector);
    if(ret == -1)
      return NULL;

    if(ret == 0)
      goto resync;

  }

  else
    Thrd_skipped_macroblock(id, dc_dct_pred, PMV, &motion_type, motion_vertical_field_select, &stwtype, &macroblock_type);
  if(!(Two_Streams == 0))
  {
    if(enhan.scalable_mode == 3)
      Decode_SNR_Macroblock(&SNRMBA, &SNRMBAinc, MBA, MBAmax, &dct_type);

  }

  Thrd_motion_compensation(id, MBA, macroblock_type, motion_type, PMV, motion_vertical_field_select, dmvector, stwtype, dct_type);
  localMBA = localMBA + 1;
  MBA = MBA + 1;
  MBAinc = MBAinc - 1;
  if(!(Two_Streams == 0))
  {
    if(enhan.scalable_mode == 3)
    {
      SNRMBA = SNRMBA + 1;
      SNRMBAinc = SNRMBAinc - 1;
    }

  }

  if(localMBA >= localMBAmax)
    return NULL;

  goto __CPROVER_DUMP_L5;
  return NULL;
}

// c::Thrd_decode_macroblock
// file src/getpic.c line 1833
static signed int Thrd_decode_macroblock(signed int t, signed int *macroblock_type, signed int *stwtype, signed int *stwclass, signed int *motion_type, signed int *dct_type, signed int (*PMV)[2l][2l], signed int *dc_dct_pred, signed int (*motion_vertical_field_select)[2l], signed int *dmvector)
{
  signed int quantizer_scale_code;
  signed int comp;
  signed int motion_vector_count;
  signed int mv_format;
  signed int dmv;
  signed int mvscale;
  signed int coded_block_pattern;
  if(base.scalable_mode == 1)
  {
    if(base.priority_breakpoint <= 2)
      ld = &enhan;

    else
      ld = &base;
  }

  Thrd_macroblock_modes(t, macroblock_type, stwtype, stwclass, motion_type, &motion_vector_count, &mv_format, &dmv, &mvscale, dct_type);
  if(!(Fault_Flag == 0))
    return 0;

  signed int tmp_if_expr$2;
  if(!((16 & *macroblock_type) == 0))
  {
    unsigned int return_value_Thrd_Get_Bits$1;
    return_value_Thrd_Get_Bits$1=Thrd_Get_Bits(t, 5);
    quantizer_scale_code = (signed int)return_value_Thrd_Get_Bits$1;
    if(!(ld->MPEG2_Flag == 0))
    {
      if(!(ld->q_scale_type == 0))
        tmp_if_expr$2 = (signed int)Non_Linear_quantizer_scale[(signed long int)quantizer_scale_code];

      else
        tmp_if_expr$2 = quantizer_scale_code << 1;
      thrd_ld[(signed long int)t].quantizer_scale = tmp_if_expr$2;
    }

    else
      thrd_ld[(signed long int)t].quantizer_scale = quantizer_scale_code;
    if(base.scalable_mode == 1)
    {
      printf("DP exiting\n");
      exit(-1);
      base.quantizer_scale = ld->quantizer_scale;
    }

  }

  _Bool tmp_if_expr$3;
  if(!((8 & *macroblock_type) == 0))
    tmp_if_expr$3 = TRUE;

  else
    tmp_if_expr$3 = ((*macroblock_type & 1) != 0 ? (concealment_motion_vectors != 0 ? TRUE : FALSE) : FALSE) ? TRUE : FALSE;
  if(tmp_if_expr$3)
  {
    if(!(ld->MPEG2_Flag == 0))
      Thrd_motion_vectors(t, PMV, dmvector, motion_vertical_field_select, 0, motion_vector_count, mv_format, f_code[(signed long int)0][(signed long int)0] - 1, f_code[(signed long int)0][(signed long int)1] - 1, dmv, mvscale);

    else
      Thrd_motion_vector(t, PMV[(signed long int)0][(signed long int)0], dmvector, forward_f_code - 1, forward_f_code - 1, 0, 0, full_pel_forward_vector);
  }

  if(!(Fault_Flag == 0))
    return 0;

  if(!((4 & *macroblock_type) == 0))
  {
    if(!(ld->MPEG2_Flag == 0))
      Thrd_motion_vectors(t, PMV, dmvector, motion_vertical_field_select, 1, motion_vector_count, mv_format, f_code[(signed long int)1][(signed long int)0] - 1, f_code[(signed long int)1][(signed long int)1] - 1, 0, mvscale);

    else
      Thrd_motion_vector(t, PMV[(signed long int)0][(signed long int)1], dmvector, backward_f_code - 1, backward_f_code - 1, 0, 0, full_pel_backward_vector);
  }

  if(!(Fault_Flag == 0))
    return 0;

  if(!((1 & *macroblock_type) == 0))
  {
    if(!(concealment_motion_vectors == 0))
      Thrd_Flush_Buffer(t, 1);

  }

  if(base.scalable_mode == 1)
  {
    if(base.priority_breakpoint == 3)
    {
      printf("enhan not supported, exiting...\n");
      exit(-1);
      ld = &enhan;
    }

  }

  if(!((2 & *macroblock_type) == 0))
  {
    coded_block_pattern=Thrd_Get_coded_block_pattern(t);
    if(chroma_format == 2)
    {
      unsigned int return_value_Thrd_Get_Bits$4;
      return_value_Thrd_Get_Bits$4=Thrd_Get_Bits(t, 2);
      coded_block_pattern = (signed int)((unsigned int)(coded_block_pattern << 2) | return_value_Thrd_Get_Bits$4);
    }

    else
      if(chroma_format == 3)
      {
        unsigned int return_value_Thrd_Get_Bits$5;
        return_value_Thrd_Get_Bits$5=Thrd_Get_Bits(t, 6);
        coded_block_pattern = (signed int)((unsigned int)(coded_block_pattern << 6) | return_value_Thrd_Get_Bits$5);
      }

  }

  else
    coded_block_pattern = (*macroblock_type & 1) != 0 ? (1 << block_count) - 1 : 0;
  if(!(Fault_Flag == 0))
    return 0;

  comp = 0;
  while(!(comp >= block_count))
  {
    if(base.scalable_mode == 1)
      ld = &base;

    Thrd_Clear_Block(t, comp);
    if(!((1 << -1 + block_count + -comp & coded_block_pattern) == 0))
    {
      if(!((1 & *macroblock_type) == 0))
      {
        if(!(ld->MPEG2_Flag == 0))
          Thrd_Decode_MPEG2_Intra_Block(t, comp, dc_dct_pred);

        else
        {
          printf("not mpeg2, exiting...\n");
          exit(-1);
          Decode_MPEG1_Intra_Block(comp, dc_dct_pred);
        }
      }

      else
        if(!(ld->MPEG2_Flag == 0))
          Thrd_Decode_MPEG2_Non_Intra_Block(t, comp);

        else
        {
          printf("not mpeg2, exiting...\n");
          exit(-1);
          Decode_MPEG1_Non_Intra_Block(comp);
        }
      if(!(Fault_Flag == 0))
        return 0;

    }

    comp = comp + 1;
  }
  if(picture_coding_type == 4)
    Thrd_Get_Bits(t, 1);

  if((1 & *macroblock_type) == 0)
  {
    dc_dct_pred[(signed long int)2] = 0;
    dc_dct_pred[(signed long int)1] = dc_dct_pred[(signed long int)2];
    dc_dct_pred[(signed long int)0] = dc_dct_pred[(signed long int)1];
  }

  if(!((1 & *macroblock_type) == 0))
  {
    if(concealment_motion_vectors == 0)
    {
      PMV[(signed long int)1][(signed long int)0][(signed long int)1] = 0;
      PMV[(signed long int)1][(signed long int)0][(signed long int)0] = PMV[(signed long int)1][(signed long int)0][(signed long int)1];
      PMV[(signed long int)0][(signed long int)0][(signed long int)1] = PMV[(signed long int)1][(signed long int)0][(signed long int)0];
      PMV[(signed long int)0][(signed long int)0][(signed long int)0] = PMV[(signed long int)0][(signed long int)0][(signed long int)1];
      PMV[(signed long int)1][(signed long int)1][(signed long int)1] = 0;
      PMV[(signed long int)1][(signed long int)1][(signed long int)0] = PMV[(signed long int)1][(signed long int)1][(signed long int)1];
      PMV[(signed long int)0][(signed long int)1][(signed long int)1] = PMV[(signed long int)1][(signed long int)1][(signed long int)0];
      PMV[(signed long int)0][(signed long int)1][(signed long int)0] = PMV[(signed long int)0][(signed long int)1][(signed long int)1];
    }

  }

  if(picture_coding_type == 2)
  {
    if((9 & *macroblock_type) == 0)
    {
      PMV[(signed long int)1][(signed long int)0][(signed long int)1] = 0;
      PMV[(signed long int)1][(signed long int)0][(signed long int)0] = PMV[(signed long int)1][(signed long int)0][(signed long int)1];
      PMV[(signed long int)0][(signed long int)0][(signed long int)1] = PMV[(signed long int)1][(signed long int)0][(signed long int)0];
      PMV[(signed long int)0][(signed long int)0][(signed long int)0] = PMV[(signed long int)0][(signed long int)0][(signed long int)1];
      if(picture_structure == 3)
        *motion_type = 2;

      else
      {
        *motion_type = 1;
        motion_vertical_field_select[(signed long int)0][(signed long int)0] = (signed int)(picture_structure == 2);
      }
    }

  }

  if(*stwclass == 4)
  {
    PMV[(signed long int)1][(signed long int)0][(signed long int)1] = 0;
    PMV[(signed long int)1][(signed long int)0][(signed long int)0] = PMV[(signed long int)1][(signed long int)0][(signed long int)1];
    PMV[(signed long int)0][(signed long int)0][(signed long int)1] = PMV[(signed long int)1][(signed long int)0][(signed long int)0];
    PMV[(signed long int)0][(signed long int)0][(signed long int)0] = PMV[(signed long int)0][(signed long int)0][(signed long int)1];
    PMV[(signed long int)1][(signed long int)1][(signed long int)1] = 0;
    PMV[(signed long int)1][(signed long int)1][(signed long int)0] = PMV[(signed long int)1][(signed long int)1][(signed long int)1];
    PMV[(signed long int)0][(signed long int)1][(signed long int)1] = PMV[(signed long int)1][(signed long int)1][(signed long int)0];
    PMV[(signed long int)0][(signed long int)1][(signed long int)0] = PMV[(signed long int)0][(signed long int)1][(signed long int)1];
  }

  return 1;
}

// c::Thrd_extra_bit_information
// file src/gethdr.c line 236
static signed int Thrd_extra_bit_information(signed int t)
{
  signed int Byte_Count = 0;
  unsigned int return_value_Thrd_Get_Bits1$1;
  do
  {
    return_value_Thrd_Get_Bits1$1=Thrd_Get_Bits1(t);
    if(return_value_Thrd_Get_Bits1$1 == 0u)
      goto __CPROVER_DUMP_L2;

    Thrd_Flush_Buffer(t, 8);
    Byte_Count = Byte_Count + 1;
  }
  while(TRUE);

__CPROVER_DUMP_L2:
  ;
  return Byte_Count;
}

// c::Thrd_macroblock_modes
// file src/getpic.c line 2162
static void Thrd_macroblock_modes(signed int t, signed int *pmacroblock_type, signed int *pstwtype, signed int *pstwclass, signed int *pmotion_type, signed int *pmotion_vector_count, signed int *pmv_format, signed int *pdmv, signed int *pmvscale, signed int *pdct_type)
{
  static unsigned char stwc_table[3l][4l] = { { (unsigned char)6, (unsigned char)3, (unsigned char)7, (unsigned char)4 }, 
    { (unsigned char)2, (unsigned char)1, (unsigned char)5, (unsigned char)4 }, 
    { (unsigned char)2, (unsigned char)5, (unsigned char)7, (unsigned char)4 } };
  static unsigned char stwclass_table[9l] = { (unsigned char)0, (unsigned char)1, (unsigned char)2, (unsigned char)1, (unsigned char)1, (unsigned char)2, (unsigned char)3, (unsigned char)3, (unsigned char)4 };
  signed int macroblock_type;
  signed int stwtype;
  signed int stwcode;
  signed int stwclass;
  signed int motion_type = 0;
  signed int motion_vector_count;
  signed int mv_format;
  signed int dmv;
  signed int mvscale;
  signed int dct_type;
  macroblock_type=Thrd_Get_macroblock_type(t);
  if(!(Fault_Flag == 0))
    return;

  if(!((32 & macroblock_type) == 0))
  {
    if(spatial_temporal_weight_code_table_index == 0)
      stwtype = 4;

    else
    {
      unsigned int return_value_Thrd_Get_Bits$1;
      return_value_Thrd_Get_Bits$1=Thrd_Get_Bits(t, 2);
      stwcode = (signed int)return_value_Thrd_Get_Bits$1;
      stwtype = (signed int)stwc_table[(signed long int)(spatial_temporal_weight_code_table_index - 1)][(signed long int)stwcode];
    }
  }

  else
    stwtype = (macroblock_type & 64) != 0 ? 8 : 0;
  stwclass = (signed int)stwclass_table[(signed long int)stwtype];
  unsigned int tmp_if_expr$3;
  unsigned int return_value_Thrd_Get_Bits$2;
  if(!((12 & macroblock_type) == 0))
  {
    if(picture_structure == 3)
    {
      if(!(frame_pred_frame_dct == 0))
        tmp_if_expr$3 = (unsigned int)2;

      else
      {
        return_value_Thrd_Get_Bits$2=Thrd_Get_Bits(t, 2);
        tmp_if_expr$3 = return_value_Thrd_Get_Bits$2;
      }
      motion_type = (signed int)tmp_if_expr$3;
    }

    else
    {
      unsigned int return_value_Thrd_Get_Bits$4;
      return_value_Thrd_Get_Bits$4=Thrd_Get_Bits(t, 2);
      motion_type = (signed int)return_value_Thrd_Get_Bits$4;
    }
  }

  else
    if(!((1 & macroblock_type) == 0))
    {
      if(!(concealment_motion_vectors == 0))
        motion_type = picture_structure == 3 ? 2 : 1;

    }

  if(picture_structure == 3)
  {
    motion_vector_count = motion_type == 1 && stwclass < 2 ? 2 : 1;
    mv_format = motion_type == 2 ? 1 : 0;
  }

  else
  {
    motion_vector_count = motion_type == 2 ? 2 : 1;
    mv_format = 0;
  }
  dmv = (signed int)(motion_type == 3);
  mvscale = (signed int)(mv_format == 0 && picture_structure == 3);
  unsigned int tmp_if_expr$6;
  unsigned int return_value_Thrd_Get_Bits$5;
  if(picture_structure == 3)
  {
    if(frame_pred_frame_dct != 0)
      goto __CPROVER_DUMP_L14;

    if((3 & macroblock_type) == 0)
      goto __CPROVER_DUMP_L14;

    return_value_Thrd_Get_Bits$5=Thrd_Get_Bits(t, 1);
    tmp_if_expr$6 = return_value_Thrd_Get_Bits$5;
  }

  else
  {

  __CPROVER_DUMP_L14:
    ;
    tmp_if_expr$6 = (unsigned int)0;
  }
  dct_type = (signed int)tmp_if_expr$6;
  *pmacroblock_type = macroblock_type;
  *pstwtype = stwtype;
  *pstwclass = stwclass;
  *pmotion_type = motion_type;
  *pmotion_vector_count = motion_vector_count;
  *pmv_format = mv_format;
  *pdmv = dmv;
  *pmvscale = mvscale;
  *pdct_type = dct_type;
}

// c::Thrd_motion_compensation
// file src/getpic.c line 2103
static void Thrd_motion_compensation(signed int t, signed int MBA, signed int macroblock_type, signed int motion_type, signed int (*PMV)[2l][2l], signed int (*motion_vertical_field_select)[2l], signed int *dmvector, signed int stwtype, signed int dct_type)
{
  signed int bx;
  signed int by;
  signed int comp;
  bx = 16 * (MBA % mb_width);
  by = 16 * (MBA / mb_width);
  if((1 & macroblock_type) == 0)
    form_predictions(bx, by, macroblock_type, motion_type, PMV, motion_vertical_field_select, dmvector, stwtype);

  if(base.scalable_mode == 1)
    ld = &base;

  comp = 0;
  _Bool tmp_if_expr$1;
  while(!(comp >= block_count))
  {
    if(!(Two_Streams == 0))
    {
      if(enhan.scalable_mode == 3)
      {
        printf("two streams and sc_snr not supported, exiting...\n");
        exit(-1);
        Sum_Block(comp);
      }

    }

    if(!(Two_Streams == 0))
    {
      if(!(enhan.scalable_mode == 3))
        goto __CPROVER_DUMP_L5;

      tmp_if_expr$1 = TRUE;
    }

    else
    {

    __CPROVER_DUMP_L5:
      ;
      tmp_if_expr$1 = ld->MPEG2_Flag != 0 ? TRUE : FALSE;
    }
    if(tmp_if_expr$1)
      Saturate(thrd_ld[(signed long int)t].block[(signed long int)comp]);

    if(!(Reference_IDCT_Flag == 0))
      Reference_IDCT(thrd_ld[(signed long int)t].block[(signed long int)comp]);

    else
      Fast_IDCT(thrd_ld[(signed long int)t].block[(signed long int)comp]);
    Thrd_Add_Block(t, comp, bx, by, dct_type, (signed int)((macroblock_type & 1) == 0));
    comp = comp + 1;
  }
}

// c::Thrd_motion_vector
// file src/global.h line 176
void Thrd_motion_vector(signed int t, signed int *PMV, signed int *dmvector, signed int h_r_size, signed int v_r_size, signed int dmv, signed int mvscale, signed int full_pel_vector)
{
  signed int motion_code;
  signed int motion_residual;
  motion_code=Thrd_Get_motion_code(t);
  unsigned int tmp_if_expr$2;
  unsigned int return_value_Thrd_Get_Bits$1;
  if(!(h_r_size == 0))
  {
    if(motion_code == 0)
      goto __CPROVER_DUMP_L1;

    return_value_Thrd_Get_Bits$1=Thrd_Get_Bits(t, h_r_size);
    tmp_if_expr$2 = return_value_Thrd_Get_Bits$1;
  }

  else
  {

  __CPROVER_DUMP_L1:
    ;
    tmp_if_expr$2 = (unsigned int)0;
  }
  motion_residual = (signed int)tmp_if_expr$2;
  decode_motion_vector(&PMV[(signed long int)0], h_r_size, motion_code, motion_residual, full_pel_vector);
  if(!(dmv == 0))
    dmvector[(signed long int)0]=Thrd_Get_dmvector(t);

  motion_code=Thrd_Get_motion_code(t);
  unsigned int tmp_if_expr$4;
  unsigned int return_value_Thrd_Get_Bits$3;
  if(!(v_r_size == 0))
  {
    if(motion_code == 0)
      goto __CPROVER_DUMP_L4;

    return_value_Thrd_Get_Bits$3=Thrd_Get_Bits(t, v_r_size);
    tmp_if_expr$4 = return_value_Thrd_Get_Bits$3;
  }

  else
  {

  __CPROVER_DUMP_L4:
    ;
    tmp_if_expr$4 = (unsigned int)0;
  }
  motion_residual = (signed int)tmp_if_expr$4;
  if(!(mvscale == 0))
    PMV[(signed long int)1] = PMV[(signed long int)1] >> 1;

  decode_motion_vector(&PMV[(signed long int)1], v_r_size, motion_code, motion_residual, full_pel_vector);
  if(!(mvscale == 0))
    PMV[(signed long int)1] = PMV[(signed long int)1] << 1;

  if(!(dmv == 0))
    dmvector[(signed long int)1]=Thrd_Get_dmvector(t);

}

// c::Thrd_motion_vectors
// file src/global.h line 173
void Thrd_motion_vectors(signed int t, signed int (*PMV)[2l][2l], signed int *dmvector, signed int (*motion_vertical_field_select)[2l], signed int s, signed int motion_vector_count, signed int mv_format, signed int h_r_size, signed int v_r_size, signed int dmv, signed int mvscale)
{
  if(motion_vector_count == 1)
  {
    if(mv_format == 0)
    {
      if(dmv == 0)
      {
        unsigned int return_value_Thrd_Get_Bits$1;
        return_value_Thrd_Get_Bits$1=Thrd_Get_Bits(t, 1);
        motion_vertical_field_select[(signed long int)0][(signed long int)s] = (signed int)return_value_Thrd_Get_Bits$1;
        motion_vertical_field_select[(signed long int)1][(signed long int)s] = motion_vertical_field_select[(signed long int)0][(signed long int)s];
      }

    }

    Thrd_motion_vector(t, PMV[(signed long int)0][(signed long int)s], dmvector, h_r_size, v_r_size, dmv, mvscale, 0);
    PMV[(signed long int)1][(signed long int)s][(signed long int)0] = PMV[(signed long int)0][(signed long int)s][(signed long int)0];
    PMV[(signed long int)1][(signed long int)s][(signed long int)1] = PMV[(signed long int)0][(signed long int)s][(signed long int)1];
  }

  else
  {
    unsigned int return_value_Thrd_Get_Bits$2;
    return_value_Thrd_Get_Bits$2=Thrd_Get_Bits(t, 1);
    motion_vertical_field_select[(signed long int)0][(signed long int)s] = (signed int)return_value_Thrd_Get_Bits$2;
    Thrd_motion_vector(t, PMV[(signed long int)0][(signed long int)s], dmvector, h_r_size, v_r_size, dmv, mvscale, 0);
    unsigned int return_value_Thrd_Get_Bits$3;
    return_value_Thrd_Get_Bits$3=Thrd_Get_Bits(t, 1);
    motion_vertical_field_select[(signed long int)1][(signed long int)s] = (signed int)return_value_Thrd_Get_Bits$3;
    Thrd_motion_vector(t, PMV[(signed long int)1][(signed long int)s], dmvector, h_r_size, v_r_size, dmv, mvscale, 0);
  }
}

// c::Thrd_next_start_code
// file src/gethdr.c line 190
void Thrd_next_start_code(signed int t)
{
  Thrd_Flush_Buffer(t, thrd_Incnt[(signed long int)t] & 7);
  unsigned int return_value_Thrd_Show_Bits$1;
  do
  {
    return_value_Thrd_Show_Bits$1=Thrd_Show_Bits(t, 24);
    if((signed long int)return_value_Thrd_Show_Bits$1 == 1l)
      goto __CPROVER_DUMP_L2;

    Thrd_Flush_Buffer(t, 8);
  }
  while(TRUE);

__CPROVER_DUMP_L2:
  ;
}

// c::Thrd_skipped_macroblock
// file src/getpic.c line 2051
static void Thrd_skipped_macroblock(signed int t, signed int *dc_dct_pred, signed int (*PMV)[2l][2l], signed int *motion_type, signed int (*motion_vertical_field_select)[2l], signed int *stwtype, signed int *macroblock_type)
{
  signed int comp;
  if(base.scalable_mode == 1)
    ld = &base;

  comp = 0;
  while(!(comp >= block_count))
  {
    Thrd_Clear_Block(t, comp);
    comp = comp + 1;
  }
  dc_dct_pred[(signed long int)2] = 0;
  dc_dct_pred[(signed long int)1] = dc_dct_pred[(signed long int)2];
  dc_dct_pred[(signed long int)0] = dc_dct_pred[(signed long int)1];
  if(picture_coding_type == 2)
  {
    PMV[(signed long int)1][(signed long int)0][(signed long int)1] = 0;
    PMV[(signed long int)1][(signed long int)0][(signed long int)0] = PMV[(signed long int)1][(signed long int)0][(signed long int)1];
    PMV[(signed long int)0][(signed long int)0][(signed long int)1] = PMV[(signed long int)1][(signed long int)0][(signed long int)0];
    PMV[(signed long int)0][(signed long int)0][(signed long int)0] = PMV[(signed long int)0][(signed long int)0][(signed long int)1];
  }

  if(picture_structure == 3)
    *motion_type = 2;

  else
  {
    *motion_type = 1;
    motion_vertical_field_select[(signed long int)0][(signed long int)1] = (signed int)(picture_structure == 2);
    motion_vertical_field_select[(signed long int)0][(signed long int)0] = motion_vertical_field_select[(signed long int)0][(signed long int)1];
  }
  *stwtype = picture_coding_type == 1 ? 8 : 0;
  *macroblock_type = *macroblock_type & ~1;
}

// c::Thrd_slice_header
// file src/gethdr.c line 198
signed int Thrd_slice_header(signed int t)
{
  signed int slice_vertical_position_extension;
  signed int quantizer_scale_code;
  signed int slice_picture_id_enable = 0;
  signed int slice_picture_id = 0;
  signed int extra_information_slice = 0;
  unsigned int tmp_if_expr$2;
  unsigned int return_value_Thrd_Get_Bits$1;
  if(vertical_size > 2800 && !(ld->MPEG2_Flag == 0))
  {
    return_value_Thrd_Get_Bits$1=Thrd_Get_Bits(t, 3);
    tmp_if_expr$2 = return_value_Thrd_Get_Bits$1;
  }

  else
    tmp_if_expr$2 = (unsigned int)0;
  slice_vertical_position_extension = (signed int)tmp_if_expr$2;
  if(ld->scalable_mode == 1)
  {
    printf("scalable_mode==SC_DP\n");
    exit(-1);
    unsigned int return_value_Get_Bits$3;
    return_value_Get_Bits$3=Get_Bits(7);
    ld->priority_breakpoint = (signed int)return_value_Get_Bits$3;
  }

  unsigned int return_value_Thrd_Get_Bits$4;
  return_value_Thrd_Get_Bits$4=Thrd_Get_Bits(t, 5);
  quantizer_scale_code = (signed int)return_value_Thrd_Get_Bits$4;
  signed int tmp_if_expr$6;
  signed int tmp_if_expr$5;
  if(!(ld->MPEG2_Flag == 0))
  {
    if(!(ld->q_scale_type == 0))
      tmp_if_expr$5 = (signed int)Non_Linear_quantizer_scale[(signed long int)quantizer_scale_code];

    else
      tmp_if_expr$5 = quantizer_scale_code << 1;
    tmp_if_expr$6 = tmp_if_expr$5;
  }

  else
    tmp_if_expr$6 = quantizer_scale_code;
  thrd_ld[(signed long int)t].quantizer_scale = tmp_if_expr$6;
  unsigned int return_value_Thrd_Get_Bits$10;
  return_value_Thrd_Get_Bits$10=Thrd_Get_Bits(t, 1);
  if(!(return_value_Thrd_Get_Bits$10 == 0u))
  {
    unsigned int return_value_Thrd_Get_Bits$7;
    return_value_Thrd_Get_Bits$7=Thrd_Get_Bits(t, 1);
    thrd_ld[(signed long int)t].intra_slice = (signed int)return_value_Thrd_Get_Bits$7;
    unsigned int return_value_Thrd_Get_Bits$8;
    return_value_Thrd_Get_Bits$8=Thrd_Get_Bits(t, 1);
    slice_picture_id_enable = (signed int)return_value_Thrd_Get_Bits$8;
    unsigned int return_value_Thrd_Get_Bits$9;
    return_value_Thrd_Get_Bits$9=Thrd_Get_Bits(t, 6);
    slice_picture_id = (signed int)return_value_Thrd_Get_Bits$9;
    extra_information_slice=Thrd_extra_bit_information(t);
  }

  else
    thrd_ld[(signed long int)t].intra_slice = 0;
  return slice_vertical_position_extension;
}

// c::Thrd_start_of_slice
// file src/getpic.c line 1769
static signed int Thrd_start_of_slice(signed int t, signed int MBAmax, signed int *MBA, signed int *MBAinc, signed int *dc_dct_pred, signed int (*PMV)[2l][2l])
{
  unsigned int code;
  signed int slice_vert_pos_ext;
  ld = &base;
  Fault_Flag = 0;
  Thrd_next_start_code(t);
  code=Thrd_Show_Bits(t, 32);
  if(!(code < 257u))
  {
    if(code > 431u)
      goto __CPROVER_DUMP_L2;

  }

  else
  {

  __CPROVER_DUMP_L2:
    ;
    if(Quiet_Flag == 0)
      printf("start_of_slice(): Premature end of picture\n");

    return -1;
  }
  Thrd_Flush_Buffer32(t);
  slice_vert_pos_ext=Thrd_slice_header(t);
  *MBAinc=Thrd_Get_macroblock_address_increment(t);
  if(!(Fault_Flag == 0))
  {
    printf("start_of_slice(): MBAinc unsuccessful\n");
    return 0;
  }

  *MBA = (signed int)(((((unsigned int)(slice_vert_pos_ext << 7) + (code & (unsigned int)255)) - (unsigned int)1) * (unsigned int)mb_width + (unsigned int)*MBAinc) - (unsigned int)1);
  *MBAinc = 1;
  dc_dct_pred[(signed long int)2] = 0;
  dc_dct_pred[(signed long int)1] = dc_dct_pred[(signed long int)2];
  dc_dct_pred[(signed long int)0] = dc_dct_pred[(signed long int)1];
  PMV[(signed long int)1][(signed long int)0][(signed long int)1] = 0;
  PMV[(signed long int)1][(signed long int)0][(signed long int)0] = PMV[(signed long int)1][(signed long int)0][(signed long int)1];
  PMV[(signed long int)0][(signed long int)0][(signed long int)1] = PMV[(signed long int)1][(signed long int)0][(signed long int)0];
  PMV[(signed long int)0][(signed long int)0][(signed long int)0] = PMV[(signed long int)0][(signed long int)0][(signed long int)1];
  PMV[(signed long int)1][(signed long int)1][(signed long int)1] = 0;
  PMV[(signed long int)1][(signed long int)1][(signed long int)0] = PMV[(signed long int)1][(signed long int)1][(signed long int)1];
  PMV[(signed long int)0][(signed long int)1][(signed long int)1] = PMV[(signed long int)1][(signed long int)1][(signed long int)0];
  PMV[(signed long int)0][(signed long int)1][(signed long int)0] = PMV[(signed long int)0][(signed long int)1][(signed long int)1];
  return 1;
}

// c::Update_Picture_Buffers
// file src/getpic.c line 897
static void Update_Picture_Buffers(void)
{
  signed int cc;
  unsigned char *tmp;
  cc = 0;
  while(cc < 3)
  {
    if(picture_coding_type == 3)
      current_frame[(signed long int)cc] = auxframe[(signed long int)cc];

    else
    {
      if(Second_Field == 0)
      {
        tmp = forward_reference_frame[(signed long int)cc];
        forward_reference_frame[(signed long int)cc] = backward_reference_frame[(signed long int)cc];
        backward_reference_frame[(signed long int)cc] = tmp;
      }

      current_frame[(signed long int)cc] = backward_reference_frame[(signed long int)cc];
    }
    if(picture_structure == 2)
      current_frame[(signed long int)cc] = current_frame[(signed long int)cc] + (signed long int)(cc == 0 ? Coded_Picture_Width : Chroma_Width);

    cc = cc + 1;
  }
}

// c::Update_Temporal_Reference_Tacking_Data
// file src/gethdr.c line 1160
static void Update_Temporal_Reference_Tacking_Data(void)
{
  static signed int temporal_reference_old = 0;
  static signed int temporal_reference_wrap = 0;
  if(ld == &base)
  {
    if(!(picture_coding_type == 3))
    {
      if(!(temporal_reference == temporal_reference_old))
      {
        if(!(temporal_reference_wrap == 0))
        {
          Temporal_Reference_Base = Temporal_Reference_Base + 1024;
          temporal_reference_wrap = 0;
        }

        if(!(temporal_reference >= temporal_reference_old))
        {
          if(Temporal_Reference_GOP_Reset == 0)
            temporal_reference_wrap = 1;

        }

        temporal_reference_old = temporal_reference;
        Temporal_Reference_GOP_Reset = 0;
      }

    }

    True_Framenum = Temporal_Reference_Base + temporal_reference;
    if(!(temporal_reference_wrap == 0))
    {
      if(temporal_reference_old >= temporal_reference)
        True_Framenum = True_Framenum + 1024;

    }

    True_Framenum_max = True_Framenum > True_Framenum_max ? True_Framenum : True_Framenum_max;
  }

}

// c::Write_Frame
// file src/global.h line 194
void Write_Frame(unsigned char **src, signed int frame)
{
  char outname[256l];
  if(progressive_sequence == 0)
  {
    if(progressive_frame != 0)
      goto __CPROVER_DUMP_L1;

    if(Frame_Store_Flag != 0)
      goto __CPROVER_DUMP_L1;

  }

  else
  {

  __CPROVER_DUMP_L1:
    ;
    sprintf(outname, Output_Picture_Filename, frame, 102);
    store_one(outname, src, 0, Coded_Picture_Width, vertical_size);
    goto __CPROVER_DUMP_L3;
  }
  sprintf(outname, Output_Picture_Filename, frame, 97);
  store_one(outname, src, 0, Coded_Picture_Width << 1, vertical_size >> 1);
  sprintf(outname, Output_Picture_Filename, frame, 98);
  store_one(outname, src, Coded_Picture_Width, Coded_Picture_Width << 1, vertical_size >> 1);

__CPROVER_DUMP_L3:
  ;
}

// c::__signbit
// file /usr/include/x86_64-linux-gnu/bits/mathinline.h line 139
signed int __signbit(double __x)
{
  signed int __m;
  asm("pmovmskb %1, %0");
  return (signed int)((__m & 128) != 0);
}

// c::__signbitf
// file /usr/include/x86_64-linux-gnu/bits/mathinline.h line 127
signed int __signbitf(float __x)
{
  signed int __m;
  asm("pmovmskb %1, %0");
  return (signed int)((__m & 8) != 0);
}

// c::__signbitl
// file /usr/include/x86_64-linux-gnu/bits/mathinline.h line 151
signed int __signbitl(long double __x)
{
  union anon$4 __u = (union anon$4){ .__l=__x };
  return (signed int)((__u.__i[(signed long int)2] & 32768) != 0);
}

// c::atof
// file /usr/include/x86_64-linux-gnu/bits/stdlib-float.h line 26
double atof(const char *__nptr)
{
  double return_value_strtod$1;
  return_value_strtod$1=strtod(__nptr, ((char **)NULL));
  return return_value_strtod$1;
}

// c::atoi
// file /usr/include/stdlib.h line 278
signed int atoi(const char *__nptr)
{
  signed long int return_value_strtol$1;
  return_value_strtol$1=strtol(__nptr, ((char **)NULL), 10);
  return (signed int)return_value_strtol$1;
}

// c::atol
// file /usr/include/stdlib.h line 283
signed long int atol(const char *__nptr)
{
  signed long int return_value_strtol$1;
  return_value_strtol$1=strtol(__nptr, ((char **)NULL), 10);
  return return_value_strtol$1;
}

// c::atoll
// file /usr/include/stdlib.h line 292
signed long long int atoll(const char *__nptr)
{
  signed long long int return_value_strtoll$1;
  return_value_strtoll$1=strtoll(__nptr, ((char **)NULL), 10);
  return return_value_strtoll$1;
}

// c::confstr
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 240
unsigned long int confstr(signed int __name, char *__buf, unsigned long int __len)
{
  unsigned long int return_value___confstr_chk$1;
  unsigned long int return_value___confstr_chk_warn$2;
  unsigned long int return_value___confstr_alias$3;
  return_value___confstr_alias$3=__confstr_alias(__name, __buf, __len);
  return return_value___confstr_alias$3;
}

// c::conv420to422
// file src/store.c line 579
static void conv420to422(unsigned char *src, unsigned char *dst)
{
  signed int w;
  signed int h;
  signed int i;
  signed int j;
  signed int j2;
  signed int jm6;
  signed int jm5;
  signed int jm4;
  signed int jm3;
  signed int jm2;
  signed int jm1;
  signed int jp1;
  signed int jp2;
  signed int jp3;
  signed int jp4;
  signed int jp5;
  signed int jp6;
  signed int jp7;
  w = Coded_Picture_Width >> 1;
  h = Coded_Picture_Height >> 1;
  if(!(progressive_frame == 0))
  {
    i = 0;
    while(!(i >= w))
    {
      j = 0;
      while(!(j >= h))
      {
        j2 = j << 1;
        jm3 = j < 3 ? 0 : j - 3;
        jm2 = j < 2 ? 0 : j - 2;
        jm1 = j < 1 ? 0 : j - 1;
        jp1 = j < h - 1 ? j + 1 : h - 1;
        jp2 = j < h - 2 ? j + 2 : h - 1;
        jp3 = j < h - 3 ? j + 3 : h - 1;
        dst[(signed long int)(w * j2)] = Clip[(signed long int)((signed int)((((3 * (signed int)src[(signed long int)(w * jm3)] - 16 * (signed int)src[(signed long int)(w * jm2)]) + 67 * (signed int)src[(signed long int)(w * jm1)] + 227 * (signed int)src[(signed long int)(w * j)]) - 32 * (signed int)src[(signed long int)(w * jp1)]) + 7 * (signed int)src[(signed long int)(w * jp2)] + 128) >> 8)];
        dst[(signed long int)(w * (j2 + 1))] = Clip[(signed long int)((signed int)((((3 * (signed int)src[(signed long int)(w * jp3)] - 16 * (signed int)src[(signed long int)(w * jp2)]) + 67 * (signed int)src[(signed long int)(w * jp1)] + 227 * (signed int)src[(signed long int)(w * j)]) - 32 * (signed int)src[(signed long int)(w * jm1)]) + 7 * (signed int)src[(signed long int)(w * jm2)] + 128) >> 8)];
        j = j + 1;
      }
      src = src + 1l;
      dst = dst + 1l;
      i = i + 1;
    }
  }

  else
  {
    i = 0;
    while(!(i >= w))
    {
      j = 0;
      while(!(j >= h))
      {
        j2 = j << 1;
        jm6 = j < 6 ? 0 : j - 6;
        jm4 = j < 4 ? 0 : j - 4;
        jm2 = j < 2 ? 0 : j - 2;
        jp2 = j < h - 2 ? j + 2 : h - 2;
        jp4 = j < h - 4 ? j + 4 : h - 2;
        jp6 = j < h - 6 ? j + 6 : h - 2;
        dst[(signed long int)(w * j2)] = Clip[(signed long int)((signed int)((((1 * (signed int)src[(signed long int)(w * jm6)] - 7 * (signed int)src[(signed long int)(w * jm4)]) + 30 * (signed int)src[(signed long int)(w * jm2)] + 248 * (signed int)src[(signed long int)(w * j)]) - 21 * (signed int)src[(signed long int)(w * jp2)]) + 5 * (signed int)src[(signed long int)(w * jp4)] + 128) >> 8)];
        dst[(signed long int)(w * (j2 + 2))] = Clip[(signed long int)((signed int)((((7 * (signed int)src[(signed long int)(w * jm4)] - 35 * (signed int)src[(signed long int)(w * jm2)]) + 194 * (signed int)src[(signed long int)(w * j)] + 110 * (signed int)src[(signed long int)(w * jp2)]) - 24 * (signed int)src[(signed long int)(w * jp4)]) + 4 * (signed int)src[(signed long int)(w * jp6)] + 128) >> 8)];
        jm5 = j < 5 ? 1 : j - 5;
        jm3 = j < 3 ? 1 : j - 3;
        jm1 = j < 1 ? 1 : j - 1;
        jp1 = j < h - 1 ? j + 1 : h - 1;
        jp3 = j < h - 3 ? j + 3 : h - 1;
        jp5 = j < h - 5 ? j + 5 : h - 1;
        jp7 = j < h - 7 ? j + 7 : h - 1;
        dst[(signed long int)(w * (j2 + 1))] = Clip[(signed long int)((signed int)((((7 * (signed int)src[(signed long int)(w * jp5)] - 35 * (signed int)src[(signed long int)(w * jp3)]) + 194 * (signed int)src[(signed long int)(w * jp1)] + 110 * (signed int)src[(signed long int)(w * jm1)]) - 24 * (signed int)src[(signed long int)(w * jm3)]) + 4 * (signed int)src[(signed long int)(w * jm5)] + 128) >> 8)];
        dst[(signed long int)(w * (j2 + 3))] = Clip[(signed long int)((signed int)((((1 * (signed int)src[(signed long int)(w * jp7)] - 7 * (signed int)src[(signed long int)(w * jp5)]) + 30 * (signed int)src[(signed long int)(w * jp3)] + 248 * (signed int)src[(signed long int)(w * jp1)]) - 21 * (signed int)src[(signed long int)(w * jm1)]) + 5 * (signed int)src[(signed long int)(w * jm3)] + 128) >> 8)];
        j = j + 2;
      }
      src = src + 1l;
      dst = dst + 1l;
      i = i + 1;
    }
  }
}

// c::conv422to444
// file src/store.c line 509
static void conv422to444(unsigned char *src, unsigned char *dst)
{
  signed int i;
  signed int i2;
  signed int w;
  signed int j;
  signed int im3;
  signed int im2;
  signed int im1;
  signed int ip1;
  signed int ip2;
  signed int ip3;
  w = Coded_Picture_Width >> 1;
  if(!(base.MPEG2_Flag == 0))
  {
    j = 0;
    while(!(j >= Coded_Picture_Height))
    {
      i = 0;
      while(!(i >= w))
      {
        i2 = i << 1;
        im2 = i < 2 ? 0 : i - 2;
        im1 = i < 1 ? 0 : i - 1;
        ip1 = i < w - 1 ? i + 1 : w - 1;
        ip2 = i < w - 2 ? i + 2 : w - 1;
        ip3 = i < w - 3 ? i + 3 : w - 1;
        dst[(signed long int)i2] = src[(signed long int)i];
        dst[(signed long int)(i2 + 1)] = Clip[(signed long int)((signed int)((21 * ((signed int)src[(signed long int)im2] + (signed int)src[(signed long int)ip3]) - 52 * ((signed int)src[(signed long int)im1] + (signed int)src[(signed long int)ip2])) + 159 * ((signed int)src[(signed long int)i] + (signed int)src[(signed long int)ip1]) + 128) >> 8)];
        i = i + 1;
      }
      src = src + (signed long int)w;
      dst = dst + (signed long int)Coded_Picture_Width;
      j = j + 1;
    }
  }

  else
  {
    j = 0;
    while(!(j >= Coded_Picture_Height))
    {
      i = 0;
      while(!(i >= w))
      {
        i2 = i << 1;
        im3 = i < 3 ? 0 : i - 3;
        im2 = i < 2 ? 0 : i - 2;
        im1 = i < 1 ? 0 : i - 1;
        ip1 = i < w - 1 ? i + 1 : w - 1;
        ip2 = i < w - 2 ? i + 2 : w - 1;
        ip3 = i < w - 3 ? i + 3 : w - 1;
        dst[(signed long int)i2] = Clip[(signed long int)((signed int)((((5 * (signed int)src[(signed long int)im3] - 21 * (signed int)src[(signed long int)im2]) + 70 * (signed int)src[(signed long int)im1] + 228 * (signed int)src[(signed long int)i]) - 37 * (signed int)src[(signed long int)ip1]) + 11 * (signed int)src[(signed long int)ip2] + 128) >> 8)];
        dst[(signed long int)(i2 + 1)] = Clip[(signed long int)((signed int)((((5 * (signed int)src[(signed long int)ip3] - 21 * (signed int)src[(signed long int)ip2]) + 70 * (signed int)src[(signed long int)ip1] + 228 * (signed int)src[(signed long int)i]) - 37 * (signed int)src[(signed long int)im1]) + 11 * (signed int)src[(signed long int)im2] + 128) >> 8)];
        i = i + 1;
      }
      src = src + (signed long int)w;
      dst = dst + (signed long int)Coded_Picture_Width;
      j = j + 1;
    }
  }
}

// c::copyright_extension
// file src/gethdr.c line 1112
static void copyright_extension(void)
{
  signed int pos;
  signed int reserved_data;
  pos = ld->Bitcnt;
  unsigned int return_value_Get_Bits$1;
  return_value_Get_Bits$1=Get_Bits(1);
  copyright_flag = (signed int)return_value_Get_Bits$1;
  unsigned int return_value_Get_Bits$2;
  return_value_Get_Bits$2=Get_Bits(8);
  copyright_identifier = (signed int)return_value_Get_Bits$2;
  unsigned int return_value_Get_Bits$3;
  return_value_Get_Bits$3=Get_Bits(1);
  original_or_copy = (signed int)return_value_Get_Bits$3;
  unsigned int return_value_Get_Bits$4;
  return_value_Get_Bits$4=Get_Bits(7);
  reserved_data = (signed int)return_value_Get_Bits$4;
  marker_bit("copyright_extension(), first marker bit");
  unsigned int return_value_Get_Bits$5;
  return_value_Get_Bits$5=Get_Bits(20);
  copyright_number_1 = (signed int)return_value_Get_Bits$5;
  marker_bit("copyright_extension(), second marker bit");
  unsigned int return_value_Get_Bits$6;
  return_value_Get_Bits$6=Get_Bits(22);
  copyright_number_2 = (signed int)return_value_Get_Bits$6;
  marker_bit("copyright_extension(), third marker bit");
  unsigned int return_value_Get_Bits$7;
  return_value_Get_Bits$7=Get_Bits(22);
  copyright_number_3 = (signed int)return_value_Get_Bits$7;
  if(Verbose_Flag > 0)
  {
    printf("copyright_extension (byte %d)\n", (pos >> 3) - 4);
    if(Verbose_Flag > 1)
    {
      printf("  copyright_flag =%d\n", copyright_flag);
      printf("  copyright_identifier=%d\n", copyright_identifier);
      printf("  original_or_copy = %d (original=1, copy=0)\n", original_or_copy);
      printf("  copyright_number_1=%d\n", copyright_number_1);
      printf("  copyright_number_2=%d\n", copyright_number_2);
      printf("  copyright_number_3=%d\n", copyright_number_3);
    }

  }

}

// c::decode_motion_vector
// file src/motion.c line 219
static void decode_motion_vector(signed int *pred, signed int r_size, signed int motion_code, signed int motion_residual, signed int full_pel_vector)
{
  signed int lim;
  signed int vec;
  lim = 16 << r_size;
  signed int tmp_if_expr$1;
  if(!(full_pel_vector == 0))
    tmp_if_expr$1 = *pred >> 1;

  else
    tmp_if_expr$1 = *pred;
  vec = tmp_if_expr$1;
  if(motion_code > 0)
  {
    vec = vec + (motion_code - 1 << r_size) + motion_residual + 1;
    if(vec >= lim)
      vec = vec - (lim + lim);

  }

  else
    if(motion_code < 0)
    {
      vec = vec - ((-motion_code - 1 << r_size) + motion_residual + 1);
      if(!(vec >= -lim))
        vec = vec + lim + lim;

    }

  *pred = full_pel_vector != 0 ? vec << 1 : vec;
}

// c::dprintf
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 139
signed int dprintf(signed int __fd, const char * restrict __fmt, ...)
{
  void *return_value___builtin_va_arg_pack$1;
  return_value___builtin_va_arg_pack$1=__builtin_va_arg_pack();
  signed int return_value___dprintf_chk$2;
  return_value___dprintf_chk$2=__dprintf_chk(__fd, 2 - 1, __fmt, return_value___builtin_va_arg_pack$1);
  return return_value___dprintf_chk$2;
}

// c::extension_and_user_data
// file src/gethdr.c line 510
static void extension_and_user_data(void)
{
  signed int code;
  signed int ext_ID;
  next_start_code();
  unsigned int return_value_Show_Bits$1;
  do
  {
    return_value_Show_Bits$1=Show_Bits(32);
    code = (signed int)return_value_Show_Bits$1;
    if(code == 437)
      goto __CPROVER_DUMP_L2;

    if(code == 434)
      goto __CPROVER_DUMP_L2;

    goto __CPROVER_DUMP_L16;

  __CPROVER_DUMP_L2:
    ;
    if(code == 437)
    {
      Flush_Buffer32();
      unsigned int return_value_Get_Bits$2;
      return_value_Get_Bits$2=Get_Bits(4);
      ext_ID = (signed int)return_value_Get_Bits$2;
      switch(ext_ID)
      {

        case 1:
          {
            sequence_extension();
            goto __CPROVER_DUMP_L13;
          }
        case 2:
          {
            sequence_display_extension();
            goto __CPROVER_DUMP_L13;
          }
        case 3:
          {
            quant_matrix_extension();
            goto __CPROVER_DUMP_L13;
          }
        case 5:
          {
            sequence_scalable_extension();
            goto __CPROVER_DUMP_L13;
          }
        case 7:
          {
            picture_display_extension();
            goto __CPROVER_DUMP_L13;
          }
        case 8:
          {
            picture_coding_extension();
            goto __CPROVER_DUMP_L13;
          }
        case 9:
          {
            picture_spatial_scalable_extension();
            goto __CPROVER_DUMP_L13;
          }
        case 10:
          {
            picture_temporal_scalable_extension();
            goto __CPROVER_DUMP_L13;
          }
        case 4:
          {
            copyright_extension();
            goto __CPROVER_DUMP_L13;
          }
        default:
          fprintf(stderr, "reserved extension start code ID %d\n", ext_ID);
      }

    __CPROVER_DUMP_L13:
      ;
      next_start_code();
    }

    else
    {
      Flush_Buffer32();
      user_data();
    }
  }
  while(TRUE);

__CPROVER_DUMP_L16:
  ;
}

// c::extra_bit_information
// file src/gethdr.c line 1066
static signed int extra_bit_information(void)
{
  signed int Byte_Count = 0;
  unsigned int return_value_Get_Bits1$1;
  do
  {
    return_value_Get_Bits1$1=Get_Bits1();
    if(return_value_Get_Bits1$1 == 0u)
      goto __CPROVER_DUMP_L2;

    Flush_Buffer(8);
    Byte_Count = Byte_Count + 1;
  }
  while(TRUE);

__CPROVER_DUMP_L2:
  ;
  return Byte_Count;
}

// c::feof_unlocked
// file /usr/include/x86_64-linux-gnu/bits/stdio.h line 125
signed int feof_unlocked(struct _IO_FILE *__stream)
{
  return (signed int)((__stream->_flags & 16) != 0);
}

// c::ferror_unlocked
// file /usr/include/x86_64-linux-gnu/bits/stdio.h line 132
signed int ferror_unlocked(struct _IO_FILE *__stream)
{
  return (signed int)((__stream->_flags & 32) != 0);
}

// c::fgetc_unlocked
// file /usr/include/x86_64-linux-gnu/bits/stdio.h line 53
signed int fgetc_unlocked(struct _IO_FILE *__fp)
{
  signed int tmp_if_expr$3;
  signed int return_value___uflow$1;
  char *tmp_post$2;
  if(__fp->_IO_read_ptr >= __fp->_IO_read_end)
  {
    return_value___uflow$1=__uflow(__fp);
    tmp_if_expr$3 = return_value___uflow$1;
  }

  else
  {
    tmp_post$2 = __fp->_IO_read_ptr;
    __fp->_IO_read_ptr = __fp->_IO_read_ptr + 1l;
    tmp_if_expr$3 = (signed int)*((unsigned char *)tmp_post$2);
  }
  return tmp_if_expr$3;
}

// c::fgets
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 253
char * fgets(char * restrict __s, signed int __n, struct _IO_FILE * restrict __stream)
{
  char *return_value___fgets_chk$1;
  char *return_value___fgets_chk_warn$2;
  if(FALSE)
  {

  __CPROVER_DUMP_L1:
    ;
    return_value___fgets_chk$1=__fgets_chk(__s, 18446744073709551615ul, __n, __stream);
    return return_value___fgets_chk$1;
    if((unsigned long int)__n > 18446744073709551615ul)
    {
      return_value___fgets_chk_warn$2=__fgets_chk_warn(__s, 18446744073709551615ul, __n, __stream);
      return return_value___fgets_chk_warn$2;
    }

  }

  char *return_value___fgets_alias$3;
  return_value___fgets_alias$3=__fgets_alias(__s, __n, __stream);
  return return_value___fgets_alias$3;
}

// c::form_component_prediction
// file src/recon.c line 437
static void form_component_prediction(unsigned char *src, unsigned char *dst, signed int lx, signed int lx2, signed int w, signed int h, signed int x, signed int y, signed int dx, signed int dy, signed int average_flag)
{
  signed int xint;
  signed int yint;
  signed int xh;
  signed int yh;
  signed int i;
  signed int j;
  signed int v;
  unsigned char *s;
  unsigned char *d;
  xint = dx >> 1;
  yint = dy >> 1;
  s = src + (signed long int)(lx * (y + yint)) + (signed long int)x + (signed long int)xint;
  d = dst + (signed long int)(lx * y) + (signed long int)x;
  xh = dx & 1;
  yh = dy & 1;
  if(!(s == d))
    (void)0;

  else
    /* assertion s!=d */
    assert(FALSE);
  if(xh == 0)
  {
    if(yh != 0)
      goto __CPROVER_DUMP_L12;

    if(!(average_flag == 0))
    {
      j = 0;
      while(!(j >= h))
      {
        i = 0;
        while(!(i >= w))
        {
          v = (signed int)d[(signed long int)i] + (signed int)s[(signed long int)i];
          d[(signed long int)i] = (unsigned char)(v + (v >= 0 ? 1 : 0) >> 1);
          i = i + 1;
        }
        s = s + (signed long int)lx2;
        d = d + (signed long int)lx2;
        j = j + 1;
      }
    }

    else
    {
      j = 0;
      while(!(j >= h))
      {
        i = 0;
        while(!(i >= w))
        {
          d[(signed long int)i] = s[(signed long int)i];
          i = i + 1;
        }
        s = s + (signed long int)lx2;
        d = d + (signed long int)lx2;
        j = j + 1;
      }
    }
  }

  else
  {

  __CPROVER_DUMP_L12:
    ;
    if(xh == 0)
    {
      if(yh == 0)
        goto __CPROVER_DUMP_L22;

      if(!(average_flag == 0))
      {
        j = 0;
        while(!(j >= h))
        {
          i = 0;
          while(!(i >= w))
          {
            v = (signed int)((unsigned int)d[(signed long int)i] + ((unsigned int)((signed int)s[(signed long int)i] + (signed int)s[(signed long int)(i + lx)] + 1) >> 1));
            d[(signed long int)i] = (unsigned char)(v + (v >= 0 ? 1 : 0) >> 1);
            i = i + 1;
          }
          s = s + (signed long int)lx2;
          d = d + (signed long int)lx2;
          j = j + 1;
        }
      }

      else
      {
        j = 0;
        while(!(j >= h))
        {
          i = 0;
          while(!(i >= w))
          {
            d[(signed long int)i] = (unsigned char)((unsigned int)((signed int)s[(signed long int)i] + (signed int)s[(signed long int)(i + lx)] + 1) >> 1);
            i = i + 1;
          }
          s = s + (signed long int)lx2;
          d = d + (signed long int)lx2;
          j = j + 1;
        }
      }
    }

    else
    {

    __CPROVER_DUMP_L22:
      ;
      if(!(xh == 0))
      {
        if(yh != 0)
          goto __CPROVER_DUMP_L32;

        if(!(average_flag == 0))
        {
          j = 0;
          while(!(j >= h))
          {
            i = 0;
            while(!(i >= w))
            {
              v = (signed int)((unsigned int)d[(signed long int)i] + ((unsigned int)((signed int)s[(signed long int)i] + (signed int)s[(signed long int)(i + 1)] + 1) >> 1));
              d[(signed long int)i] = (unsigned char)(v + (v >= 0 ? 1 : 0) >> 1);
              i = i + 1;
            }
            s = s + (signed long int)lx2;
            d = d + (signed long int)lx2;
            j = j + 1;
          }
        }

        else
        {
          j = 0;
          while(!(j >= h))
          {
            i = 0;
            while(!(i >= w))
            {
              d[(signed long int)i] = (unsigned char)((unsigned int)((signed int)s[(signed long int)i] + (signed int)s[(signed long int)(i + 1)] + 1) >> 1);
              i = i + 1;
            }
            s = s + (signed long int)lx2;
            d = d + (signed long int)lx2;
            j = j + 1;
          }
        }
      }

      else
      {

      __CPROVER_DUMP_L32:
        ;
        if(!(average_flag == 0))
        {
          j = 0;
          while(!(j >= h))
          {
            i = 0;
            while(!(i >= w))
            {
              v = (signed int)((unsigned int)d[(signed long int)i] + ((unsigned int)((signed int)s[(signed long int)i] + (signed int)s[(signed long int)(i + 1)] + (signed int)s[(signed long int)(i + lx)] + (signed int)s[(signed long int)(i + lx + 1)] + 2) >> 2));
              d[(signed long int)i] = (unsigned char)(v + (v >= 0 ? 1 : 0) >> 1);
              i = i + 1;
            }
            s = s + (signed long int)lx2;
            d = d + (signed long int)lx2;
            j = j + 1;
          }
        }

        else
        {
          j = 0;
          while(!(j >= h))
          {
            i = 0;
            while(!(i >= w))
            {
              d[(signed long int)i] = (unsigned char)((unsigned int)((signed int)s[(signed long int)i] + (signed int)s[(signed long int)(i + 1)] + (signed int)s[(signed long int)(i + lx)] + (signed int)s[(signed long int)(i + lx + 1)] + 2) >> 2);
              i = i + 1;
            }
            s = s + (signed long int)lx2;
            d = d + (signed long int)lx2;
            j = j + 1;
          }
        }
      }
    }
  }
}

// c::form_component_prediction2
// file src/recon.c line 992
static void form_component_prediction2(unsigned char *src, unsigned char *dst, signed int lx, signed int lx2, signed int w, signed int h, signed int dx, signed int dy, signed int average_flag)
{
  signed int xint;
  signed int yint;
  signed int xh;
  signed int yh;
  signed int i;
  signed int j;
  signed int v;
  unsigned char *s;
  unsigned char *d;
  s = src;
  d = dst;
  xh = dx;
  yh = dy;
  if(xh == 0)
  {
    if(yh != 0)
      goto __CPROVER_DUMP_L12;

    if(!(average_flag == 0))
    {
      unsigned char *s1;
      unsigned char *d1;
      signed int v1;
      j = 0;
      while(!(j >= h))
      {
        s1 = s + (signed long int)lx2;
        d1 = d + (signed long int)lx2;
        i = 0;
        while(!(i >= w))
        {
          v = (signed int)d[(signed long int)i] + (signed int)s[(signed long int)i];
          v1 = (signed int)d1[(signed long int)i] + (signed int)s1[(signed long int)i];
          d[(signed long int)i] = (unsigned char)(v + (v >= 0 ? 1 : 0) >> 1);
          d1[(signed long int)i] = (unsigned char)(v1 + (v1 >= 0 ? 1 : 0) >> 1);
          i = i + 1;
        }
        s = s1 + (signed long int)lx2;
        d = d1 + (signed long int)lx2;
        j = j + 2;
      }
    }

    else
    {
      j = 0;
      while(!(j >= h))
      {
        i = 0;
        while(!(i >= w))
        {
          d[(signed long int)i] = s[(signed long int)i];
          i = i + 1;
        }
        s = s + (signed long int)lx2;
        d = d + (signed long int)lx2;
        i = 0;
        while(!(i >= w))
        {
          d[(signed long int)i] = s[(signed long int)i];
          i = i + 1;
        }
        s = s + (signed long int)lx2;
        d = d + (signed long int)lx2;
        j = j + 2;
      }
    }
  }

  else
  {

  __CPROVER_DUMP_L12:
    ;
    if(xh == 0)
    {
      if(yh == 0)
        goto __CPROVER_DUMP_L26;

      if(!(average_flag == 0))
      {
        j = 0;
        while(!(j >= h))
        {
          i = 0;
          while(!(i >= w))
          {
            v = (signed int)((unsigned int)d[(signed long int)i] + ((unsigned int)((signed int)s[(signed long int)i] + (signed int)s[(signed long int)(i + lx)] + 1) >> 1));
            d[(signed long int)i] = (unsigned char)(v + (v >= 0 ? 1 : 0) >> 1);
            i = i + 1;
          }
          s = s + (signed long int)lx2;
          d = d + (signed long int)lx2;
          i = 0;
          while(!(i >= w))
          {
            v = (signed int)((unsigned int)d[(signed long int)i] + ((unsigned int)((signed int)s[(signed long int)i] + (signed int)s[(signed long int)(i + lx)] + 1) >> 1));
            d[(signed long int)i] = (unsigned char)(v + (v >= 0 ? 1 : 0) >> 1);
            i = i + 1;
          }
          s = s + (signed long int)lx2;
          d = d + (signed long int)lx2;
          j = j + 2;
        }
      }

      else
      {
        j = 0;
        while(!(j >= h))
        {
          i = 0;
          while(!(i >= w))
          {
            d[(signed long int)i] = (unsigned char)((unsigned int)((signed int)s[(signed long int)i] + (signed int)s[(signed long int)(i + lx)] + 1) >> 1);
            i = i + 1;
          }
          s = s + (signed long int)lx2;
          d = d + (signed long int)lx2;
          i = 0;
          while(!(i >= w))
          {
            d[(signed long int)i] = (unsigned char)((unsigned int)((signed int)s[(signed long int)i] + (signed int)s[(signed long int)(i + lx)] + 1) >> 1);
            i = i + 1;
          }
          s = s + (signed long int)lx2;
          d = d + (signed long int)lx2;
          j = j + 2;
        }
      }
    }

    else
    {

    __CPROVER_DUMP_L26:
      ;
      if(!(xh == 0))
      {
        if(yh != 0)
          goto __CPROVER_DUMP_L40;

        if(!(average_flag == 0))
        {
          j = 0;
          while(!(j >= h))
          {
            i = 0;
            while(!(i >= w))
            {
              v = (signed int)((unsigned int)d[(signed long int)i] + ((unsigned int)((signed int)s[(signed long int)i] + (signed int)s[(signed long int)(i + 1)] + 1) >> 1));
              d[(signed long int)i] = (unsigned char)(v + (v >= 0 ? 1 : 0) >> 1);
              i = i + 1;
            }
            s = s + (signed long int)lx2;
            d = d + (signed long int)lx2;
            i = 0;
            while(!(i >= w))
            {
              v = (signed int)((unsigned int)d[(signed long int)i] + ((unsigned int)((signed int)s[(signed long int)i] + (signed int)s[(signed long int)(i + 1)] + 1) >> 1));
              d[(signed long int)i] = (unsigned char)(v + (v >= 0 ? 1 : 0) >> 1);
              i = i + 1;
            }
            s = s + (signed long int)lx2;
            d = d + (signed long int)lx2;
            j = j + 2;
          }
        }

        else
        {
          j = 0;
          while(!(j >= h))
          {
            i = 0;
            while(!(i >= w))
            {
              d[(signed long int)i] = (unsigned char)((unsigned int)((signed int)s[(signed long int)i] + (signed int)s[(signed long int)(i + 1)] + 1) >> 1);
              i = i + 1;
            }
            s = s + (signed long int)lx2;
            d = d + (signed long int)lx2;
            i = 0;
            while(!(i >= w))
            {
              d[(signed long int)i] = (unsigned char)((unsigned int)((signed int)s[(signed long int)i] + (signed int)s[(signed long int)(i + 1)] + 1) >> 1);
              i = i + 1;
            }
            s = s + (signed long int)lx2;
            d = d + (signed long int)lx2;
            j = j + 2;
          }
        }
      }

      else
      {

      __CPROVER_DUMP_L40:
        ;
        if(!(average_flag == 0))
        {
          j = 0;
          while(!(j >= h))
          {
            i = 0;
            while(!(i >= w))
            {
              v = (signed int)((unsigned int)d[(signed long int)i] + ((unsigned int)((signed int)s[(signed long int)i] + (signed int)s[(signed long int)(i + 1)] + (signed int)s[(signed long int)(i + lx)] + (signed int)s[(signed long int)(i + lx + 1)] + 2) >> 2));
              d[(signed long int)i] = (unsigned char)(v + (v >= 0 ? 1 : 0) >> 1);
              i = i + 1;
            }
            s = s + (signed long int)lx2;
            d = d + (signed long int)lx2;
            i = 0;
            while(!(i >= w))
            {
              v = (signed int)((unsigned int)d[(signed long int)i] + ((unsigned int)((signed int)s[(signed long int)i] + (signed int)s[(signed long int)(i + 1)] + (signed int)s[(signed long int)(i + lx)] + (signed int)s[(signed long int)(i + lx + 1)] + 2) >> 2));
              d[(signed long int)i] = (unsigned char)(v + (v >= 0 ? 1 : 0) >> 1);
              i = i + 1;
            }
            s = s + (signed long int)lx2;
            d = d + (signed long int)lx2;
            j = j + 2;
          }
        }

        else
        {
          j = 0;
          while(!(j >= h))
          {
            i = 0;
            while(!(i >= w))
            {
              d[(signed long int)i] = (unsigned char)((unsigned int)((signed int)s[(signed long int)i] + (signed int)s[(signed long int)(i + 1)] + (signed int)s[(signed long int)(i + lx)] + (signed int)s[(signed long int)(i + lx + 1)] + 2) >> 2);
              i = i + 1;
            }
            s = s + (signed long int)lx2;
            d = d + (signed long int)lx2;
            i = 0;
            while(!(i >= w))
            {
              d[(signed long int)i] = (unsigned char)((unsigned int)((signed int)s[(signed long int)i] + (signed int)s[(signed long int)(i + 1)] + (signed int)s[(signed long int)(i + lx)] + (signed int)s[(signed long int)(i + lx + 1)] + 2) >> 2);
              i = i + 1;
            }
            s = s + (signed long int)lx2;
            d = d + (signed long int)lx2;
            j = j + 2;
          }
        }
      }
    }
  }
}

// c::form_prediction
// file src/recon.c line 326
static void form_prediction(unsigned char **src, signed int sfield, unsigned char **dst, signed int dfield, signed int lx, signed int lx2, signed int w, signed int h, signed int x, signed int y, signed int dx, signed int dy, signed int average_flag)
{
  signed int sf_val;
  signed int df_val;
  signed int sly_val;
  signed int dly_val;
  signed int slx_val;
  signed int xh;
  signed int yh;
  form_component_prediction(src[(signed long int)0] + (signed long int)(sfield != 0 ? lx2 >> 1 : 0), dst[(signed long int)0] + (signed long int)(dfield != 0 ? lx2 >> 1 : 0), lx, lx2, w, h, x, y, dx, dy, average_flag);
  if(!(chroma_format == 3))
  {
    lx = lx >> 1;
    lx2 = lx2 >> 1;
    w = w >> 1;
    x = x >> 1;
    dx = dx / 2;
  }

  if(chroma_format == 1)
  {
    h = h >> 1;
    y = y >> 1;
    dy = dy / 2;
  }

  sf_val = sfield != 0 ? lx2 >> 1 : 0;
  df_val = dfield != 0 ? lx2 >> 1 : 0;
  sly_val = lx * (y + (dy >> 1));
  dly_val = lx * y;
  slx_val = x + (dx >> 1);
  xh = dx & 1;
  yh = dy & 1;
  form_component_prediction2(src[(signed long int)1] + (signed long int)sf_val + (signed long int)sly_val + (signed long int)slx_val, dst[(signed long int)1] + (signed long int)df_val + (signed long int)dly_val + (signed long int)x, lx, lx2, w, h, xh, yh, average_flag);
  form_component_prediction2(src[(signed long int)2] + (signed long int)sf_val + (signed long int)sly_val + (signed long int)slx_val, dst[(signed long int)2] + (signed long int)df_val + (signed long int)dly_val + (signed long int)x, lx, lx2, w, h, xh, yh, average_flag);
}

// c::form_predictions
// file src/global.h line 186
void form_predictions(signed int bx, signed int by, signed int macroblock_type, signed int motion_type, signed int (*PMV)[2l][2l], signed int (*motion_vertical_field_select)[2l], signed int *dmvector, signed int stwtype)
{
  signed int currentfield;
  unsigned char **predframe;
  signed int DMV[2l][2l];
  signed int stwtop;
  signed int stwbot;
  stwtop = stwtype % 3;
  stwbot = stwtype / 3;
  _Bool tmp_if_expr$1;
  _Bool tmp_if_expr$2;
  if((8 & macroblock_type) == 0)
  {
    if(picture_coding_type == 2)
      goto __CPROVER_DUMP_L1;

  }

  else
  {

  __CPROVER_DUMP_L1:
    ;
    if(picture_structure == 3)
    {
      if(!(motion_type == 2))
      {
        if((8 & macroblock_type) == 0)
          goto __CPROVER_DUMP_L2;

      }

      else
      {

      __CPROVER_DUMP_L2:
        ;
        if(stwtop < 2)
          form_prediction(forward_reference_frame, 0, current_frame, 0, Coded_Picture_Width, Coded_Picture_Width << 1, 16, 8, bx, by, PMV[(signed long int)0][(signed long int)0][(signed long int)0], PMV[(signed long int)0][(signed long int)0][(signed long int)1], stwtop);

        if(stwbot < 2)
          form_prediction(forward_reference_frame, 1, current_frame, 1, Coded_Picture_Width, Coded_Picture_Width << 1, 16, 8, bx, by, PMV[(signed long int)0][(signed long int)0][(signed long int)0], PMV[(signed long int)0][(signed long int)0][(signed long int)1], stwbot);

        goto __CPROVER_DUMP_L12;
      }
      if(motion_type == 1)
      {
        if(stwtop < 2)
          form_prediction(forward_reference_frame, motion_vertical_field_select[(signed long int)0][(signed long int)0], current_frame, 0, Coded_Picture_Width << 1, Coded_Picture_Width << 1, 16, 8, bx, by >> 1, PMV[(signed long int)0][(signed long int)0][(signed long int)0], PMV[(signed long int)0][(signed long int)0][(signed long int)1] >> 1, stwtop);

        if(stwbot < 2)
          form_prediction(forward_reference_frame, motion_vertical_field_select[(signed long int)1][(signed long int)0], current_frame, 1, Coded_Picture_Width << 1, Coded_Picture_Width << 1, 16, 8, bx, by >> 1, PMV[(signed long int)1][(signed long int)0][(signed long int)0], PMV[(signed long int)1][(signed long int)0][(signed long int)1] >> 1, stwbot);

      }

      else
        if(motion_type == 3)
        {
          Dual_Prime_Arithmetic(DMV, dmvector, PMV[(signed long int)0][(signed long int)0][(signed long int)0], PMV[(signed long int)0][(signed long int)0][(signed long int)1] >> 1);
          if(stwtop < 2)
          {
            form_prediction(forward_reference_frame, 0, current_frame, 0, Coded_Picture_Width << 1, Coded_Picture_Width << 1, 16, 8, bx, by >> 1, PMV[(signed long int)0][(signed long int)0][(signed long int)0], PMV[(signed long int)0][(signed long int)0][(signed long int)1] >> 1, 0);
            form_prediction(forward_reference_frame, 1, current_frame, 0, Coded_Picture_Width << 1, Coded_Picture_Width << 1, 16, 8, bx, by >> 1, DMV[(signed long int)0][(signed long int)0], DMV[(signed long int)0][(signed long int)1], 1);
          }

          if(stwbot < 2)
          {
            form_prediction(forward_reference_frame, 1, current_frame, 1, Coded_Picture_Width << 1, Coded_Picture_Width << 1, 16, 8, bx, by >> 1, PMV[(signed long int)0][(signed long int)0][(signed long int)0], PMV[(signed long int)0][(signed long int)0][(signed long int)1] >> 1, 0);
            form_prediction(forward_reference_frame, 0, current_frame, 1, Coded_Picture_Width << 1, Coded_Picture_Width << 1, 16, 8, bx, by >> 1, DMV[(signed long int)1][(signed long int)0], DMV[(signed long int)1][(signed long int)1], 1);
          }

        }

        else
          printf("invalid motion_type\n");
    }

    else
    {
      currentfield = (signed int)(picture_structure == 2);
      if(picture_coding_type == 2)
      {
        if(Second_Field == 0)
          goto __CPROVER_DUMP_L14;

        tmp_if_expr$1 = currentfield != motion_vertical_field_select[(signed long int)0][(signed long int)0] ? TRUE : FALSE;
      }

      else
      {

      __CPROVER_DUMP_L14:
        ;
        tmp_if_expr$1 = FALSE;
      }
      if(tmp_if_expr$1)
        predframe = backward_reference_frame;

      else
        predframe = forward_reference_frame;
      if(!(motion_type == 1))
      {
        if((8 & macroblock_type) == 0)
          goto __CPROVER_DUMP_L18;

      }

      else
      {

      __CPROVER_DUMP_L18:
        ;
        if(stwtop < 2)
          form_prediction(predframe, motion_vertical_field_select[(signed long int)0][(signed long int)0], current_frame, 0, Coded_Picture_Width << 1, Coded_Picture_Width << 1, 16, 16, bx, by, PMV[(signed long int)0][(signed long int)0][(signed long int)0], PMV[(signed long int)0][(signed long int)0][(signed long int)1], stwtop);

        goto __CPROVER_DUMP_L30;
      }
      if(motion_type == 2)
      {
        if(stwtop < 2)
        {
          form_prediction(predframe, motion_vertical_field_select[(signed long int)0][(signed long int)0], current_frame, 0, Coded_Picture_Width << 1, Coded_Picture_Width << 1, 16, 8, bx, by, PMV[(signed long int)0][(signed long int)0][(signed long int)0], PMV[(signed long int)0][(signed long int)0][(signed long int)1], stwtop);
          if(picture_coding_type == 2)
          {
            if(Second_Field == 0)
              goto __CPROVER_DUMP_L21;

            tmp_if_expr$2 = currentfield != motion_vertical_field_select[(signed long int)1][(signed long int)0] ? TRUE : FALSE;
          }

          else
          {

          __CPROVER_DUMP_L21:
            ;
            tmp_if_expr$2 = FALSE;
          }
          if(tmp_if_expr$2)
            predframe = backward_reference_frame;

          else
            predframe = forward_reference_frame;
          form_prediction(predframe, motion_vertical_field_select[(signed long int)1][(signed long int)0], current_frame, 0, Coded_Picture_Width << 1, Coded_Picture_Width << 1, 16, 8, bx, by + 8, PMV[(signed long int)1][(signed long int)0][(signed long int)0], PMV[(signed long int)1][(signed long int)0][(signed long int)1], stwtop);
        }

      }

      else
        if(motion_type == 3)
        {
          if(!(Second_Field == 0))
            predframe = backward_reference_frame;

          else
            predframe = forward_reference_frame;
          Dual_Prime_Arithmetic(DMV, dmvector, PMV[(signed long int)0][(signed long int)0][(signed long int)0], PMV[(signed long int)0][(signed long int)0][(signed long int)1]);
          form_prediction(forward_reference_frame, currentfield, current_frame, 0, Coded_Picture_Width << 1, Coded_Picture_Width << 1, 16, 16, bx, by, PMV[(signed long int)0][(signed long int)0][(signed long int)0], PMV[(signed long int)0][(signed long int)0][(signed long int)1], 0);
          form_prediction(predframe, (signed int)!(currentfield != 0), current_frame, 0, Coded_Picture_Width << 1, Coded_Picture_Width << 1, 16, 16, bx, by, DMV[(signed long int)0][(signed long int)0], DMV[(signed long int)0][(signed long int)1], 1);
        }

        else
          printf("invalid motion_type\n");
    }

  __CPROVER_DUMP_L12:
    ;

  __CPROVER_DUMP_L30:
    ;
    stwbot = 1;
    stwtop = stwbot;
  }
  if(!((4 & macroblock_type) == 0))
  {
    if(picture_structure == 3)
    {
      if(motion_type == 2)
      {
        if(stwtop < 2)
          form_prediction(backward_reference_frame, 0, current_frame, 0, Coded_Picture_Width, Coded_Picture_Width << 1, 16, 8, bx, by, PMV[(signed long int)0][(signed long int)1][(signed long int)0], PMV[(signed long int)0][(signed long int)1][(signed long int)1], stwtop);

        if(stwbot < 2)
          form_prediction(backward_reference_frame, 1, current_frame, 1, Coded_Picture_Width, Coded_Picture_Width << 1, 16, 8, bx, by, PMV[(signed long int)0][(signed long int)1][(signed long int)0], PMV[(signed long int)0][(signed long int)1][(signed long int)1], stwbot);

      }

      else
      {
        if(stwtop < 2)
          form_prediction(backward_reference_frame, motion_vertical_field_select[(signed long int)0][(signed long int)1], current_frame, 0, Coded_Picture_Width << 1, Coded_Picture_Width << 1, 16, 8, bx, by >> 1, PMV[(signed long int)0][(signed long int)1][(signed long int)0], PMV[(signed long int)0][(signed long int)1][(signed long int)1] >> 1, stwtop);

        if(stwbot < 2)
          form_prediction(backward_reference_frame, motion_vertical_field_select[(signed long int)1][(signed long int)1], current_frame, 1, Coded_Picture_Width << 1, Coded_Picture_Width << 1, 16, 8, bx, by >> 1, PMV[(signed long int)1][(signed long int)1][(signed long int)0], PMV[(signed long int)1][(signed long int)1][(signed long int)1] >> 1, stwbot);

      }
    }

    else
      if(motion_type == 1)
        form_prediction(backward_reference_frame, motion_vertical_field_select[(signed long int)0][(signed long int)1], current_frame, 0, Coded_Picture_Width << 1, Coded_Picture_Width << 1, 16, 16, bx, by, PMV[(signed long int)0][(signed long int)1][(signed long int)0], PMV[(signed long int)0][(signed long int)1][(signed long int)1], stwtop);

      else
        if(motion_type == 2)
        {
          form_prediction(backward_reference_frame, motion_vertical_field_select[(signed long int)0][(signed long int)1], current_frame, 0, Coded_Picture_Width << 1, Coded_Picture_Width << 1, 16, 8, bx, by, PMV[(signed long int)0][(signed long int)1][(signed long int)0], PMV[(signed long int)0][(signed long int)1][(signed long int)1], stwtop);
          form_prediction(backward_reference_frame, motion_vertical_field_select[(signed long int)1][(signed long int)1], current_frame, 0, Coded_Picture_Width << 1, Coded_Picture_Width << 1, 16, 8, bx, by + 8, PMV[(signed long int)1][(signed long int)1][(signed long int)0], PMV[(signed long int)1][(signed long int)1][(signed long int)1], stwtop);
        }

        else
          printf("invalid motion_type\n");
  }

}

// c::fprintf
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 95
signed int fprintf(struct _IO_FILE * restrict __stream, const char * restrict __fmt, ...)
{
  void *return_value___builtin_va_arg_pack$1;
  return_value___builtin_va_arg_pack$1=__builtin_va_arg_pack();
  signed int return_value___fprintf_chk$2;
  return_value___fprintf_chk$2=__fprintf_chk(__stream, 2 - 1, __fmt, return_value___builtin_va_arg_pack$1);
  return return_value___fprintf_chk$2;
}

// c::fputc_unlocked
// file /usr/include/x86_64-linux-gnu/bits/stdio.h line 88
signed int fputc_unlocked(signed int __c, struct _IO_FILE *__stream)
{
  signed int tmp_if_expr$3;
  signed int return_value___overflow$1;
  char *tmp_post$2;
  if(__stream->_IO_write_ptr >= __stream->_IO_write_end)
  {
    return_value___overflow$1=__overflow(__stream, (signed int)(unsigned char)__c);
    tmp_if_expr$3 = return_value___overflow$1;
  }

  else
  {
    tmp_post$2 = __stream->_IO_write_ptr;
    __stream->_IO_write_ptr = __stream->_IO_write_ptr + 1l;
    *tmp_post$2 = (char)__c;
    tmp_if_expr$3 = (signed int)(unsigned char)*tmp_post$2;
  }
  return tmp_if_expr$3;
}

// c::frame_reorder
// file src/getpic.c line 955
static void frame_reorder(signed int Bitstream_Framenum, signed int Sequence_Framenum)
{
  static signed int Newref_progressive_frame;
  static signed int Oldref_progressive_frame;
  if(!(Sequence_Framenum == 0))
  {
    if(!(picture_structure == 3))
    {
      if(Second_Field != 0)
        goto __CPROVER_DUMP_L1;

    }

    else
    {

    __CPROVER_DUMP_L1:
      ;
      if(picture_coding_type == 3)
        Write_Frame(auxframe, Bitstream_Framenum - 1);

      else
      {
        Newref_progressive_frame = progressive_frame;
        progressive_frame = Oldref_progressive_frame;
        Write_Frame(forward_reference_frame, Bitstream_Framenum - 1);
        progressive_frame = Newref_progressive_frame;
        Oldref_progressive_frame = progressive_frame;
      }
    }
  }

  else
    Oldref_progressive_frame = progressive_frame;
}

// c::fread
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 282
unsigned long int fread(void * restrict __ptr, unsigned long int __size, unsigned long int __n, struct _IO_FILE * restrict __stream)
{
  unsigned long int return_value___fread_chk$1;
  unsigned long int return_value___fread_chk_warn$2;
  if(FALSE)
  {

  __CPROVER_DUMP_L1:
    ;
    return_value___fread_chk$1=__fread_chk(__ptr, 18446744073709551615ul, __size, __n, __stream);
    return return_value___fread_chk$1;
    if(__n * __size > 18446744073709551615ul)
    {
      return_value___fread_chk_warn$2=__fread_chk_warn(__ptr, 18446744073709551615ul, __size, __n, __stream);
      return return_value___fread_chk_warn$2;
    }

  }

  unsigned long int return_value___fread_alias$3;
  return_value___fread_alias$3=__fread_alias(__ptr, __size, __n, __stream);
  return return_value___fread_alias$3;
}

// c::fread_unlocked
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 343
unsigned long int fread_unlocked(void * restrict __ptr, unsigned long int __size, unsigned long int __n, struct _IO_FILE * restrict __stream)
{
  unsigned long int return_value___fread_unlocked_chk$1;
  unsigned long int return_value___fread_unlocked_chk_warn$2;
  if(FALSE)
  {

  __CPROVER_DUMP_L1:
    ;
    return_value___fread_unlocked_chk$1=__fread_unlocked_chk(__ptr, 18446744073709551615ul, __size, __n, __stream);
    return return_value___fread_unlocked_chk$1;
    if(__n * __size > 18446744073709551615ul)
    {
      return_value___fread_unlocked_chk_warn$2=__fread_unlocked_chk_warn(__ptr, 18446744073709551615ul, __size, __n, __stream);
      return return_value___fread_unlocked_chk_warn$2;
    }

  }

  signed int tmp_if_expr$5;
  signed int return_value___uflow$3;
  char *tmp_post$4;
  char *tmp_post$6;
  if(FALSE)
  {
    if(FALSE)
    {
      if((__n | __size) < 4294967296ul)
      {
        if(__n * __size <= 8ul)
        {
          unsigned long int __cnt = __size * __n;
          char *__cptr = (char *)__ptr;
          if(__cnt == 0ul)
            return (unsigned long int)0;

          while(__cnt > 0ul)
          {
            signed int __c;
            if(__stream->_IO_read_ptr >= __stream->_IO_read_end)
            {
              return_value___uflow$3=__uflow(__stream);
              tmp_if_expr$5 = return_value___uflow$3;
            }

            else
            {
              tmp_post$4 = __stream->_IO_read_ptr;
              __stream->_IO_read_ptr = __stream->_IO_read_ptr + 1l;
              tmp_if_expr$5 = (signed int)*((unsigned char *)tmp_post$4);
            }
            __c = tmp_if_expr$5;
            if(!(__c == -1))
              goto __CPROVER_DUMP_L8;

            goto __CPROVER_DUMP_L9;

          __CPROVER_DUMP_L8:
            ;
            tmp_post$6 = __cptr;
            __cptr = __cptr + 1l;
            *tmp_post$6 = (char)__c;
            __cnt = __cnt - 1ul;
          }

        __CPROVER_DUMP_L9:
          ;
          return (unsigned long int)(__cptr - (char *)__ptr) / __size;
        }

      }

    }

  }

  unsigned long int return_value___fread_unlocked_alias$7;
  return_value___fread_unlocked_alias$7=__fread_unlocked_alias(__ptr, __size, __n, __stream);
  return return_value___fread_unlocked_alias$7;
}

// c::getc_unlocked
// file /usr/include/x86_64-linux-gnu/bits/stdio.h line 63
signed int getc_unlocked(struct _IO_FILE *__fp)
{
  signed int tmp_if_expr$3;
  signed int return_value___uflow$1;
  char *tmp_post$2;
  if(__fp->_IO_read_ptr >= __fp->_IO_read_end)
  {
    return_value___uflow$1=__uflow(__fp);
    tmp_if_expr$3 = return_value___uflow$1;
  }

  else
  {
    tmp_post$2 = __fp->_IO_read_ptr;
    __fp->_IO_read_ptr = __fp->_IO_read_ptr + 1l;
    tmp_if_expr$3 = (signed int)*((unsigned char *)tmp_post$2);
  }
  return tmp_if_expr$3;
}

// c::getchar
// file /usr/include/x86_64-linux-gnu/bits/stdio.h line 44
signed int getchar(void)
{
  signed int return_value__IO_getc$1;
  return_value__IO_getc$1=_IO_getc(stdin);
  return return_value__IO_getc$1;
}

// c::getchar_unlocked
// file /usr/include/x86_64-linux-gnu/bits/stdio.h line 70
signed int getchar_unlocked(void)
{
  signed int tmp_if_expr$3;
  signed int return_value___uflow$1;
  char *tmp_post$2;
  if(stdin->_IO_read_ptr >= stdin->_IO_read_end)
  {
    return_value___uflow$1=__uflow(stdin);
    tmp_if_expr$3 = return_value___uflow$1;
  }

  else
  {
    tmp_post$2 = stdin->_IO_read_ptr;
    stdin->_IO_read_ptr = stdin->_IO_read_ptr + 1l;
    tmp_if_expr$3 = (signed int)*((unsigned char *)tmp_post$2);
  }
  return tmp_if_expr$3;
}

// c::getcwd
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 200
char * getcwd(char *__buf, unsigned long int __size)
{
  char *return_value___getcwd_chk$1;
  char *return_value___getcwd_chk_warn$2;
  char *return_value___getcwd_alias$3;
  return_value___getcwd_alias$3=__getcwd_alias(__buf, __size);
  return return_value___getcwd_alias$3;
}

// c::getdomainname
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 373
signed int getdomainname(char *__buf, unsigned long int __buflen)
{
  signed int return_value___getdomainname_chk$1;
  signed int return_value___getdomainname_chk_warn$2;
  signed int return_value___getdomainname_alias$3;
  return_value___getdomainname_alias$3=__getdomainname_alias(__buf, __buflen);
  return return_value___getdomainname_alias$3;
}

// c::getgroups
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 265
signed int getgroups(signed int __size, unsigned int *__list)
{
  signed int return_value___getgroups_chk$1;
  signed int return_value___getgroups_chk_warn$2;
  if(FALSE)
  {

  __CPROVER_DUMP_L1:
    ;
    return_value___getgroups_chk$1=__getgroups_chk(__size, __list, 18446744073709551615ul);
    return return_value___getgroups_chk$1;
    if(4ul /*[[unsigned int]]*/ * (unsigned long int)__size > 18446744073709551615ul)
    {
      return_value___getgroups_chk_warn$2=__getgroups_chk_warn(__size, __list, 18446744073709551615ul);
      return return_value___getgroups_chk_warn$2;
    }

  }

  signed int return_value___getgroups_alias$3;
  return_value___getgroups_alias$3=__getgroups_alias(__size, __list);
  return return_value___getgroups_alias$3;
}

// c::gethostname
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 344
signed int gethostname(char *__buf, unsigned long int __buflen)
{
  signed int return_value___gethostname_chk$1;
  signed int return_value___gethostname_chk_warn$2;
  signed int return_value___gethostname_alias$3;
  return_value___gethostname_alias$3=__gethostname_alias(__buf, __buflen);
  return return_value___gethostname_alias$3;
}

// c::getlogin_r
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 317
signed int getlogin_r(char *__buf, unsigned long int __buflen)
{
  signed int return_value___getlogin_r_chk$1;
  signed int return_value___getlogin_r_chk_warn$2;
  signed int return_value___getlogin_r_alias$3;
  return_value___getlogin_r_alias$3=__getlogin_r_alias(__buf, __buflen);
  return return_value___getlogin_r_alias$3;
}

// c::gets
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 233
char * gets(char *__str)
{
  char *return_value___gets_chk$1;
  char *return_value___gets_warn$2;
  return_value___gets_warn$2=__gets_warn(__str);
  return return_value___gets_warn$2;
}

// c::getwd
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 221
char * getwd(char *__buf)
{
  char *return_value___getwd_chk$1;
  char *return_value___getwd_warn$2;
  return_value___getwd_warn$2=__getwd_warn(__buf);
  return return_value___getwd_warn$2;
}

// c::gnu_dev_major
// file /usr/include/x86_64-linux-gnu/sys/sysmacros.h line 44
unsigned int gnu_dev_major(unsigned long long int __dev)
{
  return (unsigned int)(__dev >> 8 & (unsigned long int)4095 | (unsigned long int)((unsigned int)(__dev >> 32) & (unsigned int)~4095));
}

// c::gnu_dev_makedev
// file /usr/include/x86_64-linux-gnu/sys/sysmacros.h line 56
unsigned long long int gnu_dev_makedev(unsigned int __major, unsigned int __minor)
{
  return (unsigned long int)(__minor & (unsigned int)255 | (__major & (unsigned int)4095) << 8) | (unsigned long long int)(__minor & (unsigned int)~255) << 12 | (unsigned long long int)(__major & (unsigned int)~4095) << 32;
}

// c::gnu_dev_minor
// file /usr/include/x86_64-linux-gnu/sys/sysmacros.h line 50
unsigned int gnu_dev_minor(unsigned long long int __dev)
{
  return (unsigned int)(__dev & (unsigned long int)255 | (unsigned long int)((unsigned int)(__dev >> 12) & (unsigned int)~255));
}

// c::group_of_pictures_header
// file src/gethdr.c line 332
static void group_of_pictures_header(void)
{
  signed int pos;
  if(ld == &base)
  {
    Temporal_Reference_Base = True_Framenum_max + 1;
    Temporal_Reference_GOP_Reset = 1;
  }

  pos = ld->Bitcnt;
  unsigned int return_value_Get_Bits$1;
  return_value_Get_Bits$1=Get_Bits(1);
  drop_flag = (signed int)return_value_Get_Bits$1;
  unsigned int return_value_Get_Bits$2;
  return_value_Get_Bits$2=Get_Bits(5);
  hour = (signed int)return_value_Get_Bits$2;
  unsigned int return_value_Get_Bits$3;
  return_value_Get_Bits$3=Get_Bits(6);
  minute = (signed int)return_value_Get_Bits$3;
  marker_bit("group_of_pictures_header()");
  unsigned int return_value_Get_Bits$4;
  return_value_Get_Bits$4=Get_Bits(6);
  sec = (signed int)return_value_Get_Bits$4;
  unsigned int return_value_Get_Bits$5;
  return_value_Get_Bits$5=Get_Bits(6);
  frame = (signed int)return_value_Get_Bits$5;
  unsigned int return_value_Get_Bits$6;
  return_value_Get_Bits$6=Get_Bits(1);
  closed_gop = (signed int)return_value_Get_Bits$6;
  unsigned int return_value_Get_Bits$7;
  return_value_Get_Bits$7=Get_Bits(1);
  broken_link = (signed int)return_value_Get_Bits$7;
  extension_and_user_data();
}

// c::idct_M128ASM_scalar
// file src/idct.c line 750
static void idct_M128ASM_scalar(signed short int *src)
{
  signed int idct_M128ASM_scalar$$1$$1$$a0;
  signed int idct_M128ASM_scalar$$1$$1$$a1;
  signed int idct_M128ASM_scalar$$1$$1$$a2;
  signed int idct_M128ASM_scalar$$1$$1$$a3;
  signed int idct_M128ASM_scalar$$1$$1$$b0;
  signed int idct_M128ASM_scalar$$1$$1$$b1;
  signed int idct_M128ASM_scalar$$1$$1$$b2;
  signed int idct_M128ASM_scalar$$1$$1$$b3;
  idct_M128ASM_scalar$$1$$1$$a0 = (signed int)src[(signed long int)0] * (signed int)tab_i_04[(signed long int)0] + (signed int)src[(signed long int)2] * (signed int)tab_i_04[(signed long int)1] + (signed int)src[(signed long int)4] * (signed int)tab_i_04[(signed long int)2] + (signed int)src[(signed long int)6] * (signed int)tab_i_04[(signed long int)3];
  idct_M128ASM_scalar$$1$$1$$a1 = (signed int)src[(signed long int)0] * (signed int)tab_i_04[(signed long int)4] + (signed int)src[(signed long int)2] * (signed int)tab_i_04[(signed long int)5] + (signed int)src[(signed long int)4] * (signed int)tab_i_04[(signed long int)6] + (signed int)src[(signed long int)6] * (signed int)tab_i_04[(signed long int)7];
  idct_M128ASM_scalar$$1$$1$$a2 = (signed int)src[(signed long int)0] * (signed int)tab_i_04[(signed long int)8] + (signed int)src[(signed long int)2] * (signed int)tab_i_04[(signed long int)9] + (signed int)src[(signed long int)4] * (signed int)tab_i_04[(signed long int)10] + (signed int)src[(signed long int)6] * (signed int)tab_i_04[(signed long int)11];
  idct_M128ASM_scalar$$1$$1$$a3 = (signed int)src[(signed long int)0] * (signed int)tab_i_04[(signed long int)12] + (signed int)src[(signed long int)2] * (signed int)tab_i_04[(signed long int)13] + (signed int)src[(signed long int)4] * (signed int)tab_i_04[(signed long int)14] + (signed int)src[(signed long int)6] * (signed int)tab_i_04[(signed long int)15];
  idct_M128ASM_scalar$$1$$1$$b0 = (signed int)src[(signed long int)1] * (signed int)tab_i_04[(signed long int)16] + (signed int)src[(signed long int)3] * (signed int)tab_i_04[(signed long int)17] + (signed int)src[(signed long int)5] * (signed int)tab_i_04[(signed long int)18] + (signed int)src[(signed long int)7] * (signed int)tab_i_04[(signed long int)19];
  idct_M128ASM_scalar$$1$$1$$b1 = (signed int)src[(signed long int)1] * (signed int)tab_i_04[(signed long int)20] + (signed int)src[(signed long int)3] * (signed int)tab_i_04[(signed long int)21] + (signed int)src[(signed long int)5] * (signed int)tab_i_04[(signed long int)22] + (signed int)src[(signed long int)7] * (signed int)tab_i_04[(signed long int)23];
  idct_M128ASM_scalar$$1$$1$$b2 = (signed int)src[(signed long int)1] * (signed int)tab_i_04[(signed long int)24] + (signed int)src[(signed long int)3] * (signed int)tab_i_04[(signed long int)25] + (signed int)src[(signed long int)5] * (signed int)tab_i_04[(signed long int)26] + (signed int)src[(signed long int)7] * (signed int)tab_i_04[(signed long int)27];
  idct_M128ASM_scalar$$1$$1$$b3 = (signed int)src[(signed long int)1] * (signed int)tab_i_04[(signed long int)28] + (signed int)src[(signed long int)3] * (signed int)tab_i_04[(signed long int)29] + (signed int)src[(signed long int)5] * (signed int)tab_i_04[(signed long int)30] + (signed int)src[(signed long int)7] * (signed int)tab_i_04[(signed long int)31];
  src[(signed long int)0] = (signed short int)(idct_M128ASM_scalar$$1$$1$$a0 + idct_M128ASM_scalar$$1$$1$$b0 + (signed int)RND_INV_ROW >> 16 - 4);
  src[(signed long int)1] = (signed short int)(idct_M128ASM_scalar$$1$$1$$a1 + idct_M128ASM_scalar$$1$$1$$b1 + (signed int)RND_INV_ROW >> 16 - 4);
  src[(signed long int)2] = (signed short int)(idct_M128ASM_scalar$$1$$1$$a2 + idct_M128ASM_scalar$$1$$1$$b2 + (signed int)RND_INV_ROW >> 16 - 4);
  src[(signed long int)3] = (signed short int)(idct_M128ASM_scalar$$1$$1$$a3 + idct_M128ASM_scalar$$1$$1$$b3 + (signed int)RND_INV_ROW >> 16 - 4);
  src[(signed long int)4] = (signed short int)((idct_M128ASM_scalar$$1$$1$$a3 - idct_M128ASM_scalar$$1$$1$$b3) + (signed int)RND_INV_ROW >> 16 - 4);
  src[(signed long int)5] = (signed short int)((idct_M128ASM_scalar$$1$$1$$a2 - idct_M128ASM_scalar$$1$$1$$b2) + (signed int)RND_INV_ROW >> 16 - 4);
  src[(signed long int)6] = (signed short int)((idct_M128ASM_scalar$$1$$1$$a1 - idct_M128ASM_scalar$$1$$1$$b1) + (signed int)RND_INV_ROW >> 16 - 4);
  src[(signed long int)7] = (signed short int)((idct_M128ASM_scalar$$1$$1$$a0 - idct_M128ASM_scalar$$1$$1$$b0) + (signed int)RND_INV_ROW >> 16 - 4);
  signed int idct_M128ASM_scalar$$1$$2$$a0;
  signed int idct_M128ASM_scalar$$1$$2$$a1;
  signed int idct_M128ASM_scalar$$1$$2$$a2;
  signed int idct_M128ASM_scalar$$1$$2$$a3;
  signed int idct_M128ASM_scalar$$1$$2$$b0;
  signed int idct_M128ASM_scalar$$1$$2$$b1;
  signed int idct_M128ASM_scalar$$1$$2$$b2;
  signed int idct_M128ASM_scalar$$1$$2$$b3;
  idct_M128ASM_scalar$$1$$2$$a0 = (signed int)(src + (signed long int)(8 * 4))[(signed long int)0] * (signed int)tab_i_04[(signed long int)0] + (signed int)(src + (signed long int)(8 * 4))[(signed long int)2] * (signed int)tab_i_04[(signed long int)1] + (signed int)(src + (signed long int)(8 * 4))[(signed long int)4] * (signed int)tab_i_04[(signed long int)2] + (signed int)(src + (signed long int)(8 * 4))[(signed long int)6] * (signed int)tab_i_04[(signed long int)3];
  idct_M128ASM_scalar$$1$$2$$a1 = (signed int)(src + (signed long int)(8 * 4))[(signed long int)0] * (signed int)tab_i_04[(signed long int)4] + (signed int)(src + (signed long int)(8 * 4))[(signed long int)2] * (signed int)tab_i_04[(signed long int)5] + (signed int)(src + (signed long int)(8 * 4))[(signed long int)4] * (signed int)tab_i_04[(signed long int)6] + (signed int)(src + (signed long int)(8 * 4))[(signed long int)6] * (signed int)tab_i_04[(signed long int)7];
  idct_M128ASM_scalar$$1$$2$$a2 = (signed int)(src + (signed long int)(8 * 4))[(signed long int)0] * (signed int)tab_i_04[(signed long int)8] + (signed int)(src + (signed long int)(8 * 4))[(signed long int)2] * (signed int)tab_i_04[(signed long int)9] + (signed int)(src + (signed long int)(8 * 4))[(signed long int)4] * (signed int)tab_i_04[(signed long int)10] + (signed int)(src + (signed long int)(8 * 4))[(signed long int)6] * (signed int)tab_i_04[(signed long int)11];
  idct_M128ASM_scalar$$1$$2$$a3 = (signed int)(src + (signed long int)(8 * 4))[(signed long int)0] * (signed int)tab_i_04[(signed long int)12] + (signed int)(src + (signed long int)(8 * 4))[(signed long int)2] * (signed int)tab_i_04[(signed long int)13] + (signed int)(src + (signed long int)(8 * 4))[(signed long int)4] * (signed int)tab_i_04[(signed long int)14] + (signed int)(src + (signed long int)(8 * 4))[(signed long int)6] * (signed int)tab_i_04[(signed long int)15];
  idct_M128ASM_scalar$$1$$2$$b0 = (signed int)(src + (signed long int)(8 * 4))[(signed long int)1] * (signed int)tab_i_04[(signed long int)16] + (signed int)(src + (signed long int)(8 * 4))[(signed long int)3] * (signed int)tab_i_04[(signed long int)17] + (signed int)(src + (signed long int)(8 * 4))[(signed long int)5] * (signed int)tab_i_04[(signed long int)18] + (signed int)(src + (signed long int)(8 * 4))[(signed long int)7] * (signed int)tab_i_04[(signed long int)19];
  idct_M128ASM_scalar$$1$$2$$b1 = (signed int)(src + (signed long int)(8 * 4))[(signed long int)1] * (signed int)tab_i_04[(signed long int)20] + (signed int)(src + (signed long int)(8 * 4))[(signed long int)3] * (signed int)tab_i_04[(signed long int)21] + (signed int)(src + (signed long int)(8 * 4))[(signed long int)5] * (signed int)tab_i_04[(signed long int)22] + (signed int)(src + (signed long int)(8 * 4))[(signed long int)7] * (signed int)tab_i_04[(signed long int)23];
  idct_M128ASM_scalar$$1$$2$$b2 = (signed int)(src + (signed long int)(8 * 4))[(signed long int)1] * (signed int)tab_i_04[(signed long int)24] + (signed int)(src + (signed long int)(8 * 4))[(signed long int)3] * (signed int)tab_i_04[(signed long int)25] + (signed int)(src + (signed long int)(8 * 4))[(signed long int)5] * (signed int)tab_i_04[(signed long int)26] + (signed int)(src + (signed long int)(8 * 4))[(signed long int)7] * (signed int)tab_i_04[(signed long int)27];
  idct_M128ASM_scalar$$1$$2$$b3 = (signed int)(src + (signed long int)(8 * 4))[(signed long int)1] * (signed int)tab_i_04[(signed long int)28] + (signed int)(src + (signed long int)(8 * 4))[(signed long int)3] * (signed int)tab_i_04[(signed long int)29] + (signed int)(src + (signed long int)(8 * 4))[(signed long int)5] * (signed int)tab_i_04[(signed long int)30] + (signed int)(src + (signed long int)(8 * 4))[(signed long int)7] * (signed int)tab_i_04[(signed long int)31];
  (src + (signed long int)(8 * 4))[(signed long int)0] = (signed short int)(idct_M128ASM_scalar$$1$$2$$a0 + idct_M128ASM_scalar$$1$$2$$b0 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 4))[(signed long int)1] = (signed short int)(idct_M128ASM_scalar$$1$$2$$a1 + idct_M128ASM_scalar$$1$$2$$b1 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 4))[(signed long int)2] = (signed short int)(idct_M128ASM_scalar$$1$$2$$a2 + idct_M128ASM_scalar$$1$$2$$b2 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 4))[(signed long int)3] = (signed short int)(idct_M128ASM_scalar$$1$$2$$a3 + idct_M128ASM_scalar$$1$$2$$b3 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 4))[(signed long int)4] = (signed short int)((idct_M128ASM_scalar$$1$$2$$a3 - idct_M128ASM_scalar$$1$$2$$b3) + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 4))[(signed long int)5] = (signed short int)((idct_M128ASM_scalar$$1$$2$$a2 - idct_M128ASM_scalar$$1$$2$$b2) + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 4))[(signed long int)6] = (signed short int)((idct_M128ASM_scalar$$1$$2$$a1 - idct_M128ASM_scalar$$1$$2$$b1) + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 4))[(signed long int)7] = (signed short int)((idct_M128ASM_scalar$$1$$2$$a0 - idct_M128ASM_scalar$$1$$2$$b0) + (signed int)RND_INV_ROW >> 16 - 4);
  signed int idct_M128ASM_scalar$$1$$3$$a0;
  signed int idct_M128ASM_scalar$$1$$3$$a1;
  signed int idct_M128ASM_scalar$$1$$3$$a2;
  signed int idct_M128ASM_scalar$$1$$3$$a3;
  signed int idct_M128ASM_scalar$$1$$3$$b0;
  signed int idct_M128ASM_scalar$$1$$3$$b1;
  signed int idct_M128ASM_scalar$$1$$3$$b2;
  signed int idct_M128ASM_scalar$$1$$3$$b3;
  idct_M128ASM_scalar$$1$$3$$a0 = (signed int)(src + (signed long int)8)[(signed long int)0] * (signed int)tab_i_17[(signed long int)0] + (signed int)(src + (signed long int)8)[(signed long int)2] * (signed int)tab_i_17[(signed long int)1] + (signed int)(src + (signed long int)8)[(signed long int)4] * (signed int)tab_i_17[(signed long int)2] + (signed int)(src + (signed long int)8)[(signed long int)6] * (signed int)tab_i_17[(signed long int)3];
  idct_M128ASM_scalar$$1$$3$$a1 = (signed int)(src + (signed long int)8)[(signed long int)0] * (signed int)tab_i_17[(signed long int)4] + (signed int)(src + (signed long int)8)[(signed long int)2] * (signed int)tab_i_17[(signed long int)5] + (signed int)(src + (signed long int)8)[(signed long int)4] * (signed int)tab_i_17[(signed long int)6] + (signed int)(src + (signed long int)8)[(signed long int)6] * (signed int)tab_i_17[(signed long int)7];
  idct_M128ASM_scalar$$1$$3$$a2 = (signed int)(src + (signed long int)8)[(signed long int)0] * (signed int)tab_i_17[(signed long int)8] + (signed int)(src + (signed long int)8)[(signed long int)2] * (signed int)tab_i_17[(signed long int)9] + (signed int)(src + (signed long int)8)[(signed long int)4] * (signed int)tab_i_17[(signed long int)10] + (signed int)(src + (signed long int)8)[(signed long int)6] * (signed int)tab_i_17[(signed long int)11];
  idct_M128ASM_scalar$$1$$3$$a3 = (signed int)(src + (signed long int)8)[(signed long int)0] * (signed int)tab_i_17[(signed long int)12] + (signed int)(src + (signed long int)8)[(signed long int)2] * (signed int)tab_i_17[(signed long int)13] + (signed int)(src + (signed long int)8)[(signed long int)4] * (signed int)tab_i_17[(signed long int)14] + (signed int)(src + (signed long int)8)[(signed long int)6] * (signed int)tab_i_17[(signed long int)15];
  idct_M128ASM_scalar$$1$$3$$b0 = (signed int)(src + (signed long int)8)[(signed long int)1] * (signed int)tab_i_17[(signed long int)16] + (signed int)(src + (signed long int)8)[(signed long int)3] * (signed int)tab_i_17[(signed long int)17] + (signed int)(src + (signed long int)8)[(signed long int)5] * (signed int)tab_i_17[(signed long int)18] + (signed int)(src + (signed long int)8)[(signed long int)7] * (signed int)tab_i_17[(signed long int)19];
  idct_M128ASM_scalar$$1$$3$$b1 = (signed int)(src + (signed long int)8)[(signed long int)1] * (signed int)tab_i_17[(signed long int)20] + (signed int)(src + (signed long int)8)[(signed long int)3] * (signed int)tab_i_17[(signed long int)21] + (signed int)(src + (signed long int)8)[(signed long int)5] * (signed int)tab_i_17[(signed long int)22] + (signed int)(src + (signed long int)8)[(signed long int)7] * (signed int)tab_i_17[(signed long int)23];
  idct_M128ASM_scalar$$1$$3$$b2 = (signed int)(src + (signed long int)8)[(signed long int)1] * (signed int)tab_i_17[(signed long int)24] + (signed int)(src + (signed long int)8)[(signed long int)3] * (signed int)tab_i_17[(signed long int)25] + (signed int)(src + (signed long int)8)[(signed long int)5] * (signed int)tab_i_17[(signed long int)26] + (signed int)(src + (signed long int)8)[(signed long int)7] * (signed int)tab_i_17[(signed long int)27];
  idct_M128ASM_scalar$$1$$3$$b3 = (signed int)(src + (signed long int)8)[(signed long int)1] * (signed int)tab_i_17[(signed long int)28] + (signed int)(src + (signed long int)8)[(signed long int)3] * (signed int)tab_i_17[(signed long int)29] + (signed int)(src + (signed long int)8)[(signed long int)5] * (signed int)tab_i_17[(signed long int)30] + (signed int)(src + (signed long int)8)[(signed long int)7] * (signed int)tab_i_17[(signed long int)31];
  (src + (signed long int)8)[(signed long int)0] = (signed short int)(idct_M128ASM_scalar$$1$$3$$a0 + idct_M128ASM_scalar$$1$$3$$b0 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)8)[(signed long int)1] = (signed short int)(idct_M128ASM_scalar$$1$$3$$a1 + idct_M128ASM_scalar$$1$$3$$b1 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)8)[(signed long int)2] = (signed short int)(idct_M128ASM_scalar$$1$$3$$a2 + idct_M128ASM_scalar$$1$$3$$b2 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)8)[(signed long int)3] = (signed short int)(idct_M128ASM_scalar$$1$$3$$a3 + idct_M128ASM_scalar$$1$$3$$b3 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)8)[(signed long int)4] = (signed short int)((idct_M128ASM_scalar$$1$$3$$a3 - idct_M128ASM_scalar$$1$$3$$b3) + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)8)[(signed long int)5] = (signed short int)((idct_M128ASM_scalar$$1$$3$$a2 - idct_M128ASM_scalar$$1$$3$$b2) + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)8)[(signed long int)6] = (signed short int)((idct_M128ASM_scalar$$1$$3$$a1 - idct_M128ASM_scalar$$1$$3$$b1) + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)8)[(signed long int)7] = (signed short int)((idct_M128ASM_scalar$$1$$3$$a0 - idct_M128ASM_scalar$$1$$3$$b0) + (signed int)RND_INV_ROW >> 16 - 4);
  signed int idct_M128ASM_scalar$$1$$4$$a0;
  signed int idct_M128ASM_scalar$$1$$4$$a1;
  signed int idct_M128ASM_scalar$$1$$4$$a2;
  signed int idct_M128ASM_scalar$$1$$4$$a3;
  signed int idct_M128ASM_scalar$$1$$4$$b0;
  signed int idct_M128ASM_scalar$$1$$4$$b1;
  signed int idct_M128ASM_scalar$$1$$4$$b2;
  signed int idct_M128ASM_scalar$$1$$4$$b3;
  idct_M128ASM_scalar$$1$$4$$a0 = (signed int)(src + (signed long int)(8 * 7))[(signed long int)0] * (signed int)tab_i_17[(signed long int)0] + (signed int)(src + (signed long int)(8 * 7))[(signed long int)2] * (signed int)tab_i_17[(signed long int)1] + (signed int)(src + (signed long int)(8 * 7))[(signed long int)4] * (signed int)tab_i_17[(signed long int)2] + (signed int)(src + (signed long int)(8 * 7))[(signed long int)6] * (signed int)tab_i_17[(signed long int)3];
  idct_M128ASM_scalar$$1$$4$$a1 = (signed int)(src + (signed long int)(8 * 7))[(signed long int)0] * (signed int)tab_i_17[(signed long int)4] + (signed int)(src + (signed long int)(8 * 7))[(signed long int)2] * (signed int)tab_i_17[(signed long int)5] + (signed int)(src + (signed long int)(8 * 7))[(signed long int)4] * (signed int)tab_i_17[(signed long int)6] + (signed int)(src + (signed long int)(8 * 7))[(signed long int)6] * (signed int)tab_i_17[(signed long int)7];
  idct_M128ASM_scalar$$1$$4$$a2 = (signed int)(src + (signed long int)(8 * 7))[(signed long int)0] * (signed int)tab_i_17[(signed long int)8] + (signed int)(src + (signed long int)(8 * 7))[(signed long int)2] * (signed int)tab_i_17[(signed long int)9] + (signed int)(src + (signed long int)(8 * 7))[(signed long int)4] * (signed int)tab_i_17[(signed long int)10] + (signed int)(src + (signed long int)(8 * 7))[(signed long int)6] * (signed int)tab_i_17[(signed long int)11];
  idct_M128ASM_scalar$$1$$4$$a3 = (signed int)(src + (signed long int)(8 * 7))[(signed long int)0] * (signed int)tab_i_17[(signed long int)12] + (signed int)(src + (signed long int)(8 * 7))[(signed long int)2] * (signed int)tab_i_17[(signed long int)13] + (signed int)(src + (signed long int)(8 * 7))[(signed long int)4] * (signed int)tab_i_17[(signed long int)14] + (signed int)(src + (signed long int)(8 * 7))[(signed long int)6] * (signed int)tab_i_17[(signed long int)15];
  idct_M128ASM_scalar$$1$$4$$b0 = (signed int)(src + (signed long int)(8 * 7))[(signed long int)1] * (signed int)tab_i_17[(signed long int)16] + (signed int)(src + (signed long int)(8 * 7))[(signed long int)3] * (signed int)tab_i_17[(signed long int)17] + (signed int)(src + (signed long int)(8 * 7))[(signed long int)5] * (signed int)tab_i_17[(signed long int)18] + (signed int)(src + (signed long int)(8 * 7))[(signed long int)7] * (signed int)tab_i_17[(signed long int)19];
  idct_M128ASM_scalar$$1$$4$$b1 = (signed int)(src + (signed long int)(8 * 7))[(signed long int)1] * (signed int)tab_i_17[(signed long int)20] + (signed int)(src + (signed long int)(8 * 7))[(signed long int)3] * (signed int)tab_i_17[(signed long int)21] + (signed int)(src + (signed long int)(8 * 7))[(signed long int)5] * (signed int)tab_i_17[(signed long int)22] + (signed int)(src + (signed long int)(8 * 7))[(signed long int)7] * (signed int)tab_i_17[(signed long int)23];
  idct_M128ASM_scalar$$1$$4$$b2 = (signed int)(src + (signed long int)(8 * 7))[(signed long int)1] * (signed int)tab_i_17[(signed long int)24] + (signed int)(src + (signed long int)(8 * 7))[(signed long int)3] * (signed int)tab_i_17[(signed long int)25] + (signed int)(src + (signed long int)(8 * 7))[(signed long int)5] * (signed int)tab_i_17[(signed long int)26] + (signed int)(src + (signed long int)(8 * 7))[(signed long int)7] * (signed int)tab_i_17[(signed long int)27];
  idct_M128ASM_scalar$$1$$4$$b3 = (signed int)(src + (signed long int)(8 * 7))[(signed long int)1] * (signed int)tab_i_17[(signed long int)28] + (signed int)(src + (signed long int)(8 * 7))[(signed long int)3] * (signed int)tab_i_17[(signed long int)29] + (signed int)(src + (signed long int)(8 * 7))[(signed long int)5] * (signed int)tab_i_17[(signed long int)30] + (signed int)(src + (signed long int)(8 * 7))[(signed long int)7] * (signed int)tab_i_17[(signed long int)31];
  (src + (signed long int)(8 * 7))[(signed long int)0] = (signed short int)(idct_M128ASM_scalar$$1$$4$$a0 + idct_M128ASM_scalar$$1$$4$$b0 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 7))[(signed long int)1] = (signed short int)(idct_M128ASM_scalar$$1$$4$$a1 + idct_M128ASM_scalar$$1$$4$$b1 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 7))[(signed long int)2] = (signed short int)(idct_M128ASM_scalar$$1$$4$$a2 + idct_M128ASM_scalar$$1$$4$$b2 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 7))[(signed long int)3] = (signed short int)(idct_M128ASM_scalar$$1$$4$$a3 + idct_M128ASM_scalar$$1$$4$$b3 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 7))[(signed long int)4] = (signed short int)((idct_M128ASM_scalar$$1$$4$$a3 - idct_M128ASM_scalar$$1$$4$$b3) + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 7))[(signed long int)5] = (signed short int)((idct_M128ASM_scalar$$1$$4$$a2 - idct_M128ASM_scalar$$1$$4$$b2) + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 7))[(signed long int)6] = (signed short int)((idct_M128ASM_scalar$$1$$4$$a1 - idct_M128ASM_scalar$$1$$4$$b1) + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 7))[(signed long int)7] = (signed short int)((idct_M128ASM_scalar$$1$$4$$a0 - idct_M128ASM_scalar$$1$$4$$b0) + (signed int)RND_INV_ROW >> 16 - 4);
  signed int idct_M128ASM_scalar$$1$$5$$a0;
  signed int idct_M128ASM_scalar$$1$$5$$a1;
  signed int idct_M128ASM_scalar$$1$$5$$a2;
  signed int idct_M128ASM_scalar$$1$$5$$a3;
  signed int idct_M128ASM_scalar$$1$$5$$b0;
  signed int idct_M128ASM_scalar$$1$$5$$b1;
  signed int idct_M128ASM_scalar$$1$$5$$b2;
  signed int idct_M128ASM_scalar$$1$$5$$b3;
  idct_M128ASM_scalar$$1$$5$$a0 = (signed int)(src + (signed long int)(8 * 2))[(signed long int)0] * (signed int)tab_i_26[(signed long int)0] + (signed int)(src + (signed long int)(8 * 2))[(signed long int)2] * (signed int)tab_i_26[(signed long int)1] + (signed int)(src + (signed long int)(8 * 2))[(signed long int)4] * (signed int)tab_i_26[(signed long int)2] + (signed int)(src + (signed long int)(8 * 2))[(signed long int)6] * (signed int)tab_i_26[(signed long int)3];
  idct_M128ASM_scalar$$1$$5$$a1 = (signed int)(src + (signed long int)(8 * 2))[(signed long int)0] * (signed int)tab_i_26[(signed long int)4] + (signed int)(src + (signed long int)(8 * 2))[(signed long int)2] * (signed int)tab_i_26[(signed long int)5] + (signed int)(src + (signed long int)(8 * 2))[(signed long int)4] * (signed int)tab_i_26[(signed long int)6] + (signed int)(src + (signed long int)(8 * 2))[(signed long int)6] * (signed int)tab_i_26[(signed long int)7];
  idct_M128ASM_scalar$$1$$5$$a2 = (signed int)(src + (signed long int)(8 * 2))[(signed long int)0] * (signed int)tab_i_26[(signed long int)8] + (signed int)(src + (signed long int)(8 * 2))[(signed long int)2] * (signed int)tab_i_26[(signed long int)9] + (signed int)(src + (signed long int)(8 * 2))[(signed long int)4] * (signed int)tab_i_26[(signed long int)10] + (signed int)(src + (signed long int)(8 * 2))[(signed long int)6] * (signed int)tab_i_26[(signed long int)11];
  idct_M128ASM_scalar$$1$$5$$a3 = (signed int)(src + (signed long int)(8 * 2))[(signed long int)0] * (signed int)tab_i_26[(signed long int)12] + (signed int)(src + (signed long int)(8 * 2))[(signed long int)2] * (signed int)tab_i_26[(signed long int)13] + (signed int)(src + (signed long int)(8 * 2))[(signed long int)4] * (signed int)tab_i_26[(signed long int)14] + (signed int)(src + (signed long int)(8 * 2))[(signed long int)6] * (signed int)tab_i_26[(signed long int)15];
  idct_M128ASM_scalar$$1$$5$$b0 = (signed int)(src + (signed long int)(8 * 2))[(signed long int)1] * (signed int)tab_i_26[(signed long int)16] + (signed int)(src + (signed long int)(8 * 2))[(signed long int)3] * (signed int)tab_i_26[(signed long int)17] + (signed int)(src + (signed long int)(8 * 2))[(signed long int)5] * (signed int)tab_i_26[(signed long int)18] + (signed int)(src + (signed long int)(8 * 2))[(signed long int)7] * (signed int)tab_i_26[(signed long int)19];
  idct_M128ASM_scalar$$1$$5$$b1 = (signed int)(src + (signed long int)(8 * 2))[(signed long int)1] * (signed int)tab_i_26[(signed long int)20] + (signed int)(src + (signed long int)(8 * 2))[(signed long int)3] * (signed int)tab_i_26[(signed long int)21] + (signed int)(src + (signed long int)(8 * 2))[(signed long int)5] * (signed int)tab_i_26[(signed long int)22] + (signed int)(src + (signed long int)(8 * 2))[(signed long int)7] * (signed int)tab_i_26[(signed long int)23];
  idct_M128ASM_scalar$$1$$5$$b2 = (signed int)(src + (signed long int)(8 * 2))[(signed long int)1] * (signed int)tab_i_26[(signed long int)24] + (signed int)(src + (signed long int)(8 * 2))[(signed long int)3] * (signed int)tab_i_26[(signed long int)25] + (signed int)(src + (signed long int)(8 * 2))[(signed long int)5] * (signed int)tab_i_26[(signed long int)26] + (signed int)(src + (signed long int)(8 * 2))[(signed long int)7] * (signed int)tab_i_26[(signed long int)27];
  idct_M128ASM_scalar$$1$$5$$b3 = (signed int)(src + (signed long int)(8 * 2))[(signed long int)1] * (signed int)tab_i_26[(signed long int)28] + (signed int)(src + (signed long int)(8 * 2))[(signed long int)3] * (signed int)tab_i_26[(signed long int)29] + (signed int)(src + (signed long int)(8 * 2))[(signed long int)5] * (signed int)tab_i_26[(signed long int)30] + (signed int)(src + (signed long int)(8 * 2))[(signed long int)7] * (signed int)tab_i_26[(signed long int)31];
  (src + (signed long int)(8 * 2))[(signed long int)0] = (signed short int)(idct_M128ASM_scalar$$1$$5$$a0 + idct_M128ASM_scalar$$1$$5$$b0 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 2))[(signed long int)1] = (signed short int)(idct_M128ASM_scalar$$1$$5$$a1 + idct_M128ASM_scalar$$1$$5$$b1 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 2))[(signed long int)2] = (signed short int)(idct_M128ASM_scalar$$1$$5$$a2 + idct_M128ASM_scalar$$1$$5$$b2 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 2))[(signed long int)3] = (signed short int)(idct_M128ASM_scalar$$1$$5$$a3 + idct_M128ASM_scalar$$1$$5$$b3 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 2))[(signed long int)4] = (signed short int)((idct_M128ASM_scalar$$1$$5$$a3 - idct_M128ASM_scalar$$1$$5$$b3) + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 2))[(signed long int)5] = (signed short int)((idct_M128ASM_scalar$$1$$5$$a2 - idct_M128ASM_scalar$$1$$5$$b2) + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 2))[(signed long int)6] = (signed short int)((idct_M128ASM_scalar$$1$$5$$a1 - idct_M128ASM_scalar$$1$$5$$b1) + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 2))[(signed long int)7] = (signed short int)((idct_M128ASM_scalar$$1$$5$$a0 - idct_M128ASM_scalar$$1$$5$$b0) + (signed int)RND_INV_ROW >> 16 - 4);
  signed int idct_M128ASM_scalar$$1$$6$$a0;
  signed int idct_M128ASM_scalar$$1$$6$$a1;
  signed int idct_M128ASM_scalar$$1$$6$$a2;
  signed int idct_M128ASM_scalar$$1$$6$$a3;
  signed int idct_M128ASM_scalar$$1$$6$$b0;
  signed int idct_M128ASM_scalar$$1$$6$$b1;
  signed int idct_M128ASM_scalar$$1$$6$$b2;
  signed int idct_M128ASM_scalar$$1$$6$$b3;
  idct_M128ASM_scalar$$1$$6$$a0 = (signed int)(src + (signed long int)(8 * 6))[(signed long int)0] * (signed int)tab_i_26[(signed long int)0] + (signed int)(src + (signed long int)(8 * 6))[(signed long int)2] * (signed int)tab_i_26[(signed long int)1] + (signed int)(src + (signed long int)(8 * 6))[(signed long int)4] * (signed int)tab_i_26[(signed long int)2] + (signed int)(src + (signed long int)(8 * 6))[(signed long int)6] * (signed int)tab_i_26[(signed long int)3];
  idct_M128ASM_scalar$$1$$6$$a1 = (signed int)(src + (signed long int)(8 * 6))[(signed long int)0] * (signed int)tab_i_26[(signed long int)4] + (signed int)(src + (signed long int)(8 * 6))[(signed long int)2] * (signed int)tab_i_26[(signed long int)5] + (signed int)(src + (signed long int)(8 * 6))[(signed long int)4] * (signed int)tab_i_26[(signed long int)6] + (signed int)(src + (signed long int)(8 * 6))[(signed long int)6] * (signed int)tab_i_26[(signed long int)7];
  idct_M128ASM_scalar$$1$$6$$a2 = (signed int)(src + (signed long int)(8 * 6))[(signed long int)0] * (signed int)tab_i_26[(signed long int)8] + (signed int)(src + (signed long int)(8 * 6))[(signed long int)2] * (signed int)tab_i_26[(signed long int)9] + (signed int)(src + (signed long int)(8 * 6))[(signed long int)4] * (signed int)tab_i_26[(signed long int)10] + (signed int)(src + (signed long int)(8 * 6))[(signed long int)6] * (signed int)tab_i_26[(signed long int)11];
  idct_M128ASM_scalar$$1$$6$$a3 = (signed int)(src + (signed long int)(8 * 6))[(signed long int)0] * (signed int)tab_i_26[(signed long int)12] + (signed int)(src + (signed long int)(8 * 6))[(signed long int)2] * (signed int)tab_i_26[(signed long int)13] + (signed int)(src + (signed long int)(8 * 6))[(signed long int)4] * (signed int)tab_i_26[(signed long int)14] + (signed int)(src + (signed long int)(8 * 6))[(signed long int)6] * (signed int)tab_i_26[(signed long int)15];
  idct_M128ASM_scalar$$1$$6$$b0 = (signed int)(src + (signed long int)(8 * 6))[(signed long int)1] * (signed int)tab_i_26[(signed long int)16] + (signed int)(src + (signed long int)(8 * 6))[(signed long int)3] * (signed int)tab_i_26[(signed long int)17] + (signed int)(src + (signed long int)(8 * 6))[(signed long int)5] * (signed int)tab_i_26[(signed long int)18] + (signed int)(src + (signed long int)(8 * 6))[(signed long int)7] * (signed int)tab_i_26[(signed long int)19];
  idct_M128ASM_scalar$$1$$6$$b1 = (signed int)(src + (signed long int)(8 * 6))[(signed long int)1] * (signed int)tab_i_26[(signed long int)20] + (signed int)(src + (signed long int)(8 * 6))[(signed long int)3] * (signed int)tab_i_26[(signed long int)21] + (signed int)(src + (signed long int)(8 * 6))[(signed long int)5] * (signed int)tab_i_26[(signed long int)22] + (signed int)(src + (signed long int)(8 * 6))[(signed long int)7] * (signed int)tab_i_26[(signed long int)23];
  idct_M128ASM_scalar$$1$$6$$b2 = (signed int)(src + (signed long int)(8 * 6))[(signed long int)1] * (signed int)tab_i_26[(signed long int)24] + (signed int)(src + (signed long int)(8 * 6))[(signed long int)3] * (signed int)tab_i_26[(signed long int)25] + (signed int)(src + (signed long int)(8 * 6))[(signed long int)5] * (signed int)tab_i_26[(signed long int)26] + (signed int)(src + (signed long int)(8 * 6))[(signed long int)7] * (signed int)tab_i_26[(signed long int)27];
  idct_M128ASM_scalar$$1$$6$$b3 = (signed int)(src + (signed long int)(8 * 6))[(signed long int)1] * (signed int)tab_i_26[(signed long int)28] + (signed int)(src + (signed long int)(8 * 6))[(signed long int)3] * (signed int)tab_i_26[(signed long int)29] + (signed int)(src + (signed long int)(8 * 6))[(signed long int)5] * (signed int)tab_i_26[(signed long int)30] + (signed int)(src + (signed long int)(8 * 6))[(signed long int)7] * (signed int)tab_i_26[(signed long int)31];
  (src + (signed long int)(8 * 6))[(signed long int)0] = (signed short int)(idct_M128ASM_scalar$$1$$6$$a0 + idct_M128ASM_scalar$$1$$6$$b0 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 6))[(signed long int)1] = (signed short int)(idct_M128ASM_scalar$$1$$6$$a1 + idct_M128ASM_scalar$$1$$6$$b1 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 6))[(signed long int)2] = (signed short int)(idct_M128ASM_scalar$$1$$6$$a2 + idct_M128ASM_scalar$$1$$6$$b2 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 6))[(signed long int)3] = (signed short int)(idct_M128ASM_scalar$$1$$6$$a3 + idct_M128ASM_scalar$$1$$6$$b3 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 6))[(signed long int)4] = (signed short int)((idct_M128ASM_scalar$$1$$6$$a3 - idct_M128ASM_scalar$$1$$6$$b3) + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 6))[(signed long int)5] = (signed short int)((idct_M128ASM_scalar$$1$$6$$a2 - idct_M128ASM_scalar$$1$$6$$b2) + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 6))[(signed long int)6] = (signed short int)((idct_M128ASM_scalar$$1$$6$$a1 - idct_M128ASM_scalar$$1$$6$$b1) + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 6))[(signed long int)7] = (signed short int)((idct_M128ASM_scalar$$1$$6$$a0 - idct_M128ASM_scalar$$1$$6$$b0) + (signed int)RND_INV_ROW >> 16 - 4);
  signed int idct_M128ASM_scalar$$1$$7$$a0;
  signed int idct_M128ASM_scalar$$1$$7$$a1;
  signed int idct_M128ASM_scalar$$1$$7$$a2;
  signed int idct_M128ASM_scalar$$1$$7$$a3;
  signed int idct_M128ASM_scalar$$1$$7$$b0;
  signed int idct_M128ASM_scalar$$1$$7$$b1;
  signed int idct_M128ASM_scalar$$1$$7$$b2;
  signed int idct_M128ASM_scalar$$1$$7$$b3;
  idct_M128ASM_scalar$$1$$7$$a0 = (signed int)(src + (signed long int)(8 * 3))[(signed long int)0] * (signed int)tab_i_35[(signed long int)0] + (signed int)(src + (signed long int)(8 * 3))[(signed long int)2] * (signed int)tab_i_35[(signed long int)1] + (signed int)(src + (signed long int)(8 * 3))[(signed long int)4] * (signed int)tab_i_35[(signed long int)2] + (signed int)(src + (signed long int)(8 * 3))[(signed long int)6] * (signed int)tab_i_35[(signed long int)3];
  idct_M128ASM_scalar$$1$$7$$a1 = (signed int)(src + (signed long int)(8 * 3))[(signed long int)0] * (signed int)tab_i_35[(signed long int)4] + (signed int)(src + (signed long int)(8 * 3))[(signed long int)2] * (signed int)tab_i_35[(signed long int)5] + (signed int)(src + (signed long int)(8 * 3))[(signed long int)4] * (signed int)tab_i_35[(signed long int)6] + (signed int)(src + (signed long int)(8 * 3))[(signed long int)6] * (signed int)tab_i_35[(signed long int)7];
  idct_M128ASM_scalar$$1$$7$$a2 = (signed int)(src + (signed long int)(8 * 3))[(signed long int)0] * (signed int)tab_i_35[(signed long int)8] + (signed int)(src + (signed long int)(8 * 3))[(signed long int)2] * (signed int)tab_i_35[(signed long int)9] + (signed int)(src + (signed long int)(8 * 3))[(signed long int)4] * (signed int)tab_i_35[(signed long int)10] + (signed int)(src + (signed long int)(8 * 3))[(signed long int)6] * (signed int)tab_i_35[(signed long int)11];
  idct_M128ASM_scalar$$1$$7$$a3 = (signed int)(src + (signed long int)(8 * 3))[(signed long int)0] * (signed int)tab_i_35[(signed long int)12] + (signed int)(src + (signed long int)(8 * 3))[(signed long int)2] * (signed int)tab_i_35[(signed long int)13] + (signed int)(src + (signed long int)(8 * 3))[(signed long int)4] * (signed int)tab_i_35[(signed long int)14] + (signed int)(src + (signed long int)(8 * 3))[(signed long int)6] * (signed int)tab_i_35[(signed long int)15];
  idct_M128ASM_scalar$$1$$7$$b0 = (signed int)(src + (signed long int)(8 * 3))[(signed long int)1] * (signed int)tab_i_35[(signed long int)16] + (signed int)(src + (signed long int)(8 * 3))[(signed long int)3] * (signed int)tab_i_35[(signed long int)17] + (signed int)(src + (signed long int)(8 * 3))[(signed long int)5] * (signed int)tab_i_35[(signed long int)18] + (signed int)(src + (signed long int)(8 * 3))[(signed long int)7] * (signed int)tab_i_35[(signed long int)19];
  idct_M128ASM_scalar$$1$$7$$b1 = (signed int)(src + (signed long int)(8 * 3))[(signed long int)1] * (signed int)tab_i_35[(signed long int)20] + (signed int)(src + (signed long int)(8 * 3))[(signed long int)3] * (signed int)tab_i_35[(signed long int)21] + (signed int)(src + (signed long int)(8 * 3))[(signed long int)5] * (signed int)tab_i_35[(signed long int)22] + (signed int)(src + (signed long int)(8 * 3))[(signed long int)7] * (signed int)tab_i_35[(signed long int)23];
  idct_M128ASM_scalar$$1$$7$$b2 = (signed int)(src + (signed long int)(8 * 3))[(signed long int)1] * (signed int)tab_i_35[(signed long int)24] + (signed int)(src + (signed long int)(8 * 3))[(signed long int)3] * (signed int)tab_i_35[(signed long int)25] + (signed int)(src + (signed long int)(8 * 3))[(signed long int)5] * (signed int)tab_i_35[(signed long int)26] + (signed int)(src + (signed long int)(8 * 3))[(signed long int)7] * (signed int)tab_i_35[(signed long int)27];
  idct_M128ASM_scalar$$1$$7$$b3 = (signed int)(src + (signed long int)(8 * 3))[(signed long int)1] * (signed int)tab_i_35[(signed long int)28] + (signed int)(src + (signed long int)(8 * 3))[(signed long int)3] * (signed int)tab_i_35[(signed long int)29] + (signed int)(src + (signed long int)(8 * 3))[(signed long int)5] * (signed int)tab_i_35[(signed long int)30] + (signed int)(src + (signed long int)(8 * 3))[(signed long int)7] * (signed int)tab_i_35[(signed long int)31];
  (src + (signed long int)(8 * 3))[(signed long int)0] = (signed short int)(idct_M128ASM_scalar$$1$$7$$a0 + idct_M128ASM_scalar$$1$$7$$b0 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 3))[(signed long int)1] = (signed short int)(idct_M128ASM_scalar$$1$$7$$a1 + idct_M128ASM_scalar$$1$$7$$b1 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 3))[(signed long int)2] = (signed short int)(idct_M128ASM_scalar$$1$$7$$a2 + idct_M128ASM_scalar$$1$$7$$b2 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 3))[(signed long int)3] = (signed short int)(idct_M128ASM_scalar$$1$$7$$a3 + idct_M128ASM_scalar$$1$$7$$b3 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 3))[(signed long int)4] = (signed short int)((idct_M128ASM_scalar$$1$$7$$a3 - idct_M128ASM_scalar$$1$$7$$b3) + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 3))[(signed long int)5] = (signed short int)((idct_M128ASM_scalar$$1$$7$$a2 - idct_M128ASM_scalar$$1$$7$$b2) + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 3))[(signed long int)6] = (signed short int)((idct_M128ASM_scalar$$1$$7$$a1 - idct_M128ASM_scalar$$1$$7$$b1) + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 3))[(signed long int)7] = (signed short int)((idct_M128ASM_scalar$$1$$7$$a0 - idct_M128ASM_scalar$$1$$7$$b0) + (signed int)RND_INV_ROW >> 16 - 4);
  signed int idct_M128ASM_scalar$$1$$8$$a0;
  signed int idct_M128ASM_scalar$$1$$8$$a1;
  signed int idct_M128ASM_scalar$$1$$8$$a2;
  signed int idct_M128ASM_scalar$$1$$8$$a3;
  signed int idct_M128ASM_scalar$$1$$8$$b0;
  signed int idct_M128ASM_scalar$$1$$8$$b1;
  signed int idct_M128ASM_scalar$$1$$8$$b2;
  signed int idct_M128ASM_scalar$$1$$8$$b3;
  idct_M128ASM_scalar$$1$$8$$a0 = (signed int)(src + (signed long int)(8 * 5))[(signed long int)0] * (signed int)tab_i_35[(signed long int)0] + (signed int)(src + (signed long int)(8 * 5))[(signed long int)2] * (signed int)tab_i_35[(signed long int)1] + (signed int)(src + (signed long int)(8 * 5))[(signed long int)4] * (signed int)tab_i_35[(signed long int)2] + (signed int)(src + (signed long int)(8 * 5))[(signed long int)6] * (signed int)tab_i_35[(signed long int)3];
  idct_M128ASM_scalar$$1$$8$$a1 = (signed int)(src + (signed long int)(8 * 5))[(signed long int)0] * (signed int)tab_i_35[(signed long int)4] + (signed int)(src + (signed long int)(8 * 5))[(signed long int)2] * (signed int)tab_i_35[(signed long int)5] + (signed int)(src + (signed long int)(8 * 5))[(signed long int)4] * (signed int)tab_i_35[(signed long int)6] + (signed int)(src + (signed long int)(8 * 5))[(signed long int)6] * (signed int)tab_i_35[(signed long int)7];
  idct_M128ASM_scalar$$1$$8$$a2 = (signed int)(src + (signed long int)(8 * 5))[(signed long int)0] * (signed int)tab_i_35[(signed long int)8] + (signed int)(src + (signed long int)(8 * 5))[(signed long int)2] * (signed int)tab_i_35[(signed long int)9] + (signed int)(src + (signed long int)(8 * 5))[(signed long int)4] * (signed int)tab_i_35[(signed long int)10] + (signed int)(src + (signed long int)(8 * 5))[(signed long int)6] * (signed int)tab_i_35[(signed long int)11];
  idct_M128ASM_scalar$$1$$8$$a3 = (signed int)(src + (signed long int)(8 * 5))[(signed long int)0] * (signed int)tab_i_35[(signed long int)12] + (signed int)(src + (signed long int)(8 * 5))[(signed long int)2] * (signed int)tab_i_35[(signed long int)13] + (signed int)(src + (signed long int)(8 * 5))[(signed long int)4] * (signed int)tab_i_35[(signed long int)14] + (signed int)(src + (signed long int)(8 * 5))[(signed long int)6] * (signed int)tab_i_35[(signed long int)15];
  idct_M128ASM_scalar$$1$$8$$b0 = (signed int)(src + (signed long int)(8 * 5))[(signed long int)1] * (signed int)tab_i_35[(signed long int)16] + (signed int)(src + (signed long int)(8 * 5))[(signed long int)3] * (signed int)tab_i_35[(signed long int)17] + (signed int)(src + (signed long int)(8 * 5))[(signed long int)5] * (signed int)tab_i_35[(signed long int)18] + (signed int)(src + (signed long int)(8 * 5))[(signed long int)7] * (signed int)tab_i_35[(signed long int)19];
  idct_M128ASM_scalar$$1$$8$$b1 = (signed int)(src + (signed long int)(8 * 5))[(signed long int)1] * (signed int)tab_i_35[(signed long int)20] + (signed int)(src + (signed long int)(8 * 5))[(signed long int)3] * (signed int)tab_i_35[(signed long int)21] + (signed int)(src + (signed long int)(8 * 5))[(signed long int)5] * (signed int)tab_i_35[(signed long int)22] + (signed int)(src + (signed long int)(8 * 5))[(signed long int)7] * (signed int)tab_i_35[(signed long int)23];
  idct_M128ASM_scalar$$1$$8$$b2 = (signed int)(src + (signed long int)(8 * 5))[(signed long int)1] * (signed int)tab_i_35[(signed long int)24] + (signed int)(src + (signed long int)(8 * 5))[(signed long int)3] * (signed int)tab_i_35[(signed long int)25] + (signed int)(src + (signed long int)(8 * 5))[(signed long int)5] * (signed int)tab_i_35[(signed long int)26] + (signed int)(src + (signed long int)(8 * 5))[(signed long int)7] * (signed int)tab_i_35[(signed long int)27];
  idct_M128ASM_scalar$$1$$8$$b3 = (signed int)(src + (signed long int)(8 * 5))[(signed long int)1] * (signed int)tab_i_35[(signed long int)28] + (signed int)(src + (signed long int)(8 * 5))[(signed long int)3] * (signed int)tab_i_35[(signed long int)29] + (signed int)(src + (signed long int)(8 * 5))[(signed long int)5] * (signed int)tab_i_35[(signed long int)30] + (signed int)(src + (signed long int)(8 * 5))[(signed long int)7] * (signed int)tab_i_35[(signed long int)31];
  (src + (signed long int)(8 * 5))[(signed long int)0] = (signed short int)(idct_M128ASM_scalar$$1$$8$$a0 + idct_M128ASM_scalar$$1$$8$$b0 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 5))[(signed long int)1] = (signed short int)(idct_M128ASM_scalar$$1$$8$$a1 + idct_M128ASM_scalar$$1$$8$$b1 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 5))[(signed long int)2] = (signed short int)(idct_M128ASM_scalar$$1$$8$$a2 + idct_M128ASM_scalar$$1$$8$$b2 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 5))[(signed long int)3] = (signed short int)(idct_M128ASM_scalar$$1$$8$$a3 + idct_M128ASM_scalar$$1$$8$$b3 + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 5))[(signed long int)4] = (signed short int)((idct_M128ASM_scalar$$1$$8$$a3 - idct_M128ASM_scalar$$1$$8$$b3) + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 5))[(signed long int)5] = (signed short int)((idct_M128ASM_scalar$$1$$8$$a2 - idct_M128ASM_scalar$$1$$8$$b2) + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 5))[(signed long int)6] = (signed short int)((idct_M128ASM_scalar$$1$$8$$a1 - idct_M128ASM_scalar$$1$$8$$b1) + (signed int)RND_INV_ROW >> 16 - 4);
  (src + (signed long int)(8 * 5))[(signed long int)7] = (signed short int)((idct_M128ASM_scalar$$1$$8$$a0 - idct_M128ASM_scalar$$1$$8$$b0) + (signed int)RND_INV_ROW >> 16 - 4);
  signed int idct_M128ASM_scalar$$1$$9$$t0;
  signed int idct_M128ASM_scalar$$1$$9$$t1;
  signed int idct_M128ASM_scalar$$1$$9$$t2;
  signed int idct_M128ASM_scalar$$1$$9$$t3;
  signed int idct_M128ASM_scalar$$1$$9$$t4;
  signed int idct_M128ASM_scalar$$1$$9$$t5;
  signed int idct_M128ASM_scalar$$1$$9$$t6;
  signed int idct_M128ASM_scalar$$1$$9$$t7;
  signed int idct_M128ASM_scalar$$1$$9$$tp03;
  signed int idct_M128ASM_scalar$$1$$9$$tm03;
  signed int idct_M128ASM_scalar$$1$$9$$tp12;
  signed int idct_M128ASM_scalar$$1$$9$$tm12;
  signed int idct_M128ASM_scalar$$1$$9$$tp65;
  signed int idct_M128ASM_scalar$$1$$9$$tm65;
  signed int idct_M128ASM_scalar$$1$$9$$tp465;
  signed int idct_M128ASM_scalar$$1$$9$$tm465;
  signed int idct_M128ASM_scalar$$1$$9$$tp765;
  signed int idct_M128ASM_scalar$$1$$9$$tm765;
  idct_M128ASM_scalar$$1$$9$$tp765 = (signed int)src[(signed long int)(8 * 1)] + ((signed int)src[(signed long int)(8 * 7)] * 13036 >> 16);
  idct_M128ASM_scalar$$1$$9$$tp465 = ((signed int)src[(signed long int)(8 * 1)] * 13036 >> 16) - (signed int)src[(signed long int)(8 * 7)];
  idct_M128ASM_scalar$$1$$9$$tm765 = ((signed int)src[(signed long int)(8 * 5)] * -21746 >> 16) + (signed int)src[(signed long int)(8 * 5)] + (signed int)src[(signed long int)(8 * 3)];
  idct_M128ASM_scalar$$1$$9$$tm465 = ((signed int)src[(signed long int)(8 * 5)] - ((signed int)src[(signed long int)(8 * 3)] * -21746 >> 16)) - (signed int)src[(signed long int)(8 * 3)];
  idct_M128ASM_scalar$$1$$9$$t7 = idct_M128ASM_scalar$$1$$9$$tp765 + idct_M128ASM_scalar$$1$$9$$tm765 + 1;
  idct_M128ASM_scalar$$1$$9$$tp65 = idct_M128ASM_scalar$$1$$9$$tp765 - idct_M128ASM_scalar$$1$$9$$tm765;
  idct_M128ASM_scalar$$1$$9$$t4 = idct_M128ASM_scalar$$1$$9$$tp465 + idct_M128ASM_scalar$$1$$9$$tm465;
  idct_M128ASM_scalar$$1$$9$$tm65 = (idct_M128ASM_scalar$$1$$9$$tp465 - idct_M128ASM_scalar$$1$$9$$tm465) + 1;
  idct_M128ASM_scalar$$1$$9$$t6 = (signed int)(idct_M128ASM_scalar$$1$$9$$tp65 + idct_M128ASM_scalar$$1$$9$$tm65) * -19195 >> 16 | 1;
  idct_M128ASM_scalar$$1$$9$$t6 = idct_M128ASM_scalar$$1$$9$$t6 + idct_M128ASM_scalar$$1$$9$$tp65 + idct_M128ASM_scalar$$1$$9$$tm65;
  idct_M128ASM_scalar$$1$$9$$t5 = (signed int)(idct_M128ASM_scalar$$1$$9$$tp65 - idct_M128ASM_scalar$$1$$9$$tm65) * -19195 >> 16 | 1;
  idct_M128ASM_scalar$$1$$9$$t5 = idct_M128ASM_scalar$$1$$9$$t5 + (idct_M128ASM_scalar$$1$$9$$tp65 - idct_M128ASM_scalar$$1$$9$$tm65);
  idct_M128ASM_scalar$$1$$9$$tp03 = (signed int)src[(signed long int)(8 * 0)] + (signed int)src[(signed long int)(8 * 4)];
  idct_M128ASM_scalar$$1$$9$$tp12 = (signed int)src[(signed long int)(8 * 0)] - (signed int)src[(signed long int)(8 * 4)];
  idct_M128ASM_scalar$$1$$9$$tm03 = (signed int)src[(signed long int)(8 * 2)] + ((signed int)src[(signed long int)(8 * 6)] * 27146 >> 16);
  idct_M128ASM_scalar$$1$$9$$tm12 = ((signed int)src[(signed long int)(8 * 2)] * 27146 >> 16) - (signed int)src[(signed long int)(8 * 6)];
  idct_M128ASM_scalar$$1$$9$$t0 = idct_M128ASM_scalar$$1$$9$$tp03 + idct_M128ASM_scalar$$1$$9$$tm03 + 16 * (4 - 3);
  idct_M128ASM_scalar$$1$$9$$t3 = (idct_M128ASM_scalar$$1$$9$$tp03 - idct_M128ASM_scalar$$1$$9$$tm03) + (signed int)RND_INV_CORR;
  idct_M128ASM_scalar$$1$$9$$t1 = idct_M128ASM_scalar$$1$$9$$tp12 + idct_M128ASM_scalar$$1$$9$$tm12 + 16 * (4 - 3);
  idct_M128ASM_scalar$$1$$9$$t2 = (idct_M128ASM_scalar$$1$$9$$tp12 - idct_M128ASM_scalar$$1$$9$$tm12) + (signed int)RND_INV_CORR;
  src[(signed long int)(8 * 0)] = (signed short int)((idct_M128ASM_scalar$$1$$9$$t0 + idct_M128ASM_scalar$$1$$9$$t7 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$9$$t0 + idct_M128ASM_scalar$$1$$9$$t7 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$9$$t0 + idct_M128ASM_scalar$$1$$9$$t7)) >> 1 + 4);
  src[(signed long int)(8 * 7)] = (signed short int)((idct_M128ASM_scalar$$1$$9$$t0 - idct_M128ASM_scalar$$1$$9$$t7 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$9$$t0 - idct_M128ASM_scalar$$1$$9$$t7 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$9$$t0 - idct_M128ASM_scalar$$1$$9$$t7)) >> 1 + 4);
  src[(signed long int)(8 * 1)] = (signed short int)((idct_M128ASM_scalar$$1$$9$$t1 + idct_M128ASM_scalar$$1$$9$$t6 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$9$$t1 + idct_M128ASM_scalar$$1$$9$$t6 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$9$$t1 + idct_M128ASM_scalar$$1$$9$$t6)) >> 1 + 4);
  src[(signed long int)(8 * 6)] = (signed short int)((idct_M128ASM_scalar$$1$$9$$t1 - idct_M128ASM_scalar$$1$$9$$t6 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$9$$t1 - idct_M128ASM_scalar$$1$$9$$t6 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$9$$t1 - idct_M128ASM_scalar$$1$$9$$t6)) >> 1 + 4);
  src[(signed long int)(8 * 2)] = (signed short int)((idct_M128ASM_scalar$$1$$9$$t2 + idct_M128ASM_scalar$$1$$9$$t5 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$9$$t2 + idct_M128ASM_scalar$$1$$9$$t5 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$9$$t2 + idct_M128ASM_scalar$$1$$9$$t5)) >> 1 + 4);
  src[(signed long int)(8 * 5)] = (signed short int)((idct_M128ASM_scalar$$1$$9$$t2 - idct_M128ASM_scalar$$1$$9$$t5 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$9$$t2 - idct_M128ASM_scalar$$1$$9$$t5 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$9$$t2 - idct_M128ASM_scalar$$1$$9$$t5)) >> 1 + 4);
  src[(signed long int)(8 * 3)] = (signed short int)((idct_M128ASM_scalar$$1$$9$$t3 + idct_M128ASM_scalar$$1$$9$$t4 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$9$$t3 + idct_M128ASM_scalar$$1$$9$$t4 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$9$$t3 + idct_M128ASM_scalar$$1$$9$$t4)) >> 1 + 4);
  src[(signed long int)(8 * 4)] = (signed short int)((idct_M128ASM_scalar$$1$$9$$t3 - idct_M128ASM_scalar$$1$$9$$t4 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$9$$t3 - idct_M128ASM_scalar$$1$$9$$t4 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$9$$t3 - idct_M128ASM_scalar$$1$$9$$t4)) >> 1 + 4);
  signed int idct_M128ASM_scalar$$1$$10$$t0;
  signed int idct_M128ASM_scalar$$1$$10$$t1;
  signed int idct_M128ASM_scalar$$1$$10$$t2;
  signed int idct_M128ASM_scalar$$1$$10$$t3;
  signed int idct_M128ASM_scalar$$1$$10$$t4;
  signed int idct_M128ASM_scalar$$1$$10$$t5;
  signed int idct_M128ASM_scalar$$1$$10$$t6;
  signed int idct_M128ASM_scalar$$1$$10$$t7;
  signed int idct_M128ASM_scalar$$1$$10$$tp03;
  signed int idct_M128ASM_scalar$$1$$10$$tm03;
  signed int idct_M128ASM_scalar$$1$$10$$tp12;
  signed int idct_M128ASM_scalar$$1$$10$$tm12;
  signed int idct_M128ASM_scalar$$1$$10$$tp65;
  signed int idct_M128ASM_scalar$$1$$10$$tm65;
  signed int idct_M128ASM_scalar$$1$$10$$tp465;
  signed int idct_M128ASM_scalar$$1$$10$$tm465;
  signed int idct_M128ASM_scalar$$1$$10$$tp765;
  signed int idct_M128ASM_scalar$$1$$10$$tm765;
  idct_M128ASM_scalar$$1$$10$$tp765 = (signed int)(src + (signed long int)1)[(signed long int)(8 * 1)] + ((signed int)(src + (signed long int)1)[(signed long int)(8 * 7)] * 13036 >> 16);
  idct_M128ASM_scalar$$1$$10$$tp465 = ((signed int)(src + (signed long int)1)[(signed long int)(8 * 1)] * 13036 >> 16) - (signed int)(src + (signed long int)1)[(signed long int)(8 * 7)];
  idct_M128ASM_scalar$$1$$10$$tm765 = ((signed int)(src + (signed long int)1)[(signed long int)(8 * 5)] * -21746 >> 16) + (signed int)(src + (signed long int)1)[(signed long int)(8 * 5)] + (signed int)(src + (signed long int)1)[(signed long int)(8 * 3)];
  idct_M128ASM_scalar$$1$$10$$tm465 = ((signed int)(src + (signed long int)1)[(signed long int)(8 * 5)] - ((signed int)(src + (signed long int)1)[(signed long int)(8 * 3)] * -21746 >> 16)) - (signed int)(src + (signed long int)1)[(signed long int)(8 * 3)];
  idct_M128ASM_scalar$$1$$10$$t7 = idct_M128ASM_scalar$$1$$10$$tp765 + idct_M128ASM_scalar$$1$$10$$tm765 + 1;
  idct_M128ASM_scalar$$1$$10$$tp65 = idct_M128ASM_scalar$$1$$10$$tp765 - idct_M128ASM_scalar$$1$$10$$tm765;
  idct_M128ASM_scalar$$1$$10$$t4 = idct_M128ASM_scalar$$1$$10$$tp465 + idct_M128ASM_scalar$$1$$10$$tm465;
  idct_M128ASM_scalar$$1$$10$$tm65 = (idct_M128ASM_scalar$$1$$10$$tp465 - idct_M128ASM_scalar$$1$$10$$tm465) + 1;
  idct_M128ASM_scalar$$1$$10$$t6 = (signed int)(idct_M128ASM_scalar$$1$$10$$tp65 + idct_M128ASM_scalar$$1$$10$$tm65) * -19195 >> 16 | 1;
  idct_M128ASM_scalar$$1$$10$$t6 = idct_M128ASM_scalar$$1$$10$$t6 + idct_M128ASM_scalar$$1$$10$$tp65 + idct_M128ASM_scalar$$1$$10$$tm65;
  idct_M128ASM_scalar$$1$$10$$t5 = (signed int)(idct_M128ASM_scalar$$1$$10$$tp65 - idct_M128ASM_scalar$$1$$10$$tm65) * -19195 >> 16 | 1;
  idct_M128ASM_scalar$$1$$10$$t5 = idct_M128ASM_scalar$$1$$10$$t5 + (idct_M128ASM_scalar$$1$$10$$tp65 - idct_M128ASM_scalar$$1$$10$$tm65);
  idct_M128ASM_scalar$$1$$10$$tp03 = (signed int)(src + (signed long int)1)[(signed long int)(8 * 0)] + (signed int)(src + (signed long int)1)[(signed long int)(8 * 4)];
  idct_M128ASM_scalar$$1$$10$$tp12 = (signed int)(src + (signed long int)1)[(signed long int)(8 * 0)] - (signed int)(src + (signed long int)1)[(signed long int)(8 * 4)];
  idct_M128ASM_scalar$$1$$10$$tm03 = (signed int)(src + (signed long int)1)[(signed long int)(8 * 2)] + ((signed int)(src + (signed long int)1)[(signed long int)(8 * 6)] * 27146 >> 16);
  idct_M128ASM_scalar$$1$$10$$tm12 = ((signed int)(src + (signed long int)1)[(signed long int)(8 * 2)] * 27146 >> 16) - (signed int)(src + (signed long int)1)[(signed long int)(8 * 6)];
  idct_M128ASM_scalar$$1$$10$$t0 = idct_M128ASM_scalar$$1$$10$$tp03 + idct_M128ASM_scalar$$1$$10$$tm03 + 16 * (4 - 3);
  idct_M128ASM_scalar$$1$$10$$t3 = (idct_M128ASM_scalar$$1$$10$$tp03 - idct_M128ASM_scalar$$1$$10$$tm03) + (signed int)RND_INV_CORR;
  idct_M128ASM_scalar$$1$$10$$t1 = idct_M128ASM_scalar$$1$$10$$tp12 + idct_M128ASM_scalar$$1$$10$$tm12 + 16 * (4 - 3);
  idct_M128ASM_scalar$$1$$10$$t2 = (idct_M128ASM_scalar$$1$$10$$tp12 - idct_M128ASM_scalar$$1$$10$$tm12) + (signed int)RND_INV_CORR;
  (src + (signed long int)1)[(signed long int)(8 * 0)] = (signed short int)((idct_M128ASM_scalar$$1$$10$$t0 + idct_M128ASM_scalar$$1$$10$$t7 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$10$$t0 + idct_M128ASM_scalar$$1$$10$$t7 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$10$$t0 + idct_M128ASM_scalar$$1$$10$$t7)) >> 1 + 4);
  (src + (signed long int)1)[(signed long int)(8 * 7)] = (signed short int)((idct_M128ASM_scalar$$1$$10$$t0 - idct_M128ASM_scalar$$1$$10$$t7 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$10$$t0 - idct_M128ASM_scalar$$1$$10$$t7 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$10$$t0 - idct_M128ASM_scalar$$1$$10$$t7)) >> 1 + 4);
  (src + (signed long int)1)[(signed long int)(8 * 1)] = (signed short int)((idct_M128ASM_scalar$$1$$10$$t1 + idct_M128ASM_scalar$$1$$10$$t6 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$10$$t1 + idct_M128ASM_scalar$$1$$10$$t6 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$10$$t1 + idct_M128ASM_scalar$$1$$10$$t6)) >> 1 + 4);
  (src + (signed long int)1)[(signed long int)(8 * 6)] = (signed short int)((idct_M128ASM_scalar$$1$$10$$t1 - idct_M128ASM_scalar$$1$$10$$t6 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$10$$t1 - idct_M128ASM_scalar$$1$$10$$t6 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$10$$t1 - idct_M128ASM_scalar$$1$$10$$t6)) >> 1 + 4);
  (src + (signed long int)1)[(signed long int)(8 * 2)] = (signed short int)((idct_M128ASM_scalar$$1$$10$$t2 + idct_M128ASM_scalar$$1$$10$$t5 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$10$$t2 + idct_M128ASM_scalar$$1$$10$$t5 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$10$$t2 + idct_M128ASM_scalar$$1$$10$$t5)) >> 1 + 4);
  (src + (signed long int)1)[(signed long int)(8 * 5)] = (signed short int)((idct_M128ASM_scalar$$1$$10$$t2 - idct_M128ASM_scalar$$1$$10$$t5 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$10$$t2 - idct_M128ASM_scalar$$1$$10$$t5 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$10$$t2 - idct_M128ASM_scalar$$1$$10$$t5)) >> 1 + 4);
  (src + (signed long int)1)[(signed long int)(8 * 3)] = (signed short int)((idct_M128ASM_scalar$$1$$10$$t3 + idct_M128ASM_scalar$$1$$10$$t4 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$10$$t3 + idct_M128ASM_scalar$$1$$10$$t4 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$10$$t3 + idct_M128ASM_scalar$$1$$10$$t4)) >> 1 + 4);
  (src + (signed long int)1)[(signed long int)(8 * 4)] = (signed short int)((idct_M128ASM_scalar$$1$$10$$t3 - idct_M128ASM_scalar$$1$$10$$t4 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$10$$t3 - idct_M128ASM_scalar$$1$$10$$t4 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$10$$t3 - idct_M128ASM_scalar$$1$$10$$t4)) >> 1 + 4);
  signed int idct_M128ASM_scalar$$1$$11$$t0;
  signed int idct_M128ASM_scalar$$1$$11$$t1;
  signed int idct_M128ASM_scalar$$1$$11$$t2;
  signed int idct_M128ASM_scalar$$1$$11$$t3;
  signed int idct_M128ASM_scalar$$1$$11$$t4;
  signed int idct_M128ASM_scalar$$1$$11$$t5;
  signed int idct_M128ASM_scalar$$1$$11$$t6;
  signed int idct_M128ASM_scalar$$1$$11$$t7;
  signed int idct_M128ASM_scalar$$1$$11$$tp03;
  signed int idct_M128ASM_scalar$$1$$11$$tm03;
  signed int idct_M128ASM_scalar$$1$$11$$tp12;
  signed int idct_M128ASM_scalar$$1$$11$$tm12;
  signed int idct_M128ASM_scalar$$1$$11$$tp65;
  signed int idct_M128ASM_scalar$$1$$11$$tm65;
  signed int idct_M128ASM_scalar$$1$$11$$tp465;
  signed int idct_M128ASM_scalar$$1$$11$$tm465;
  signed int idct_M128ASM_scalar$$1$$11$$tp765;
  signed int idct_M128ASM_scalar$$1$$11$$tm765;
  idct_M128ASM_scalar$$1$$11$$tp765 = (signed int)(src + (signed long int)2)[(signed long int)(8 * 1)] + ((signed int)(src + (signed long int)2)[(signed long int)(8 * 7)] * 13036 >> 16);
  idct_M128ASM_scalar$$1$$11$$tp465 = ((signed int)(src + (signed long int)2)[(signed long int)(8 * 1)] * 13036 >> 16) - (signed int)(src + (signed long int)2)[(signed long int)(8 * 7)];
  idct_M128ASM_scalar$$1$$11$$tm765 = ((signed int)(src + (signed long int)2)[(signed long int)(8 * 5)] * -21746 >> 16) + (signed int)(src + (signed long int)2)[(signed long int)(8 * 5)] + (signed int)(src + (signed long int)2)[(signed long int)(8 * 3)];
  idct_M128ASM_scalar$$1$$11$$tm465 = ((signed int)(src + (signed long int)2)[(signed long int)(8 * 5)] - ((signed int)(src + (signed long int)2)[(signed long int)(8 * 3)] * -21746 >> 16)) - (signed int)(src + (signed long int)2)[(signed long int)(8 * 3)];
  idct_M128ASM_scalar$$1$$11$$t7 = idct_M128ASM_scalar$$1$$11$$tp765 + idct_M128ASM_scalar$$1$$11$$tm765 + 1;
  idct_M128ASM_scalar$$1$$11$$tp65 = idct_M128ASM_scalar$$1$$11$$tp765 - idct_M128ASM_scalar$$1$$11$$tm765;
  idct_M128ASM_scalar$$1$$11$$t4 = idct_M128ASM_scalar$$1$$11$$tp465 + idct_M128ASM_scalar$$1$$11$$tm465;
  idct_M128ASM_scalar$$1$$11$$tm65 = (idct_M128ASM_scalar$$1$$11$$tp465 - idct_M128ASM_scalar$$1$$11$$tm465) + 1;
  idct_M128ASM_scalar$$1$$11$$t6 = (signed int)(idct_M128ASM_scalar$$1$$11$$tp65 + idct_M128ASM_scalar$$1$$11$$tm65) * -19195 >> 16 | 1;
  idct_M128ASM_scalar$$1$$11$$t6 = idct_M128ASM_scalar$$1$$11$$t6 + idct_M128ASM_scalar$$1$$11$$tp65 + idct_M128ASM_scalar$$1$$11$$tm65;
  idct_M128ASM_scalar$$1$$11$$t5 = (signed int)(idct_M128ASM_scalar$$1$$11$$tp65 - idct_M128ASM_scalar$$1$$11$$tm65) * -19195 >> 16 | 1;
  idct_M128ASM_scalar$$1$$11$$t5 = idct_M128ASM_scalar$$1$$11$$t5 + (idct_M128ASM_scalar$$1$$11$$tp65 - idct_M128ASM_scalar$$1$$11$$tm65);
  idct_M128ASM_scalar$$1$$11$$tp03 = (signed int)(src + (signed long int)2)[(signed long int)(8 * 0)] + (signed int)(src + (signed long int)2)[(signed long int)(8 * 4)];
  idct_M128ASM_scalar$$1$$11$$tp12 = (signed int)(src + (signed long int)2)[(signed long int)(8 * 0)] - (signed int)(src + (signed long int)2)[(signed long int)(8 * 4)];
  idct_M128ASM_scalar$$1$$11$$tm03 = (signed int)(src + (signed long int)2)[(signed long int)(8 * 2)] + ((signed int)(src + (signed long int)2)[(signed long int)(8 * 6)] * 27146 >> 16);
  idct_M128ASM_scalar$$1$$11$$tm12 = ((signed int)(src + (signed long int)2)[(signed long int)(8 * 2)] * 27146 >> 16) - (signed int)(src + (signed long int)2)[(signed long int)(8 * 6)];
  idct_M128ASM_scalar$$1$$11$$t0 = idct_M128ASM_scalar$$1$$11$$tp03 + idct_M128ASM_scalar$$1$$11$$tm03 + 16 * (4 - 3);
  idct_M128ASM_scalar$$1$$11$$t3 = (idct_M128ASM_scalar$$1$$11$$tp03 - idct_M128ASM_scalar$$1$$11$$tm03) + (signed int)RND_INV_CORR;
  idct_M128ASM_scalar$$1$$11$$t1 = idct_M128ASM_scalar$$1$$11$$tp12 + idct_M128ASM_scalar$$1$$11$$tm12 + 16 * (4 - 3);
  idct_M128ASM_scalar$$1$$11$$t2 = (idct_M128ASM_scalar$$1$$11$$tp12 - idct_M128ASM_scalar$$1$$11$$tm12) + (signed int)RND_INV_CORR;
  (src + (signed long int)2)[(signed long int)(8 * 0)] = (signed short int)((idct_M128ASM_scalar$$1$$11$$t0 + idct_M128ASM_scalar$$1$$11$$t7 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$11$$t0 + idct_M128ASM_scalar$$1$$11$$t7 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$11$$t0 + idct_M128ASM_scalar$$1$$11$$t7)) >> 1 + 4);
  (src + (signed long int)2)[(signed long int)(8 * 7)] = (signed short int)((idct_M128ASM_scalar$$1$$11$$t0 - idct_M128ASM_scalar$$1$$11$$t7 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$11$$t0 - idct_M128ASM_scalar$$1$$11$$t7 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$11$$t0 - idct_M128ASM_scalar$$1$$11$$t7)) >> 1 + 4);
  (src + (signed long int)2)[(signed long int)(8 * 1)] = (signed short int)((idct_M128ASM_scalar$$1$$11$$t1 + idct_M128ASM_scalar$$1$$11$$t6 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$11$$t1 + idct_M128ASM_scalar$$1$$11$$t6 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$11$$t1 + idct_M128ASM_scalar$$1$$11$$t6)) >> 1 + 4);
  (src + (signed long int)2)[(signed long int)(8 * 6)] = (signed short int)((idct_M128ASM_scalar$$1$$11$$t1 - idct_M128ASM_scalar$$1$$11$$t6 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$11$$t1 - idct_M128ASM_scalar$$1$$11$$t6 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$11$$t1 - idct_M128ASM_scalar$$1$$11$$t6)) >> 1 + 4);
  (src + (signed long int)2)[(signed long int)(8 * 2)] = (signed short int)((idct_M128ASM_scalar$$1$$11$$t2 + idct_M128ASM_scalar$$1$$11$$t5 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$11$$t2 + idct_M128ASM_scalar$$1$$11$$t5 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$11$$t2 + idct_M128ASM_scalar$$1$$11$$t5)) >> 1 + 4);
  (src + (signed long int)2)[(signed long int)(8 * 5)] = (signed short int)((idct_M128ASM_scalar$$1$$11$$t2 - idct_M128ASM_scalar$$1$$11$$t5 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$11$$t2 - idct_M128ASM_scalar$$1$$11$$t5 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$11$$t2 - idct_M128ASM_scalar$$1$$11$$t5)) >> 1 + 4);
  (src + (signed long int)2)[(signed long int)(8 * 3)] = (signed short int)((idct_M128ASM_scalar$$1$$11$$t3 + idct_M128ASM_scalar$$1$$11$$t4 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$11$$t3 + idct_M128ASM_scalar$$1$$11$$t4 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$11$$t3 + idct_M128ASM_scalar$$1$$11$$t4)) >> 1 + 4);
  (src + (signed long int)2)[(signed long int)(8 * 4)] = (signed short int)((idct_M128ASM_scalar$$1$$11$$t3 - idct_M128ASM_scalar$$1$$11$$t4 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$11$$t3 - idct_M128ASM_scalar$$1$$11$$t4 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$11$$t3 - idct_M128ASM_scalar$$1$$11$$t4)) >> 1 + 4);
  signed int idct_M128ASM_scalar$$1$$12$$t0;
  signed int idct_M128ASM_scalar$$1$$12$$t1;
  signed int idct_M128ASM_scalar$$1$$12$$t2;
  signed int idct_M128ASM_scalar$$1$$12$$t3;
  signed int idct_M128ASM_scalar$$1$$12$$t4;
  signed int idct_M128ASM_scalar$$1$$12$$t5;
  signed int idct_M128ASM_scalar$$1$$12$$t6;
  signed int idct_M128ASM_scalar$$1$$12$$t7;
  signed int idct_M128ASM_scalar$$1$$12$$tp03;
  signed int idct_M128ASM_scalar$$1$$12$$tm03;
  signed int idct_M128ASM_scalar$$1$$12$$tp12;
  signed int idct_M128ASM_scalar$$1$$12$$tm12;
  signed int idct_M128ASM_scalar$$1$$12$$tp65;
  signed int idct_M128ASM_scalar$$1$$12$$tm65;
  signed int idct_M128ASM_scalar$$1$$12$$tp465;
  signed int idct_M128ASM_scalar$$1$$12$$tm465;
  signed int idct_M128ASM_scalar$$1$$12$$tp765;
  signed int idct_M128ASM_scalar$$1$$12$$tm765;
  idct_M128ASM_scalar$$1$$12$$tp765 = (signed int)(src + (signed long int)3)[(signed long int)(8 * 1)] + ((signed int)(src + (signed long int)3)[(signed long int)(8 * 7)] * 13036 >> 16);
  idct_M128ASM_scalar$$1$$12$$tp465 = ((signed int)(src + (signed long int)3)[(signed long int)(8 * 1)] * 13036 >> 16) - (signed int)(src + (signed long int)3)[(signed long int)(8 * 7)];
  idct_M128ASM_scalar$$1$$12$$tm765 = ((signed int)(src + (signed long int)3)[(signed long int)(8 * 5)] * -21746 >> 16) + (signed int)(src + (signed long int)3)[(signed long int)(8 * 5)] + (signed int)(src + (signed long int)3)[(signed long int)(8 * 3)];
  idct_M128ASM_scalar$$1$$12$$tm465 = ((signed int)(src + (signed long int)3)[(signed long int)(8 * 5)] - ((signed int)(src + (signed long int)3)[(signed long int)(8 * 3)] * -21746 >> 16)) - (signed int)(src + (signed long int)3)[(signed long int)(8 * 3)];
  idct_M128ASM_scalar$$1$$12$$t7 = idct_M128ASM_scalar$$1$$12$$tp765 + idct_M128ASM_scalar$$1$$12$$tm765 + 1;
  idct_M128ASM_scalar$$1$$12$$tp65 = idct_M128ASM_scalar$$1$$12$$tp765 - idct_M128ASM_scalar$$1$$12$$tm765;
  idct_M128ASM_scalar$$1$$12$$t4 = idct_M128ASM_scalar$$1$$12$$tp465 + idct_M128ASM_scalar$$1$$12$$tm465;
  idct_M128ASM_scalar$$1$$12$$tm65 = (idct_M128ASM_scalar$$1$$12$$tp465 - idct_M128ASM_scalar$$1$$12$$tm465) + 1;
  idct_M128ASM_scalar$$1$$12$$t6 = (signed int)(idct_M128ASM_scalar$$1$$12$$tp65 + idct_M128ASM_scalar$$1$$12$$tm65) * -19195 >> 16 | 1;
  idct_M128ASM_scalar$$1$$12$$t6 = idct_M128ASM_scalar$$1$$12$$t6 + idct_M128ASM_scalar$$1$$12$$tp65 + idct_M128ASM_scalar$$1$$12$$tm65;
  idct_M128ASM_scalar$$1$$12$$t5 = (signed int)(idct_M128ASM_scalar$$1$$12$$tp65 - idct_M128ASM_scalar$$1$$12$$tm65) * -19195 >> 16 | 1;
  idct_M128ASM_scalar$$1$$12$$t5 = idct_M128ASM_scalar$$1$$12$$t5 + (idct_M128ASM_scalar$$1$$12$$tp65 - idct_M128ASM_scalar$$1$$12$$tm65);
  idct_M128ASM_scalar$$1$$12$$tp03 = (signed int)(src + (signed long int)3)[(signed long int)(8 * 0)] + (signed int)(src + (signed long int)3)[(signed long int)(8 * 4)];
  idct_M128ASM_scalar$$1$$12$$tp12 = (signed int)(src + (signed long int)3)[(signed long int)(8 * 0)] - (signed int)(src + (signed long int)3)[(signed long int)(8 * 4)];
  idct_M128ASM_scalar$$1$$12$$tm03 = (signed int)(src + (signed long int)3)[(signed long int)(8 * 2)] + ((signed int)(src + (signed long int)3)[(signed long int)(8 * 6)] * 27146 >> 16);
  idct_M128ASM_scalar$$1$$12$$tm12 = ((signed int)(src + (signed long int)3)[(signed long int)(8 * 2)] * 27146 >> 16) - (signed int)(src + (signed long int)3)[(signed long int)(8 * 6)];
  idct_M128ASM_scalar$$1$$12$$t0 = idct_M128ASM_scalar$$1$$12$$tp03 + idct_M128ASM_scalar$$1$$12$$tm03 + 16 * (4 - 3);
  idct_M128ASM_scalar$$1$$12$$t3 = (idct_M128ASM_scalar$$1$$12$$tp03 - idct_M128ASM_scalar$$1$$12$$tm03) + (signed int)RND_INV_CORR;
  idct_M128ASM_scalar$$1$$12$$t1 = idct_M128ASM_scalar$$1$$12$$tp12 + idct_M128ASM_scalar$$1$$12$$tm12 + 16 * (4 - 3);
  idct_M128ASM_scalar$$1$$12$$t2 = (idct_M128ASM_scalar$$1$$12$$tp12 - idct_M128ASM_scalar$$1$$12$$tm12) + (signed int)RND_INV_CORR;
  (src + (signed long int)3)[(signed long int)(8 * 0)] = (signed short int)((idct_M128ASM_scalar$$1$$12$$t0 + idct_M128ASM_scalar$$1$$12$$t7 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$12$$t0 + idct_M128ASM_scalar$$1$$12$$t7 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$12$$t0 + idct_M128ASM_scalar$$1$$12$$t7)) >> 1 + 4);
  (src + (signed long int)3)[(signed long int)(8 * 7)] = (signed short int)((idct_M128ASM_scalar$$1$$12$$t0 - idct_M128ASM_scalar$$1$$12$$t7 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$12$$t0 - idct_M128ASM_scalar$$1$$12$$t7 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$12$$t0 - idct_M128ASM_scalar$$1$$12$$t7)) >> 1 + 4);
  (src + (signed long int)3)[(signed long int)(8 * 1)] = (signed short int)((idct_M128ASM_scalar$$1$$12$$t1 + idct_M128ASM_scalar$$1$$12$$t6 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$12$$t1 + idct_M128ASM_scalar$$1$$12$$t6 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$12$$t1 + idct_M128ASM_scalar$$1$$12$$t6)) >> 1 + 4);
  (src + (signed long int)3)[(signed long int)(8 * 6)] = (signed short int)((idct_M128ASM_scalar$$1$$12$$t1 - idct_M128ASM_scalar$$1$$12$$t6 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$12$$t1 - idct_M128ASM_scalar$$1$$12$$t6 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$12$$t1 - idct_M128ASM_scalar$$1$$12$$t6)) >> 1 + 4);
  (src + (signed long int)3)[(signed long int)(8 * 2)] = (signed short int)((idct_M128ASM_scalar$$1$$12$$t2 + idct_M128ASM_scalar$$1$$12$$t5 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$12$$t2 + idct_M128ASM_scalar$$1$$12$$t5 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$12$$t2 + idct_M128ASM_scalar$$1$$12$$t5)) >> 1 + 4);
  (src + (signed long int)3)[(signed long int)(8 * 5)] = (signed short int)((idct_M128ASM_scalar$$1$$12$$t2 - idct_M128ASM_scalar$$1$$12$$t5 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$12$$t2 - idct_M128ASM_scalar$$1$$12$$t5 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$12$$t2 - idct_M128ASM_scalar$$1$$12$$t5)) >> 1 + 4);
  (src + (signed long int)3)[(signed long int)(8 * 3)] = (signed short int)((idct_M128ASM_scalar$$1$$12$$t3 + idct_M128ASM_scalar$$1$$12$$t4 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$12$$t3 + idct_M128ASM_scalar$$1$$12$$t4 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$12$$t3 + idct_M128ASM_scalar$$1$$12$$t4)) >> 1 + 4);
  (src + (signed long int)3)[(signed long int)(8 * 4)] = (signed short int)((idct_M128ASM_scalar$$1$$12$$t3 - idct_M128ASM_scalar$$1$$12$$t4 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$12$$t3 - idct_M128ASM_scalar$$1$$12$$t4 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$12$$t3 - idct_M128ASM_scalar$$1$$12$$t4)) >> 1 + 4);
  signed int idct_M128ASM_scalar$$1$$13$$t0;
  signed int idct_M128ASM_scalar$$1$$13$$t1;
  signed int idct_M128ASM_scalar$$1$$13$$t2;
  signed int idct_M128ASM_scalar$$1$$13$$t3;
  signed int idct_M128ASM_scalar$$1$$13$$t4;
  signed int idct_M128ASM_scalar$$1$$13$$t5;
  signed int idct_M128ASM_scalar$$1$$13$$t6;
  signed int idct_M128ASM_scalar$$1$$13$$t7;
  signed int idct_M128ASM_scalar$$1$$13$$tp03;
  signed int idct_M128ASM_scalar$$1$$13$$tm03;
  signed int idct_M128ASM_scalar$$1$$13$$tp12;
  signed int idct_M128ASM_scalar$$1$$13$$tm12;
  signed int idct_M128ASM_scalar$$1$$13$$tp65;
  signed int idct_M128ASM_scalar$$1$$13$$tm65;
  signed int idct_M128ASM_scalar$$1$$13$$tp465;
  signed int idct_M128ASM_scalar$$1$$13$$tm465;
  signed int idct_M128ASM_scalar$$1$$13$$tp765;
  signed int idct_M128ASM_scalar$$1$$13$$tm765;
  idct_M128ASM_scalar$$1$$13$$tp765 = (signed int)(src + (signed long int)4)[(signed long int)(8 * 1)] + ((signed int)(src + (signed long int)4)[(signed long int)(8 * 7)] * 13036 >> 16);
  idct_M128ASM_scalar$$1$$13$$tp465 = ((signed int)(src + (signed long int)4)[(signed long int)(8 * 1)] * 13036 >> 16) - (signed int)(src + (signed long int)4)[(signed long int)(8 * 7)];
  idct_M128ASM_scalar$$1$$13$$tm765 = ((signed int)(src + (signed long int)4)[(signed long int)(8 * 5)] * -21746 >> 16) + (signed int)(src + (signed long int)4)[(signed long int)(8 * 5)] + (signed int)(src + (signed long int)4)[(signed long int)(8 * 3)];
  idct_M128ASM_scalar$$1$$13$$tm465 = ((signed int)(src + (signed long int)4)[(signed long int)(8 * 5)] - ((signed int)(src + (signed long int)4)[(signed long int)(8 * 3)] * -21746 >> 16)) - (signed int)(src + (signed long int)4)[(signed long int)(8 * 3)];
  idct_M128ASM_scalar$$1$$13$$t7 = idct_M128ASM_scalar$$1$$13$$tp765 + idct_M128ASM_scalar$$1$$13$$tm765 + 1;
  idct_M128ASM_scalar$$1$$13$$tp65 = idct_M128ASM_scalar$$1$$13$$tp765 - idct_M128ASM_scalar$$1$$13$$tm765;
  idct_M128ASM_scalar$$1$$13$$t4 = idct_M128ASM_scalar$$1$$13$$tp465 + idct_M128ASM_scalar$$1$$13$$tm465;
  idct_M128ASM_scalar$$1$$13$$tm65 = (idct_M128ASM_scalar$$1$$13$$tp465 - idct_M128ASM_scalar$$1$$13$$tm465) + 1;
  idct_M128ASM_scalar$$1$$13$$t6 = (signed int)(idct_M128ASM_scalar$$1$$13$$tp65 + idct_M128ASM_scalar$$1$$13$$tm65) * -19195 >> 16 | 1;
  idct_M128ASM_scalar$$1$$13$$t6 = idct_M128ASM_scalar$$1$$13$$t6 + idct_M128ASM_scalar$$1$$13$$tp65 + idct_M128ASM_scalar$$1$$13$$tm65;
  idct_M128ASM_scalar$$1$$13$$t5 = (signed int)(idct_M128ASM_scalar$$1$$13$$tp65 - idct_M128ASM_scalar$$1$$13$$tm65) * -19195 >> 16 | 1;
  idct_M128ASM_scalar$$1$$13$$t5 = idct_M128ASM_scalar$$1$$13$$t5 + (idct_M128ASM_scalar$$1$$13$$tp65 - idct_M128ASM_scalar$$1$$13$$tm65);
  idct_M128ASM_scalar$$1$$13$$tp03 = (signed int)(src + (signed long int)4)[(signed long int)(8 * 0)] + (signed int)(src + (signed long int)4)[(signed long int)(8 * 4)];
  idct_M128ASM_scalar$$1$$13$$tp12 = (signed int)(src + (signed long int)4)[(signed long int)(8 * 0)] - (signed int)(src + (signed long int)4)[(signed long int)(8 * 4)];
  idct_M128ASM_scalar$$1$$13$$tm03 = (signed int)(src + (signed long int)4)[(signed long int)(8 * 2)] + ((signed int)(src + (signed long int)4)[(signed long int)(8 * 6)] * 27146 >> 16);
  idct_M128ASM_scalar$$1$$13$$tm12 = ((signed int)(src + (signed long int)4)[(signed long int)(8 * 2)] * 27146 >> 16) - (signed int)(src + (signed long int)4)[(signed long int)(8 * 6)];
  idct_M128ASM_scalar$$1$$13$$t0 = idct_M128ASM_scalar$$1$$13$$tp03 + idct_M128ASM_scalar$$1$$13$$tm03 + 16 * (4 - 3);
  idct_M128ASM_scalar$$1$$13$$t3 = (idct_M128ASM_scalar$$1$$13$$tp03 - idct_M128ASM_scalar$$1$$13$$tm03) + (signed int)RND_INV_CORR;
  idct_M128ASM_scalar$$1$$13$$t1 = idct_M128ASM_scalar$$1$$13$$tp12 + idct_M128ASM_scalar$$1$$13$$tm12 + 16 * (4 - 3);
  idct_M128ASM_scalar$$1$$13$$t2 = (idct_M128ASM_scalar$$1$$13$$tp12 - idct_M128ASM_scalar$$1$$13$$tm12) + (signed int)RND_INV_CORR;
  (src + (signed long int)4)[(signed long int)(8 * 0)] = (signed short int)((idct_M128ASM_scalar$$1$$13$$t0 + idct_M128ASM_scalar$$1$$13$$t7 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$13$$t0 + idct_M128ASM_scalar$$1$$13$$t7 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$13$$t0 + idct_M128ASM_scalar$$1$$13$$t7)) >> 1 + 4);
  (src + (signed long int)4)[(signed long int)(8 * 7)] = (signed short int)((idct_M128ASM_scalar$$1$$13$$t0 - idct_M128ASM_scalar$$1$$13$$t7 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$13$$t0 - idct_M128ASM_scalar$$1$$13$$t7 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$13$$t0 - idct_M128ASM_scalar$$1$$13$$t7)) >> 1 + 4);
  (src + (signed long int)4)[(signed long int)(8 * 1)] = (signed short int)((idct_M128ASM_scalar$$1$$13$$t1 + idct_M128ASM_scalar$$1$$13$$t6 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$13$$t1 + idct_M128ASM_scalar$$1$$13$$t6 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$13$$t1 + idct_M128ASM_scalar$$1$$13$$t6)) >> 1 + 4);
  (src + (signed long int)4)[(signed long int)(8 * 6)] = (signed short int)((idct_M128ASM_scalar$$1$$13$$t1 - idct_M128ASM_scalar$$1$$13$$t6 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$13$$t1 - idct_M128ASM_scalar$$1$$13$$t6 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$13$$t1 - idct_M128ASM_scalar$$1$$13$$t6)) >> 1 + 4);
  (src + (signed long int)4)[(signed long int)(8 * 2)] = (signed short int)((idct_M128ASM_scalar$$1$$13$$t2 + idct_M128ASM_scalar$$1$$13$$t5 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$13$$t2 + idct_M128ASM_scalar$$1$$13$$t5 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$13$$t2 + idct_M128ASM_scalar$$1$$13$$t5)) >> 1 + 4);
  (src + (signed long int)4)[(signed long int)(8 * 5)] = (signed short int)((idct_M128ASM_scalar$$1$$13$$t2 - idct_M128ASM_scalar$$1$$13$$t5 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$13$$t2 - idct_M128ASM_scalar$$1$$13$$t5 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$13$$t2 - idct_M128ASM_scalar$$1$$13$$t5)) >> 1 + 4);
  (src + (signed long int)4)[(signed long int)(8 * 3)] = (signed short int)((idct_M128ASM_scalar$$1$$13$$t3 + idct_M128ASM_scalar$$1$$13$$t4 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$13$$t3 + idct_M128ASM_scalar$$1$$13$$t4 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$13$$t3 + idct_M128ASM_scalar$$1$$13$$t4)) >> 1 + 4);
  (src + (signed long int)4)[(signed long int)(8 * 4)] = (signed short int)((idct_M128ASM_scalar$$1$$13$$t3 - idct_M128ASM_scalar$$1$$13$$t4 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$13$$t3 - idct_M128ASM_scalar$$1$$13$$t4 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$13$$t3 - idct_M128ASM_scalar$$1$$13$$t4)) >> 1 + 4);
  signed int idct_M128ASM_scalar$$1$$14$$t0;
  signed int idct_M128ASM_scalar$$1$$14$$t1;
  signed int idct_M128ASM_scalar$$1$$14$$t2;
  signed int idct_M128ASM_scalar$$1$$14$$t3;
  signed int idct_M128ASM_scalar$$1$$14$$t4;
  signed int idct_M128ASM_scalar$$1$$14$$t5;
  signed int idct_M128ASM_scalar$$1$$14$$t6;
  signed int idct_M128ASM_scalar$$1$$14$$t7;
  signed int idct_M128ASM_scalar$$1$$14$$tp03;
  signed int idct_M128ASM_scalar$$1$$14$$tm03;
  signed int idct_M128ASM_scalar$$1$$14$$tp12;
  signed int idct_M128ASM_scalar$$1$$14$$tm12;
  signed int idct_M128ASM_scalar$$1$$14$$tp65;
  signed int idct_M128ASM_scalar$$1$$14$$tm65;
  signed int idct_M128ASM_scalar$$1$$14$$tp465;
  signed int idct_M128ASM_scalar$$1$$14$$tm465;
  signed int idct_M128ASM_scalar$$1$$14$$tp765;
  signed int idct_M128ASM_scalar$$1$$14$$tm765;
  idct_M128ASM_scalar$$1$$14$$tp765 = (signed int)(src + (signed long int)5)[(signed long int)(8 * 1)] + ((signed int)(src + (signed long int)5)[(signed long int)(8 * 7)] * 13036 >> 16);
  idct_M128ASM_scalar$$1$$14$$tp465 = ((signed int)(src + (signed long int)5)[(signed long int)(8 * 1)] * 13036 >> 16) - (signed int)(src + (signed long int)5)[(signed long int)(8 * 7)];
  idct_M128ASM_scalar$$1$$14$$tm765 = ((signed int)(src + (signed long int)5)[(signed long int)(8 * 5)] * -21746 >> 16) + (signed int)(src + (signed long int)5)[(signed long int)(8 * 5)] + (signed int)(src + (signed long int)5)[(signed long int)(8 * 3)];
  idct_M128ASM_scalar$$1$$14$$tm465 = ((signed int)(src + (signed long int)5)[(signed long int)(8 * 5)] - ((signed int)(src + (signed long int)5)[(signed long int)(8 * 3)] * -21746 >> 16)) - (signed int)(src + (signed long int)5)[(signed long int)(8 * 3)];
  idct_M128ASM_scalar$$1$$14$$t7 = idct_M128ASM_scalar$$1$$14$$tp765 + idct_M128ASM_scalar$$1$$14$$tm765 + 1;
  idct_M128ASM_scalar$$1$$14$$tp65 = idct_M128ASM_scalar$$1$$14$$tp765 - idct_M128ASM_scalar$$1$$14$$tm765;
  idct_M128ASM_scalar$$1$$14$$t4 = idct_M128ASM_scalar$$1$$14$$tp465 + idct_M128ASM_scalar$$1$$14$$tm465;
  idct_M128ASM_scalar$$1$$14$$tm65 = (idct_M128ASM_scalar$$1$$14$$tp465 - idct_M128ASM_scalar$$1$$14$$tm465) + 1;
  idct_M128ASM_scalar$$1$$14$$t6 = (signed int)(idct_M128ASM_scalar$$1$$14$$tp65 + idct_M128ASM_scalar$$1$$14$$tm65) * -19195 >> 16 | 1;
  idct_M128ASM_scalar$$1$$14$$t6 = idct_M128ASM_scalar$$1$$14$$t6 + idct_M128ASM_scalar$$1$$14$$tp65 + idct_M128ASM_scalar$$1$$14$$tm65;
  idct_M128ASM_scalar$$1$$14$$t5 = (signed int)(idct_M128ASM_scalar$$1$$14$$tp65 - idct_M128ASM_scalar$$1$$14$$tm65) * -19195 >> 16 | 1;
  idct_M128ASM_scalar$$1$$14$$t5 = idct_M128ASM_scalar$$1$$14$$t5 + (idct_M128ASM_scalar$$1$$14$$tp65 - idct_M128ASM_scalar$$1$$14$$tm65);
  idct_M128ASM_scalar$$1$$14$$tp03 = (signed int)(src + (signed long int)5)[(signed long int)(8 * 0)] + (signed int)(src + (signed long int)5)[(signed long int)(8 * 4)];
  idct_M128ASM_scalar$$1$$14$$tp12 = (signed int)(src + (signed long int)5)[(signed long int)(8 * 0)] - (signed int)(src + (signed long int)5)[(signed long int)(8 * 4)];
  idct_M128ASM_scalar$$1$$14$$tm03 = (signed int)(src + (signed long int)5)[(signed long int)(8 * 2)] + ((signed int)(src + (signed long int)5)[(signed long int)(8 * 6)] * 27146 >> 16);
  idct_M128ASM_scalar$$1$$14$$tm12 = ((signed int)(src + (signed long int)5)[(signed long int)(8 * 2)] * 27146 >> 16) - (signed int)(src + (signed long int)5)[(signed long int)(8 * 6)];
  idct_M128ASM_scalar$$1$$14$$t0 = idct_M128ASM_scalar$$1$$14$$tp03 + idct_M128ASM_scalar$$1$$14$$tm03 + 16 * (4 - 3);
  idct_M128ASM_scalar$$1$$14$$t3 = (idct_M128ASM_scalar$$1$$14$$tp03 - idct_M128ASM_scalar$$1$$14$$tm03) + (signed int)RND_INV_CORR;
  idct_M128ASM_scalar$$1$$14$$t1 = idct_M128ASM_scalar$$1$$14$$tp12 + idct_M128ASM_scalar$$1$$14$$tm12 + 16 * (4 - 3);
  idct_M128ASM_scalar$$1$$14$$t2 = (idct_M128ASM_scalar$$1$$14$$tp12 - idct_M128ASM_scalar$$1$$14$$tm12) + (signed int)RND_INV_CORR;
  (src + (signed long int)5)[(signed long int)(8 * 0)] = (signed short int)((idct_M128ASM_scalar$$1$$14$$t0 + idct_M128ASM_scalar$$1$$14$$t7 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$14$$t0 + idct_M128ASM_scalar$$1$$14$$t7 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$14$$t0 + idct_M128ASM_scalar$$1$$14$$t7)) >> 1 + 4);
  (src + (signed long int)5)[(signed long int)(8 * 7)] = (signed short int)((idct_M128ASM_scalar$$1$$14$$t0 - idct_M128ASM_scalar$$1$$14$$t7 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$14$$t0 - idct_M128ASM_scalar$$1$$14$$t7 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$14$$t0 - idct_M128ASM_scalar$$1$$14$$t7)) >> 1 + 4);
  (src + (signed long int)5)[(signed long int)(8 * 1)] = (signed short int)((idct_M128ASM_scalar$$1$$14$$t1 + idct_M128ASM_scalar$$1$$14$$t6 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$14$$t1 + idct_M128ASM_scalar$$1$$14$$t6 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$14$$t1 + idct_M128ASM_scalar$$1$$14$$t6)) >> 1 + 4);
  (src + (signed long int)5)[(signed long int)(8 * 6)] = (signed short int)((idct_M128ASM_scalar$$1$$14$$t1 - idct_M128ASM_scalar$$1$$14$$t6 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$14$$t1 - idct_M128ASM_scalar$$1$$14$$t6 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$14$$t1 - idct_M128ASM_scalar$$1$$14$$t6)) >> 1 + 4);
  (src + (signed long int)5)[(signed long int)(8 * 2)] = (signed short int)((idct_M128ASM_scalar$$1$$14$$t2 + idct_M128ASM_scalar$$1$$14$$t5 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$14$$t2 + idct_M128ASM_scalar$$1$$14$$t5 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$14$$t2 + idct_M128ASM_scalar$$1$$14$$t5)) >> 1 + 4);
  (src + (signed long int)5)[(signed long int)(8 * 5)] = (signed short int)((idct_M128ASM_scalar$$1$$14$$t2 - idct_M128ASM_scalar$$1$$14$$t5 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$14$$t2 - idct_M128ASM_scalar$$1$$14$$t5 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$14$$t2 - idct_M128ASM_scalar$$1$$14$$t5)) >> 1 + 4);
  (src + (signed long int)5)[(signed long int)(8 * 3)] = (signed short int)((idct_M128ASM_scalar$$1$$14$$t3 + idct_M128ASM_scalar$$1$$14$$t4 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$14$$t3 + idct_M128ASM_scalar$$1$$14$$t4 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$14$$t3 + idct_M128ASM_scalar$$1$$14$$t4)) >> 1 + 4);
  (src + (signed long int)5)[(signed long int)(8 * 4)] = (signed short int)((idct_M128ASM_scalar$$1$$14$$t3 - idct_M128ASM_scalar$$1$$14$$t4 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$14$$t3 - idct_M128ASM_scalar$$1$$14$$t4 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$14$$t3 - idct_M128ASM_scalar$$1$$14$$t4)) >> 1 + 4);
  signed int idct_M128ASM_scalar$$1$$15$$t0;
  signed int idct_M128ASM_scalar$$1$$15$$t1;
  signed int idct_M128ASM_scalar$$1$$15$$t2;
  signed int idct_M128ASM_scalar$$1$$15$$t3;
  signed int idct_M128ASM_scalar$$1$$15$$t4;
  signed int idct_M128ASM_scalar$$1$$15$$t5;
  signed int idct_M128ASM_scalar$$1$$15$$t6;
  signed int idct_M128ASM_scalar$$1$$15$$t7;
  signed int idct_M128ASM_scalar$$1$$15$$tp03;
  signed int idct_M128ASM_scalar$$1$$15$$tm03;
  signed int idct_M128ASM_scalar$$1$$15$$tp12;
  signed int idct_M128ASM_scalar$$1$$15$$tm12;
  signed int idct_M128ASM_scalar$$1$$15$$tp65;
  signed int idct_M128ASM_scalar$$1$$15$$tm65;
  signed int idct_M128ASM_scalar$$1$$15$$tp465;
  signed int idct_M128ASM_scalar$$1$$15$$tm465;
  signed int idct_M128ASM_scalar$$1$$15$$tp765;
  signed int idct_M128ASM_scalar$$1$$15$$tm765;
  idct_M128ASM_scalar$$1$$15$$tp765 = (signed int)(src + (signed long int)6)[(signed long int)(8 * 1)] + ((signed int)(src + (signed long int)6)[(signed long int)(8 * 7)] * 13036 >> 16);
  idct_M128ASM_scalar$$1$$15$$tp465 = ((signed int)(src + (signed long int)6)[(signed long int)(8 * 1)] * 13036 >> 16) - (signed int)(src + (signed long int)6)[(signed long int)(8 * 7)];
  idct_M128ASM_scalar$$1$$15$$tm765 = ((signed int)(src + (signed long int)6)[(signed long int)(8 * 5)] * -21746 >> 16) + (signed int)(src + (signed long int)6)[(signed long int)(8 * 5)] + (signed int)(src + (signed long int)6)[(signed long int)(8 * 3)];
  idct_M128ASM_scalar$$1$$15$$tm465 = ((signed int)(src + (signed long int)6)[(signed long int)(8 * 5)] - ((signed int)(src + (signed long int)6)[(signed long int)(8 * 3)] * -21746 >> 16)) - (signed int)(src + (signed long int)6)[(signed long int)(8 * 3)];
  idct_M128ASM_scalar$$1$$15$$t7 = idct_M128ASM_scalar$$1$$15$$tp765 + idct_M128ASM_scalar$$1$$15$$tm765 + 1;
  idct_M128ASM_scalar$$1$$15$$tp65 = idct_M128ASM_scalar$$1$$15$$tp765 - idct_M128ASM_scalar$$1$$15$$tm765;
  idct_M128ASM_scalar$$1$$15$$t4 = idct_M128ASM_scalar$$1$$15$$tp465 + idct_M128ASM_scalar$$1$$15$$tm465;
  idct_M128ASM_scalar$$1$$15$$tm65 = (idct_M128ASM_scalar$$1$$15$$tp465 - idct_M128ASM_scalar$$1$$15$$tm465) + 1;
  idct_M128ASM_scalar$$1$$15$$t6 = (signed int)(idct_M128ASM_scalar$$1$$15$$tp65 + idct_M128ASM_scalar$$1$$15$$tm65) * -19195 >> 16 | 1;
  idct_M128ASM_scalar$$1$$15$$t6 = idct_M128ASM_scalar$$1$$15$$t6 + idct_M128ASM_scalar$$1$$15$$tp65 + idct_M128ASM_scalar$$1$$15$$tm65;
  idct_M128ASM_scalar$$1$$15$$t5 = (signed int)(idct_M128ASM_scalar$$1$$15$$tp65 - idct_M128ASM_scalar$$1$$15$$tm65) * -19195 >> 16 | 1;
  idct_M128ASM_scalar$$1$$15$$t5 = idct_M128ASM_scalar$$1$$15$$t5 + (idct_M128ASM_scalar$$1$$15$$tp65 - idct_M128ASM_scalar$$1$$15$$tm65);
  idct_M128ASM_scalar$$1$$15$$tp03 = (signed int)(src + (signed long int)6)[(signed long int)(8 * 0)] + (signed int)(src + (signed long int)6)[(signed long int)(8 * 4)];
  idct_M128ASM_scalar$$1$$15$$tp12 = (signed int)(src + (signed long int)6)[(signed long int)(8 * 0)] - (signed int)(src + (signed long int)6)[(signed long int)(8 * 4)];
  idct_M128ASM_scalar$$1$$15$$tm03 = (signed int)(src + (signed long int)6)[(signed long int)(8 * 2)] + ((signed int)(src + (signed long int)6)[(signed long int)(8 * 6)] * 27146 >> 16);
  idct_M128ASM_scalar$$1$$15$$tm12 = ((signed int)(src + (signed long int)6)[(signed long int)(8 * 2)] * 27146 >> 16) - (signed int)(src + (signed long int)6)[(signed long int)(8 * 6)];
  idct_M128ASM_scalar$$1$$15$$t0 = idct_M128ASM_scalar$$1$$15$$tp03 + idct_M128ASM_scalar$$1$$15$$tm03 + 16 * (4 - 3);
  idct_M128ASM_scalar$$1$$15$$t3 = (idct_M128ASM_scalar$$1$$15$$tp03 - idct_M128ASM_scalar$$1$$15$$tm03) + (signed int)RND_INV_CORR;
  idct_M128ASM_scalar$$1$$15$$t1 = idct_M128ASM_scalar$$1$$15$$tp12 + idct_M128ASM_scalar$$1$$15$$tm12 + 16 * (4 - 3);
  idct_M128ASM_scalar$$1$$15$$t2 = (idct_M128ASM_scalar$$1$$15$$tp12 - idct_M128ASM_scalar$$1$$15$$tm12) + (signed int)RND_INV_CORR;
  (src + (signed long int)6)[(signed long int)(8 * 0)] = (signed short int)((idct_M128ASM_scalar$$1$$15$$t0 + idct_M128ASM_scalar$$1$$15$$t7 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$15$$t0 + idct_M128ASM_scalar$$1$$15$$t7 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$15$$t0 + idct_M128ASM_scalar$$1$$15$$t7)) >> 1 + 4);
  (src + (signed long int)6)[(signed long int)(8 * 7)] = (signed short int)((idct_M128ASM_scalar$$1$$15$$t0 - idct_M128ASM_scalar$$1$$15$$t7 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$15$$t0 - idct_M128ASM_scalar$$1$$15$$t7 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$15$$t0 - idct_M128ASM_scalar$$1$$15$$t7)) >> 1 + 4);
  (src + (signed long int)6)[(signed long int)(8 * 1)] = (signed short int)((idct_M128ASM_scalar$$1$$15$$t1 + idct_M128ASM_scalar$$1$$15$$t6 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$15$$t1 + idct_M128ASM_scalar$$1$$15$$t6 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$15$$t1 + idct_M128ASM_scalar$$1$$15$$t6)) >> 1 + 4);
  (src + (signed long int)6)[(signed long int)(8 * 6)] = (signed short int)((idct_M128ASM_scalar$$1$$15$$t1 - idct_M128ASM_scalar$$1$$15$$t6 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$15$$t1 - idct_M128ASM_scalar$$1$$15$$t6 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$15$$t1 - idct_M128ASM_scalar$$1$$15$$t6)) >> 1 + 4);
  (src + (signed long int)6)[(signed long int)(8 * 2)] = (signed short int)((idct_M128ASM_scalar$$1$$15$$t2 + idct_M128ASM_scalar$$1$$15$$t5 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$15$$t2 + idct_M128ASM_scalar$$1$$15$$t5 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$15$$t2 + idct_M128ASM_scalar$$1$$15$$t5)) >> 1 + 4);
  (src + (signed long int)6)[(signed long int)(8 * 5)] = (signed short int)((idct_M128ASM_scalar$$1$$15$$t2 - idct_M128ASM_scalar$$1$$15$$t5 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$15$$t2 - idct_M128ASM_scalar$$1$$15$$t5 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$15$$t2 - idct_M128ASM_scalar$$1$$15$$t5)) >> 1 + 4);
  (src + (signed long int)6)[(signed long int)(8 * 3)] = (signed short int)((idct_M128ASM_scalar$$1$$15$$t3 + idct_M128ASM_scalar$$1$$15$$t4 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$15$$t3 + idct_M128ASM_scalar$$1$$15$$t4 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$15$$t3 + idct_M128ASM_scalar$$1$$15$$t4)) >> 1 + 4);
  (src + (signed long int)6)[(signed long int)(8 * 4)] = (signed short int)((idct_M128ASM_scalar$$1$$15$$t3 - idct_M128ASM_scalar$$1$$15$$t4 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$15$$t3 - idct_M128ASM_scalar$$1$$15$$t4 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$15$$t3 - idct_M128ASM_scalar$$1$$15$$t4)) >> 1 + 4);
  signed int idct_M128ASM_scalar$$1$$16$$t0;
  signed int idct_M128ASM_scalar$$1$$16$$t1;
  signed int idct_M128ASM_scalar$$1$$16$$t2;
  signed int idct_M128ASM_scalar$$1$$16$$t3;
  signed int idct_M128ASM_scalar$$1$$16$$t4;
  signed int idct_M128ASM_scalar$$1$$16$$t5;
  signed int idct_M128ASM_scalar$$1$$16$$t6;
  signed int idct_M128ASM_scalar$$1$$16$$t7;
  signed int idct_M128ASM_scalar$$1$$16$$tp03;
  signed int idct_M128ASM_scalar$$1$$16$$tm03;
  signed int idct_M128ASM_scalar$$1$$16$$tp12;
  signed int idct_M128ASM_scalar$$1$$16$$tm12;
  signed int idct_M128ASM_scalar$$1$$16$$tp65;
  signed int idct_M128ASM_scalar$$1$$16$$tm65;
  signed int idct_M128ASM_scalar$$1$$16$$tp465;
  signed int idct_M128ASM_scalar$$1$$16$$tm465;
  signed int idct_M128ASM_scalar$$1$$16$$tp765;
  signed int idct_M128ASM_scalar$$1$$16$$tm765;
  idct_M128ASM_scalar$$1$$16$$tp765 = (signed int)(src + (signed long int)7)[(signed long int)(8 * 1)] + ((signed int)(src + (signed long int)7)[(signed long int)(8 * 7)] * 13036 >> 16);
  idct_M128ASM_scalar$$1$$16$$tp465 = ((signed int)(src + (signed long int)7)[(signed long int)(8 * 1)] * 13036 >> 16) - (signed int)(src + (signed long int)7)[(signed long int)(8 * 7)];
  idct_M128ASM_scalar$$1$$16$$tm765 = ((signed int)(src + (signed long int)7)[(signed long int)(8 * 5)] * -21746 >> 16) + (signed int)(src + (signed long int)7)[(signed long int)(8 * 5)] + (signed int)(src + (signed long int)7)[(signed long int)(8 * 3)];
  idct_M128ASM_scalar$$1$$16$$tm465 = ((signed int)(src + (signed long int)7)[(signed long int)(8 * 5)] - ((signed int)(src + (signed long int)7)[(signed long int)(8 * 3)] * -21746 >> 16)) - (signed int)(src + (signed long int)7)[(signed long int)(8 * 3)];
  idct_M128ASM_scalar$$1$$16$$t7 = idct_M128ASM_scalar$$1$$16$$tp765 + idct_M128ASM_scalar$$1$$16$$tm765 + 1;
  idct_M128ASM_scalar$$1$$16$$tp65 = idct_M128ASM_scalar$$1$$16$$tp765 - idct_M128ASM_scalar$$1$$16$$tm765;
  idct_M128ASM_scalar$$1$$16$$t4 = idct_M128ASM_scalar$$1$$16$$tp465 + idct_M128ASM_scalar$$1$$16$$tm465;
  idct_M128ASM_scalar$$1$$16$$tm65 = (idct_M128ASM_scalar$$1$$16$$tp465 - idct_M128ASM_scalar$$1$$16$$tm465) + 1;
  idct_M128ASM_scalar$$1$$16$$t6 = (signed int)(idct_M128ASM_scalar$$1$$16$$tp65 + idct_M128ASM_scalar$$1$$16$$tm65) * -19195 >> 16 | 1;
  idct_M128ASM_scalar$$1$$16$$t6 = idct_M128ASM_scalar$$1$$16$$t6 + idct_M128ASM_scalar$$1$$16$$tp65 + idct_M128ASM_scalar$$1$$16$$tm65;
  idct_M128ASM_scalar$$1$$16$$t5 = (signed int)(idct_M128ASM_scalar$$1$$16$$tp65 - idct_M128ASM_scalar$$1$$16$$tm65) * -19195 >> 16 | 1;
  idct_M128ASM_scalar$$1$$16$$t5 = idct_M128ASM_scalar$$1$$16$$t5 + (idct_M128ASM_scalar$$1$$16$$tp65 - idct_M128ASM_scalar$$1$$16$$tm65);
  idct_M128ASM_scalar$$1$$16$$tp03 = (signed int)(src + (signed long int)7)[(signed long int)(8 * 0)] + (signed int)(src + (signed long int)7)[(signed long int)(8 * 4)];
  idct_M128ASM_scalar$$1$$16$$tp12 = (signed int)(src + (signed long int)7)[(signed long int)(8 * 0)] - (signed int)(src + (signed long int)7)[(signed long int)(8 * 4)];
  idct_M128ASM_scalar$$1$$16$$tm03 = (signed int)(src + (signed long int)7)[(signed long int)(8 * 2)] + ((signed int)(src + (signed long int)7)[(signed long int)(8 * 6)] * 27146 >> 16);
  idct_M128ASM_scalar$$1$$16$$tm12 = ((signed int)(src + (signed long int)7)[(signed long int)(8 * 2)] * 27146 >> 16) - (signed int)(src + (signed long int)7)[(signed long int)(8 * 6)];
  idct_M128ASM_scalar$$1$$16$$t0 = idct_M128ASM_scalar$$1$$16$$tp03 + idct_M128ASM_scalar$$1$$16$$tm03 + 16 * (4 - 3);
  idct_M128ASM_scalar$$1$$16$$t3 = (idct_M128ASM_scalar$$1$$16$$tp03 - idct_M128ASM_scalar$$1$$16$$tm03) + (signed int)RND_INV_CORR;
  idct_M128ASM_scalar$$1$$16$$t1 = idct_M128ASM_scalar$$1$$16$$tp12 + idct_M128ASM_scalar$$1$$16$$tm12 + 16 * (4 - 3);
  idct_M128ASM_scalar$$1$$16$$t2 = (idct_M128ASM_scalar$$1$$16$$tp12 - idct_M128ASM_scalar$$1$$16$$tm12) + (signed int)RND_INV_CORR;
  (src + (signed long int)7)[(signed long int)(8 * 0)] = (signed short int)((idct_M128ASM_scalar$$1$$16$$t0 + idct_M128ASM_scalar$$1$$16$$t7 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$16$$t0 + idct_M128ASM_scalar$$1$$16$$t7 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$16$$t0 + idct_M128ASM_scalar$$1$$16$$t7)) >> 1 + 4);
  (src + (signed long int)7)[(signed long int)(8 * 7)] = (signed short int)((idct_M128ASM_scalar$$1$$16$$t0 - idct_M128ASM_scalar$$1$$16$$t7 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$16$$t0 - idct_M128ASM_scalar$$1$$16$$t7 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$16$$t0 - idct_M128ASM_scalar$$1$$16$$t7)) >> 1 + 4);
  (src + (signed long int)7)[(signed long int)(8 * 1)] = (signed short int)((idct_M128ASM_scalar$$1$$16$$t1 + idct_M128ASM_scalar$$1$$16$$t6 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$16$$t1 + idct_M128ASM_scalar$$1$$16$$t6 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$16$$t1 + idct_M128ASM_scalar$$1$$16$$t6)) >> 1 + 4);
  (src + (signed long int)7)[(signed long int)(8 * 6)] = (signed short int)((idct_M128ASM_scalar$$1$$16$$t1 - idct_M128ASM_scalar$$1$$16$$t6 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$16$$t1 - idct_M128ASM_scalar$$1$$16$$t6 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$16$$t1 - idct_M128ASM_scalar$$1$$16$$t6)) >> 1 + 4);
  (src + (signed long int)7)[(signed long int)(8 * 2)] = (signed short int)((idct_M128ASM_scalar$$1$$16$$t2 + idct_M128ASM_scalar$$1$$16$$t5 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$16$$t2 + idct_M128ASM_scalar$$1$$16$$t5 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$16$$t2 + idct_M128ASM_scalar$$1$$16$$t5)) >> 1 + 4);
  (src + (signed long int)7)[(signed long int)(8 * 5)] = (signed short int)((idct_M128ASM_scalar$$1$$16$$t2 - idct_M128ASM_scalar$$1$$16$$t5 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$16$$t2 - idct_M128ASM_scalar$$1$$16$$t5 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$16$$t2 - idct_M128ASM_scalar$$1$$16$$t5)) >> 1 + 4);
  (src + (signed long int)7)[(signed long int)(8 * 3)] = (signed short int)((idct_M128ASM_scalar$$1$$16$$t3 + idct_M128ASM_scalar$$1$$16$$t4 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$16$$t3 + idct_M128ASM_scalar$$1$$16$$t4 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$16$$t3 + idct_M128ASM_scalar$$1$$16$$t4)) >> 1 + 4);
  (src + (signed long int)7)[(signed long int)(8 * 4)] = (signed short int)((idct_M128ASM_scalar$$1$$16$$t3 - idct_M128ASM_scalar$$1$$16$$t4 > 32767 ? 32767 : (idct_M128ASM_scalar$$1$$16$$t3 - idct_M128ASM_scalar$$1$$16$$t4 < -32768 ? -32768 : idct_M128ASM_scalar$$1$$16$$t3 - idct_M128ASM_scalar$$1$$16$$t4)) >> 1 + 4);
}

// c::macroblock_modes
// file src/getpic.c line 363
static void macroblock_modes(signed int *pmacroblock_type, signed int *pstwtype, signed int *pstwclass, signed int *pmotion_type, signed int *pmotion_vector_count, signed int *pmv_format, signed int *pdmv, signed int *pmvscale, signed int *pdct_type)
{
  static unsigned char stwc_table[3l][4l] = { { (unsigned char)6, (unsigned char)3, (unsigned char)7, (unsigned char)4 }, 
    { (unsigned char)2, (unsigned char)1, (unsigned char)5, (unsigned char)4 }, 
    { (unsigned char)2, (unsigned char)5, (unsigned char)7, (unsigned char)4 } };
  static unsigned char stwclass_table[9l] = { (unsigned char)0, (unsigned char)1, (unsigned char)2, (unsigned char)1, (unsigned char)1, (unsigned char)2, (unsigned char)3, (unsigned char)3, (unsigned char)4 };
  signed int macroblock_type;
  signed int stwtype;
  signed int stwcode;
  signed int stwclass;
  signed int motion_type = 0;
  signed int motion_vector_count;
  signed int mv_format;
  signed int dmv;
  signed int mvscale;
  signed int dct_type;
  macroblock_type=Get_macroblock_type();
  if(!(Fault_Flag == 0))
    return;

  if(!((32 & macroblock_type) == 0))
  {
    if(spatial_temporal_weight_code_table_index == 0)
      stwtype = 4;

    else
    {
      unsigned int return_value_Get_Bits$1;
      return_value_Get_Bits$1=Get_Bits(2);
      stwcode = (signed int)return_value_Get_Bits$1;
      stwtype = (signed int)stwc_table[(signed long int)(spatial_temporal_weight_code_table_index - 1)][(signed long int)stwcode];
    }
  }

  else
    stwtype = (macroblock_type & 64) != 0 ? 8 : 0;
  stwclass = (signed int)stwclass_table[(signed long int)stwtype];
  unsigned int tmp_if_expr$3;
  unsigned int return_value_Get_Bits$2;
  if(!((12 & macroblock_type) == 0))
  {
    if(picture_structure == 3)
    {
      if(!(frame_pred_frame_dct == 0))
        tmp_if_expr$3 = (unsigned int)2;

      else
      {
        return_value_Get_Bits$2=Get_Bits(2);
        tmp_if_expr$3 = return_value_Get_Bits$2;
      }
      motion_type = (signed int)tmp_if_expr$3;
    }

    else
    {
      unsigned int return_value_Get_Bits$4;
      return_value_Get_Bits$4=Get_Bits(2);
      motion_type = (signed int)return_value_Get_Bits$4;
    }
  }

  else
    if(!((1 & macroblock_type) == 0))
    {
      if(!(concealment_motion_vectors == 0))
        motion_type = picture_structure == 3 ? 2 : 1;

    }

  if(picture_structure == 3)
  {
    motion_vector_count = motion_type == 1 && stwclass < 2 ? 2 : 1;
    mv_format = motion_type == 2 ? 1 : 0;
  }

  else
  {
    motion_vector_count = motion_type == 2 ? 2 : 1;
    mv_format = 0;
  }
  dmv = (signed int)(motion_type == 3);
  mvscale = (signed int)(mv_format == 0 && picture_structure == 3);
  unsigned int tmp_if_expr$6;
  unsigned int return_value_Get_Bits$5;
  if(picture_structure == 3)
  {
    if(frame_pred_frame_dct != 0)
      goto __CPROVER_DUMP_L14;

    if((3 & macroblock_type) == 0)
      goto __CPROVER_DUMP_L14;

    return_value_Get_Bits$5=Get_Bits(1);
    tmp_if_expr$6 = return_value_Get_Bits$5;
  }

  else
  {

  __CPROVER_DUMP_L14:
    ;
    tmp_if_expr$6 = (unsigned int)0;
  }
  dct_type = (signed int)tmp_if_expr$6;
  *pmacroblock_type = macroblock_type;
  *pstwtype = stwtype;
  *pstwclass = stwclass;
  *pmotion_type = motion_type;
  *pmotion_vector_count = motion_vector_count;
  *pmv_format = mv_format;
  *pdmv = dmv;
  *pmvscale = mvscale;
  *pdct_type = dct_type;
}

// c::main
// file src/mpeg2dec.c line 116
signed int main(signed int argc, char **argv)
{
  signed int ret;
  signed int code;
  Clear_Options();
  Process_Options(argc, argv);
  ld = &base;
  base.Infile=open(Main_Bitstream_Filename, 0 | 0);
  if(base.Infile < 0)
  {
    fprintf(stderr, "Base layer input file %s not found\n", Main_Bitstream_Filename);
    exit(1);
  }

  if(!(base.Infile == 0))
  {
    Initialize_Buffer();
    unsigned int return_value_Show_Bits$1;
    return_value_Show_Bits$1=Show_Bits(8);
    if(return_value_Show_Bits$1 == 71u)
    {
      sprintf(Error_Text, "Decoder currently does not parse transport streams\n");
      Error(Error_Text);
    }

    next_start_code();
    unsigned int return_value_Show_Bits$2;
    return_value_Show_Bits$2=Show_Bits(32);
    code = (signed int)return_value_Show_Bits$2;
    switch(code)
    {

      case 435:
        goto __CPROVER_DUMP_L7;
      case 442:
        System_Stream_Flag = 1;
      case 480:
        {
          System_Stream_Flag = 1;
          goto __CPROVER_DUMP_L7;
        }
      default:
        {
          sprintf(Error_Text, "Unable to recognize stream type\n");
          Error(Error_Text);
        }
    }

  __CPROVER_DUMP_L7:
    ;
    lseek(base.Infile, 0l, 0);
    Initialize_Buffer();
  }

  if(System_Stream_Flag == 0)
    (void)0;

  else
    /* assertion !System_Stream_Flag */
    assert(FALSE);
  if(!(base.Infile == 0))
    lseek(base.Infile, 0l, 0);

  Initialize_Buffer();
  if(Two_Streams == 0)
    (void)0;

  else
  {
  /* assertion !Two_Streams&&"I don't support two streams\n" */

  __CPROVER_DUMP_L12:
    ;
    /* assertion !Two_Streams&&"I don't support two streams\n" */
    assert(FALSE);
  }
  if(!(Two_Streams == 0))
  {
    ld = &enhan;
    enhan.Infile=open(Enhancement_Layer_Bitstream_Filename, 0 | 0);
    if(enhan.Infile < 0)
    {
      sprintf(Error_Text, "enhancment layer bitstream file %s not found\n", Enhancement_Layer_Bitstream_Filename);
      Error(Error_Text);
    }

    Initialize_Buffer();
    ld = &base;
  }

  Initialize_Decoder();
  Initialize_Frame_Buffer();
  ret=Decode_Bitstream();
  close(base.Infile);
  if(!(Two_Streams == 0))
    close(enhan.Infile);

  return 0;
}

// c::marker_bit
// file src/gethdr.c line 1084
void marker_bit(char *text)
{
  signed int marker;
  unsigned int return_value_Get_Bits$1;
  return_value_Get_Bits$1=Get_Bits(1);
  marker = (signed int)return_value_Get_Bits$1;
}

// c::mbstowcs
// file /usr/include/x86_64-linux-gnu/bits/stdlib.h line 113
unsigned long int mbstowcs(signed int * restrict __dst, const char * restrict __src, unsigned long int __len)
{
  unsigned long int return_value___mbstowcs_chk$1;
  unsigned long int return_value___mbstowcs_chk_warn$2;
  unsigned long int return_value___mbstowcs_alias$3;
  return_value___mbstowcs_alias$3=__mbstowcs_alias(__dst, __src, __len);
  return return_value___mbstowcs_alias$3;
}

// c::motion_vector
// file src/motion.c line 144
void motion_vector(signed int *PMV, signed int *dmvector, signed int h_r_size, signed int v_r_size, signed int dmv, signed int mvscale, signed int full_pel_vector)
{
  signed int motion_code;
  signed int motion_residual;
  motion_code=Get_motion_code();
  unsigned int tmp_if_expr$2;
  unsigned int return_value_Get_Bits$1;
  if(!(h_r_size == 0))
  {
    if(motion_code == 0)
      goto __CPROVER_DUMP_L1;

    return_value_Get_Bits$1=Get_Bits(h_r_size);
    tmp_if_expr$2 = return_value_Get_Bits$1;
  }

  else
  {

  __CPROVER_DUMP_L1:
    ;
    tmp_if_expr$2 = (unsigned int)0;
  }
  motion_residual = (signed int)tmp_if_expr$2;
  decode_motion_vector(&PMV[(signed long int)0], h_r_size, motion_code, motion_residual, full_pel_vector);
  if(!(dmv == 0))
    dmvector[(signed long int)0]=Get_dmvector();

  motion_code=Get_motion_code();
  unsigned int tmp_if_expr$4;
  unsigned int return_value_Get_Bits$3;
  if(!(v_r_size == 0))
  {
    if(motion_code == 0)
      goto __CPROVER_DUMP_L4;

    return_value_Get_Bits$3=Get_Bits(v_r_size);
    tmp_if_expr$4 = return_value_Get_Bits$3;
  }

  else
  {

  __CPROVER_DUMP_L4:
    ;
    tmp_if_expr$4 = (unsigned int)0;
  }
  motion_residual = (signed int)tmp_if_expr$4;
  if(!(mvscale == 0))
    PMV[(signed long int)1] = PMV[(signed long int)1] >> 1;

  decode_motion_vector(&PMV[(signed long int)1], v_r_size, motion_code, motion_residual, full_pel_vector);
  if(!(mvscale == 0))
    PMV[(signed long int)1] = PMV[(signed long int)1] << 1;

  if(!(dmv == 0))
    dmvector[(signed long int)1]=Get_dmvector();

}

// c::motion_vectors
// file src/motion.c line 91
void motion_vectors(signed int (*PMV)[2l][2l], signed int *dmvector, signed int (*motion_vertical_field_select)[2l], signed int s, signed int motion_vector_count, signed int mv_format, signed int h_r_size, signed int v_r_size, signed int dmv, signed int mvscale)
{
  if(motion_vector_count == 1)
  {
    if(mv_format == 0)
    {
      if(dmv == 0)
      {
        unsigned int return_value_Get_Bits$1;
        return_value_Get_Bits$1=Get_Bits(1);
        motion_vertical_field_select[(signed long int)0][(signed long int)s] = (signed int)return_value_Get_Bits$1;
        motion_vertical_field_select[(signed long int)1][(signed long int)s] = motion_vertical_field_select[(signed long int)0][(signed long int)s];
      }

    }

    motion_vector(PMV[(signed long int)0][(signed long int)s], dmvector, h_r_size, v_r_size, dmv, mvscale, 0);
    PMV[(signed long int)1][(signed long int)s][(signed long int)0] = PMV[(signed long int)0][(signed long int)s][(signed long int)0];
    PMV[(signed long int)1][(signed long int)s][(signed long int)1] = PMV[(signed long int)0][(signed long int)s][(signed long int)1];
  }

  else
  {
    unsigned int return_value_Get_Bits$2;
    return_value_Get_Bits$2=Get_Bits(1);
    motion_vertical_field_select[(signed long int)0][(signed long int)s] = (signed int)return_value_Get_Bits$2;
    motion_vector(PMV[(signed long int)0][(signed long int)s], dmvector, h_r_size, v_r_size, dmv, mvscale, 0);
    unsigned int return_value_Get_Bits$3;
    return_value_Get_Bits$3=Get_Bits(1);
    motion_vertical_field_select[(signed long int)1][(signed long int)s] = (signed int)return_value_Get_Bits$3;
    motion_vector(PMV[(signed long int)1][(signed long int)s], dmvector, h_r_size, v_r_size, dmv, mvscale, 0);
  }
}

// c::new_slice
// file src/getpic.c line 1622
static signed int new_slice(signed int framenum, signed int MBAmax)
{
  unsigned int code;
  unsigned int num_slices = (unsigned int)0;
  signed int chunk_size;
  signed int remainder;
  signed int thrd_num = 1;
  signed int num_decode_slice[2l];
  signed int tmp;
  signed int t;
  signed int next_marker;
  unsigned int ptr_offset[2l];
  unsigned long int thread[1l];
  union pthread_attr_t attr;
  signed int rc;
  signed int status;
  signed int num_thrds = mb_height > 2 ? 2 : mb_height;
  pthread_attr_init(&attr);
  pthread_attr_setdetachstate(&attr, 0);
  tb[(signed long int)0].frame_buf_offset = (unsigned int)0;
  next_start_code();
  code=Show_Bits(32);
  if(!(code < 257u))
  {
    if(code > 431u)
      goto __CPROVER_DUMP_L1;

    (void)0;
  }

  else
  {
  /* assertion !(code<0x101 || code>0x1AF)&&"Bad slice start code\n" */

  __CPROVER_DUMP_L1:
    ;
    /* assertion !(code<0x101 || code>0x1AF)&&"Bad slice start code\n" */
    assert(FALSE);
  }
  write_frame_buf32(0, code);
  Flush_Buffer32();
  num_slices = num_slices + 1u;
  chunk_size = mb_height / num_thrds;
  remainder = mb_height % num_thrds;
  num_decode_slice[(signed long int)0] = remainder > 0 ? chunk_size + 1 : chunk_size;
  next_marker = num_decode_slice[(signed long int)0];
  unsigned int return_value_Show_Bits$1;
  while((unsigned int)mb_height >= num_slices)
  {
    if(ld->Incnt > 24)
      (void)0;

    else
      /* assertion ld->Incnt > 24 */
      assert(FALSE);
    do
    {
      return_value_Show_Bits$1=Show_Bits(24);
      if((signed long int)return_value_Show_Bits$1 == 1l)
        goto __CPROVER_DUMP_L7;

      unsigned int return_value_Show_Bits$2;
      return_value_Show_Bits$2=Show_Bits(8);
      write_frame_buf8(thrd_num - 1, (unsigned char)return_value_Show_Bits$2);
      Flush_Buffer(8);
    }
    while(TRUE);

  __CPROVER_DUMP_L7:
    ;
    if(!(num_slices == (unsigned int)mb_height))
    {
      code=Show_Bits(32);
      if(!(code < 257u))
      {
        if(code > 431u)
          goto __CPROVER_DUMP_L8;

        (void)0;
      }

      else
      {
      /* assertion !(code<0x101 || code>0x1AF)&&"Bad slice start code\n" */

      __CPROVER_DUMP_L8:
        ;
        /* assertion !(code<0x101 || code>0x1AF)&&"Bad slice start code\n" */
        assert(FALSE);
      }
      if(num_slices == (unsigned int)next_marker)
      {
        tb[(signed long int)thrd_num].frame_buf_offset = (unsigned int)0;
        num_decode_slice[(signed long int)thrd_num] = remainder > thrd_num ? chunk_size + 1 : chunk_size;
        next_marker = next_marker + num_decode_slice[(signed long int)thrd_num];
        t = thrd_num - 1;
        thread_data_array[(signed long int)t].id = t;
        thread_data_array[(signed long int)t].num_slices = num_decode_slice[(signed long int)t];
        thread_data_array[(signed long int)t].framenum = framenum;
        thread_data_array[(signed long int)t].MBAmax = MBAmax;
        thrd_ptr[(signed long int)t] = tb[(signed long int)t].frame_buf;
        Thrd_Initialize_Buffer(t);
        if(!(t == -1 + num_thrds))
        {
          rc=pthread_create(&thread[(signed long int)t], &attr, Thrd_Work, (void *)&thread_data_array[(signed long int)t]);
          if(!(rc == 0))
          {
            printf("ERROR; return code from pthread_create() is %d\n", rc);
            exit(-1);
          }

        }

        thrd_num = thrd_num + 1;
      }

      write_frame_buf32(thrd_num - 1, code);
      Flush_Buffer32();
    }

    num_slices = num_slices + 1u;
  }
  t = thrd_num - 1;
  thread_data_array[(signed long int)t].id = t;
  thread_data_array[(signed long int)t].num_slices = num_decode_slice[(signed long int)t];
  thread_data_array[(signed long int)t].framenum = framenum;
  thread_data_array[(signed long int)t].MBAmax = MBAmax;
  thrd_ptr[(signed long int)t] = tb[(signed long int)t].frame_buf;
  Thrd_Initialize_Buffer(t);
  Thrd_Work((void *)&thread_data_array[(signed long int)t]);
  t = 0;
  while(!(t >= -1 + num_thrds))
  {
    rc=pthread_join(thread[(signed long int)t], (void **)&status);
    if(!(rc == 0))
    {
      printf("ERROR; return code from pthread_join() is %d\n", rc);
      exit(-1);
    }

    t = t + 1;
  }
  return -1;
}

// c::next_start_code
// file src/gethdr.c line 181
void next_start_code(void)
{
  Flush_Buffer(ld->Incnt & 7);
  unsigned int return_value_Show_Bits$1;
  do
  {
    return_value_Show_Bits$1=Show_Bits(24);
    if((signed long int)return_value_Show_Bits$1 == 1l)
      goto __CPROVER_DUMP_L2;

    Flush_Buffer(8);
  }
  while(TRUE);

__CPROVER_DUMP_L2:
  ;
}

// c::open
// file /usr/include/x86_64-linux-gnu/bits/fcntl2.h line 41
signed int open(const char *__path, signed int __oflag, ...)
{
  signed int return_value___builtin_va_arg_pack_len$1;
  return_value___builtin_va_arg_pack_len$1=__builtin_va_arg_pack_len();
  if(return_value___builtin_va_arg_pack_len$1 > 1)
    __open_too_many_args();

  signed int return_value___builtin_va_arg_pack_len$3;
  signed int return_value___builtin_va_arg_pack_len$7;
  return_value___builtin_va_arg_pack_len$7=__builtin_va_arg_pack_len();
  signed int return_value___open_2$6;
  if(return_value___builtin_va_arg_pack_len$7 < 1)
  {
    return_value___open_2$6=__open_2(__path, __oflag);
    return return_value___open_2$6;
  }

  void *return_value___builtin_va_arg_pack$8;
  return_value___builtin_va_arg_pack$8=__builtin_va_arg_pack();
  signed int return_value___open_alias$9;
  return_value___open_alias$9=__open_alias(__path, __oflag, return_value___builtin_va_arg_pack$8);
  return return_value___open_alias$9;
}

// c::openat
// file /usr/include/x86_64-linux-gnu/bits/fcntl2.h line 117
signed int openat(signed int __fd, const char *__path, signed int __oflag, ...)
{
  signed int return_value___builtin_va_arg_pack_len$1;
  return_value___builtin_va_arg_pack_len$1=__builtin_va_arg_pack_len();
  if(return_value___builtin_va_arg_pack_len$1 > 1)
    __openat_too_many_args();

  signed int return_value___builtin_va_arg_pack_len$3;
  signed int return_value___builtin_va_arg_pack_len$7;
  return_value___builtin_va_arg_pack_len$7=__builtin_va_arg_pack_len();
  signed int return_value___openat_2$6;
  if(return_value___builtin_va_arg_pack_len$7 < 1)
  {
    return_value___openat_2$6=__openat_2(__fd, __path, __oflag);
    return return_value___openat_2$6;
  }

  void *return_value___builtin_va_arg_pack$8;
  return_value___builtin_va_arg_pack$8=__builtin_va_arg_pack();
  signed int return_value___openat_alias$9;
  return_value___openat_alias$9=__openat_alias(__fd, __path, __oflag, return_value___builtin_va_arg_pack$8);
  return return_value___openat_alias$9;
}

// c::picture_coding_extension
// file src/gethdr.c line 928
static void picture_coding_extension(void)
{
  signed int pos = ld->Bitcnt;
  unsigned int return_value_Get_Bits$1;
  return_value_Get_Bits$1=Get_Bits(4);
  f_code[(signed long int)0][(signed long int)0] = (signed int)return_value_Get_Bits$1;
  unsigned int return_value_Get_Bits$2;
  return_value_Get_Bits$2=Get_Bits(4);
  f_code[(signed long int)0][(signed long int)1] = (signed int)return_value_Get_Bits$2;
  unsigned int return_value_Get_Bits$3;
  return_value_Get_Bits$3=Get_Bits(4);
  f_code[(signed long int)1][(signed long int)0] = (signed int)return_value_Get_Bits$3;
  unsigned int return_value_Get_Bits$4;
  return_value_Get_Bits$4=Get_Bits(4);
  f_code[(signed long int)1][(signed long int)1] = (signed int)return_value_Get_Bits$4;
  unsigned int return_value_Get_Bits$5;
  return_value_Get_Bits$5=Get_Bits(2);
  intra_dc_precision = (signed int)return_value_Get_Bits$5;
  unsigned int return_value_Get_Bits$6;
  return_value_Get_Bits$6=Get_Bits(2);
  picture_structure = (signed int)return_value_Get_Bits$6;
  unsigned int return_value_Get_Bits$7;
  return_value_Get_Bits$7=Get_Bits(1);
  top_field_first = (signed int)return_value_Get_Bits$7;
  unsigned int return_value_Get_Bits$8;
  return_value_Get_Bits$8=Get_Bits(1);
  frame_pred_frame_dct = (signed int)return_value_Get_Bits$8;
  unsigned int return_value_Get_Bits$9;
  return_value_Get_Bits$9=Get_Bits(1);
  concealment_motion_vectors = (signed int)return_value_Get_Bits$9;
  unsigned int return_value_Get_Bits$10;
  return_value_Get_Bits$10=Get_Bits(1);
  ld->q_scale_type = (signed int)return_value_Get_Bits$10;
  unsigned int return_value_Get_Bits$11;
  return_value_Get_Bits$11=Get_Bits(1);
  intra_vlc_format = (signed int)return_value_Get_Bits$11;
  unsigned int return_value_Get_Bits$12;
  return_value_Get_Bits$12=Get_Bits(1);
  ld->alternate_scan = (signed int)return_value_Get_Bits$12;
  unsigned int return_value_Get_Bits$13;
  return_value_Get_Bits$13=Get_Bits(1);
  repeat_first_field = (signed int)return_value_Get_Bits$13;
  unsigned int return_value_Get_Bits$14;
  return_value_Get_Bits$14=Get_Bits(1);
  chroma_420_type = (signed int)return_value_Get_Bits$14;
  unsigned int return_value_Get_Bits$15;
  return_value_Get_Bits$15=Get_Bits(1);
  progressive_frame = (signed int)return_value_Get_Bits$15;
  unsigned int return_value_Get_Bits$16;
  return_value_Get_Bits$16=Get_Bits(1);
  composite_display_flag = (signed int)return_value_Get_Bits$16;
  if(!(composite_display_flag == 0))
  {
    unsigned int return_value_Get_Bits$17;
    return_value_Get_Bits$17=Get_Bits(1);
    v_axis = (signed int)return_value_Get_Bits$17;
    unsigned int return_value_Get_Bits$18;
    return_value_Get_Bits$18=Get_Bits(3);
    field_sequence = (signed int)return_value_Get_Bits$18;
    unsigned int return_value_Get_Bits$19;
    return_value_Get_Bits$19=Get_Bits(1);
    sub_carrier = (signed int)return_value_Get_Bits$19;
    unsigned int return_value_Get_Bits$20;
    return_value_Get_Bits$20=Get_Bits(7);
    burst_amplitude = (signed int)return_value_Get_Bits$20;
    unsigned int return_value_Get_Bits$21;
    return_value_Get_Bits$21=Get_Bits(8);
    sub_carrier_phase = (signed int)return_value_Get_Bits$21;
  }

}

// c::picture_data
// file src/getpic.c line 201
static void picture_data(signed int framenum)
{
  signed int MBAmax;
  signed int ret;
  signed int slice_num = 0;
  MBAmax = mb_width * mb_height;
  if(!(picture_structure == 3))
    MBAmax = MBAmax >> 1;

  do
  {
    slice_num = slice_num + 1;
    slice_num;
    ret=new_slice(framenum, MBAmax);
    if(ret < 0)
      return;

  }
  while(TRUE);
}

// c::picture_display_extension
// file src/gethdr.c line 851
static void picture_display_extension(void)
{
  signed int i;
  signed int number_of_frame_center_offsets;
  signed int pos = ld->Bitcnt;
  if(!(progressive_sequence == 0))
  {
    if(!(repeat_first_field == 0))
    {
      if(!(top_field_first == 0))
        number_of_frame_center_offsets = 3;

      else
        number_of_frame_center_offsets = 2;
    }

    else
      number_of_frame_center_offsets = 1;
  }

  else
    if(!(picture_structure == 3))
      number_of_frame_center_offsets = 1;

    else
      if(!(repeat_first_field == 0))
        number_of_frame_center_offsets = 3;

      else
        number_of_frame_center_offsets = 2;
  i = 0;
  while(!(i >= number_of_frame_center_offsets))
  {
    unsigned int return_value_Get_Bits$1;
    return_value_Get_Bits$1=Get_Bits(16);
    frame_center_horizontal_offset[(signed long int)i] = (signed int)return_value_Get_Bits$1;
    marker_bit("picture_display_extension, first marker bit");
    unsigned int return_value_Get_Bits$2;
    return_value_Get_Bits$2=Get_Bits(16);
    frame_center_vertical_offset[(signed long int)i] = (signed int)return_value_Get_Bits$2;
    marker_bit("picture_display_extension, second marker bit");
    i = i + 1;
  }
}

// c::picture_header
// file src/gethdr.c line 377
static void picture_header(void)
{
  signed int pos;
  signed int Extra_Information_Byte_Count;
  ld->pict_scal = 0;
  pos = ld->Bitcnt;
  unsigned int return_value_Get_Bits$1;
  return_value_Get_Bits$1=Get_Bits(10);
  temporal_reference = (signed int)return_value_Get_Bits$1;
  unsigned int return_value_Get_Bits$2;
  return_value_Get_Bits$2=Get_Bits(3);
  picture_coding_type = (signed int)return_value_Get_Bits$2;
  unsigned int return_value_Get_Bits$3;
  return_value_Get_Bits$3=Get_Bits(16);
  vbv_delay = (signed int)return_value_Get_Bits$3;
  if(!(picture_coding_type == 2))
  {
    if(picture_coding_type == 3)
      goto __CPROVER_DUMP_L1;

  }

  else
  {

  __CPROVER_DUMP_L1:
    ;
    unsigned int return_value_Get_Bits$4;
    return_value_Get_Bits$4=Get_Bits(1);
    full_pel_forward_vector = (signed int)return_value_Get_Bits$4;
    unsigned int return_value_Get_Bits$5;
    return_value_Get_Bits$5=Get_Bits(3);
    forward_f_code = (signed int)return_value_Get_Bits$5;
  }
  if(picture_coding_type == 3)
  {
    unsigned int return_value_Get_Bits$6;
    return_value_Get_Bits$6=Get_Bits(1);
    full_pel_backward_vector = (signed int)return_value_Get_Bits$6;
    unsigned int return_value_Get_Bits$7;
    return_value_Get_Bits$7=Get_Bits(3);
    backward_f_code = (signed int)return_value_Get_Bits$7;
  }

  Extra_Information_Byte_Count=extra_bit_information();
  extension_and_user_data();
  Update_Temporal_Reference_Tacking_Data();
}

// c::picture_spatial_scalable_extension
// file src/gethdr.c line 1004
static void picture_spatial_scalable_extension(void)
{
  signed int pos = ld->Bitcnt;
  ld->pict_scal = 1;
  unsigned int return_value_Get_Bits$1;
  return_value_Get_Bits$1=Get_Bits(10);
  lower_layer_temporal_reference = (signed int)return_value_Get_Bits$1;
  marker_bit("picture_spatial_scalable_extension(), first marker bit");
  unsigned int return_value_Get_Bits$2;
  return_value_Get_Bits$2=Get_Bits(15);
  lower_layer_horizontal_offset = (signed int)return_value_Get_Bits$2;
  if(lower_layer_horizontal_offset >= 16384)
    lower_layer_horizontal_offset = lower_layer_horizontal_offset - 32768;

  marker_bit("picture_spatial_scalable_extension(), second marker bit");
  unsigned int return_value_Get_Bits$3;
  return_value_Get_Bits$3=Get_Bits(15);
  lower_layer_vertical_offset = (signed int)return_value_Get_Bits$3;
  if(lower_layer_vertical_offset >= 16384)
    lower_layer_vertical_offset = lower_layer_vertical_offset - 32768;

  unsigned int return_value_Get_Bits$4;
  return_value_Get_Bits$4=Get_Bits(2);
  spatial_temporal_weight_code_table_index = (signed int)return_value_Get_Bits$4;
  unsigned int return_value_Get_Bits$5;
  return_value_Get_Bits$5=Get_Bits(1);
  lower_layer_progressive_frame = (signed int)return_value_Get_Bits$5;
  unsigned int return_value_Get_Bits$6;
  return_value_Get_Bits$6=Get_Bits(1);
  lower_layer_deinterlaced_field_select = (signed int)return_value_Get_Bits$6;
}

// c::picture_temporal_scalable_extension
// file src/gethdr.c line 1054
static void picture_temporal_scalable_extension(void)
{
  Error("temporal scalability not supported\n");
}

// c::printf
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 102
signed int printf(const char * restrict __fmt, ...)
{
  void *return_value___builtin_va_arg_pack$1;
  return_value___builtin_va_arg_pack$1=__builtin_va_arg_pack();
  signed int return_value___printf_chk$2;
  return_value___printf_chk$2=__printf_chk(2 - 1, __fmt, return_value___builtin_va_arg_pack$1);
  return return_value___printf_chk$2;
}

// c::pthread_equal
// file /usr/include/pthread.h line 1144
signed int pthread_equal(unsigned long int __thread1, unsigned long int __thread2)
{
  return (signed int)(__thread1 == __thread2);
}

// c::ptsname_r
// file /usr/include/x86_64-linux-gnu/bits/stdlib.h line 64
signed int ptsname_r(signed int __fd, char *__buf, unsigned long int __buflen)
{
  signed int return_value___ptsname_r_chk$1;
  signed int return_value___ptsname_r_chk_warn$2;
  signed int return_value___ptsname_r_alias$3;
  return_value___ptsname_r_alias$3=__ptsname_r_alias(__fd, __buf, __buflen);
  return return_value___ptsname_r_alias$3;
}

// c::putbyte
// file src/store.c line 490
static void putbyte(signed int c)
{
  unsigned char *tmp_post$1 = optr;
  optr = optr + 1l;
  *tmp_post$1 = (unsigned char)c;
  if(optr == obfr + 8192l)
  {
    write(outfile, (const void *)obfr, (unsigned long int)8192);
    optr = obfr;
  }

}

// c::putc_unlocked
// file /usr/include/x86_64-linux-gnu/bits/stdio.h line 98
signed int putc_unlocked(signed int __c, struct _IO_FILE *__stream)
{
  signed int tmp_if_expr$3;
  signed int return_value___overflow$1;
  char *tmp_post$2;
  if(__stream->_IO_write_ptr >= __stream->_IO_write_end)
  {
    return_value___overflow$1=__overflow(__stream, (signed int)(unsigned char)__c);
    tmp_if_expr$3 = return_value___overflow$1;
  }

  else
  {
    tmp_post$2 = __stream->_IO_write_ptr;
    __stream->_IO_write_ptr = __stream->_IO_write_ptr + 1l;
    *tmp_post$2 = (char)__c;
    tmp_if_expr$3 = (signed int)(unsigned char)*tmp_post$2;
  }
  return tmp_if_expr$3;
}

// c::putchar
// file /usr/include/x86_64-linux-gnu/bits/stdio.h line 79
signed int putchar(signed int __c)
{
  signed int return_value__IO_putc$1;
  return_value__IO_putc$1=_IO_putc(__c, stdout);
  return return_value__IO_putc$1;
}

// c::putchar_unlocked
// file /usr/include/x86_64-linux-gnu/bits/stdio.h line 105
signed int putchar_unlocked(signed int __c)
{
  signed int tmp_if_expr$3;
  signed int return_value___overflow$1;
  char *tmp_post$2;
  if(stdout->_IO_write_ptr >= stdout->_IO_write_end)
  {
    return_value___overflow$1=__overflow(stdout, (signed int)(unsigned char)__c);
    tmp_if_expr$3 = return_value___overflow$1;
  }

  else
  {
    tmp_post$2 = stdout->_IO_write_ptr;
    stdout->_IO_write_ptr = stdout->_IO_write_ptr + 1l;
    *tmp_post$2 = (char)__c;
    tmp_if_expr$3 = (signed int)(unsigned char)*tmp_post$2;
  }
  return tmp_if_expr$3;
}

// c::putword
// file src/store.c line 502
static void putword(signed int w)
{
  putbyte(w);
  putbyte(w >> 8);
}

// c::quant_matrix_extension
// file src/gethdr.c line 726
static void quant_matrix_extension(void)
{
  signed int i;
  signed int pos = ld->Bitcnt;
  unsigned int return_value_Get_Bits$2;
  return_value_Get_Bits$2=Get_Bits(1);
  ld->load_intra_quantizer_matrix = (signed int)return_value_Get_Bits$2;
  if(!(ld->load_intra_quantizer_matrix == 0))
  {
    i = 0;
    while(i < 64)
    {
      unsigned int return_value_Get_Bits$1;
      return_value_Get_Bits$1=Get_Bits(8);
      ld->intra_quantizer_matrix[(signed long int)scan[(signed long int)0][(signed long int)i]] = (signed int)return_value_Get_Bits$1;
      ld->chroma_intra_quantizer_matrix[(signed long int)scan[(signed long int)0][(signed long int)i]] = ld->intra_quantizer_matrix[(signed long int)scan[(signed long int)0][(signed long int)i]];
      i = i + 1;
    }
  }

  unsigned int return_value_Get_Bits$4;
  return_value_Get_Bits$4=Get_Bits(1);
  ld->load_non_intra_quantizer_matrix = (signed int)return_value_Get_Bits$4;
  if(!(ld->load_non_intra_quantizer_matrix == 0))
  {
    i = 0;
    while(i < 64)
    {
      unsigned int return_value_Get_Bits$3;
      return_value_Get_Bits$3=Get_Bits(8);
      ld->non_intra_quantizer_matrix[(signed long int)scan[(signed long int)0][(signed long int)i]] = (signed int)return_value_Get_Bits$3;
      ld->chroma_non_intra_quantizer_matrix[(signed long int)scan[(signed long int)0][(signed long int)i]] = ld->non_intra_quantizer_matrix[(signed long int)scan[(signed long int)0][(signed long int)i]];
      i = i + 1;
    }
  }

  unsigned int return_value_Get_Bits$6;
  return_value_Get_Bits$6=Get_Bits(1);
  ld->load_chroma_intra_quantizer_matrix = (signed int)return_value_Get_Bits$6;
  unsigned int return_value_Get_Bits$5;
  if(!(ld->load_chroma_intra_quantizer_matrix == 0))
  {
    i = 0;
    while(i < 64)
    {
      return_value_Get_Bits$5=Get_Bits(8);
      ld->chroma_intra_quantizer_matrix[(signed long int)scan[(signed long int)0][(signed long int)i]] = (signed int)return_value_Get_Bits$5;
      i = i + 1;
    }
  }

  unsigned int return_value_Get_Bits$8;
  return_value_Get_Bits$8=Get_Bits(1);
  ld->load_chroma_non_intra_quantizer_matrix = (signed int)return_value_Get_Bits$8;
  unsigned int return_value_Get_Bits$7;
  if(!(ld->load_chroma_non_intra_quantizer_matrix == 0))
  {
    i = 0;
    while(i < 64)
    {
      return_value_Get_Bits$7=Get_Bits(8);
      ld->chroma_non_intra_quantizer_matrix[(signed long int)scan[(signed long int)0][(signed long int)i]] = (signed int)return_value_Get_Bits$7;
      i = i + 1;
    }
  }

}

// c::read
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 34
signed long int read(signed int __fd, void *__buf, unsigned long int __nbytes)
{
  signed long int return_value___read_chk$1;
  signed long int return_value___read_chk_warn$2;
  signed long int return_value___read_alias$3;
  return_value___read_alias$3=__read_alias(__fd, __buf, __nbytes);
  return return_value___read_alias$3;
}

// c::readlink
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 139
signed long int readlink(const char * restrict __path, char * restrict __buf, unsigned long int __len)
{
  signed long int return_value___readlink_chk$1;
  signed long int return_value___readlink_chk_warn$2;
  signed long int return_value___readlink_alias$3;
  return_value___readlink_alias$3=__readlink_alias(__path, __buf, __len);
  return return_value___readlink_alias$3;
}

// c::readlinkat
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 173
signed long int readlinkat(signed int __fd, const char * restrict __path, char * restrict __buf, unsigned long int __len)
{
  signed long int return_value___readlinkat_chk$1;
  signed long int return_value___readlinkat_chk_warn$2;
  signed long int return_value___readlinkat_alias$3;
  return_value___readlinkat_alias$3=__readlinkat_alias(__fd, __path, __buf, __len);
  return return_value___readlinkat_alias$3;
}

// c::realpath
// file /usr/include/x86_64-linux-gnu/bits/stdlib.h line 37
char * realpath(const char * restrict __name, char * restrict __resolved)
{
  char *return_value___realpath_alias$2;
  return_value___realpath_alias$2=__realpath_alias(__name, __resolved);
  return return_value___realpath_alias$2;
}

// c::sequence_display_extension
// file src/gethdr.c line 676
static void sequence_display_extension(void)
{
  signed int pos = ld->Bitcnt;
  unsigned int return_value_Get_Bits$1;
  return_value_Get_Bits$1=Get_Bits(3);
  video_format = (signed int)return_value_Get_Bits$1;
  unsigned int return_value_Get_Bits$2;
  return_value_Get_Bits$2=Get_Bits(1);
  color_description = (signed int)return_value_Get_Bits$2;
  if(!(color_description == 0))
  {
    unsigned int return_value_Get_Bits$3;
    return_value_Get_Bits$3=Get_Bits(8);
    color_primaries = (signed int)return_value_Get_Bits$3;
    unsigned int return_value_Get_Bits$4;
    return_value_Get_Bits$4=Get_Bits(8);
    transfer_characteristics = (signed int)return_value_Get_Bits$4;
    unsigned int return_value_Get_Bits$5;
    return_value_Get_Bits$5=Get_Bits(8);
    matrix_coefficients = (signed int)return_value_Get_Bits$5;
  }

  unsigned int return_value_Get_Bits$6;
  return_value_Get_Bits$6=Get_Bits(14);
  display_horizontal_size = (signed int)return_value_Get_Bits$6;
  marker_bit("sequence_display_extension");
  unsigned int return_value_Get_Bits$7;
  return_value_Get_Bits$7=Get_Bits(14);
  display_vertical_size = (signed int)return_value_Get_Bits$7;
}

// c::sequence_extension
// file src/gethdr.c line 573
static void sequence_extension(void)
{
  signed int horizontal_size_extension;
  signed int vertical_size_extension;
  signed int bit_rate_extension;
  signed int vbv_buffer_size_extension;
  ld->MPEG2_Flag = 1;
  ld->scalable_mode = 0;
  layer_id = 0;
  unsigned int return_value_Get_Bits$1;
  return_value_Get_Bits$1=Get_Bits(8);
  profile_and_level_indication = (signed int)return_value_Get_Bits$1;
  unsigned int return_value_Get_Bits$2;
  return_value_Get_Bits$2=Get_Bits(1);
  progressive_sequence = (signed int)return_value_Get_Bits$2;
  unsigned int return_value_Get_Bits$3;
  return_value_Get_Bits$3=Get_Bits(2);
  chroma_format = (signed int)return_value_Get_Bits$3;
  unsigned int return_value_Get_Bits$4;
  return_value_Get_Bits$4=Get_Bits(2);
  horizontal_size_extension = (signed int)return_value_Get_Bits$4;
  unsigned int return_value_Get_Bits$5;
  return_value_Get_Bits$5=Get_Bits(2);
  vertical_size_extension = (signed int)return_value_Get_Bits$5;
  unsigned int return_value_Get_Bits$6;
  return_value_Get_Bits$6=Get_Bits(12);
  bit_rate_extension = (signed int)return_value_Get_Bits$6;
  marker_bit("sequence_extension");
  unsigned int return_value_Get_Bits$7;
  return_value_Get_Bits$7=Get_Bits(8);
  vbv_buffer_size_extension = (signed int)return_value_Get_Bits$7;
  unsigned int return_value_Get_Bits$8;
  return_value_Get_Bits$8=Get_Bits(1);
  low_delay = (signed int)return_value_Get_Bits$8;
  unsigned int return_value_Get_Bits$9;
  return_value_Get_Bits$9=Get_Bits(2);
  frame_rate_extension_n = (signed int)return_value_Get_Bits$9;
  unsigned int return_value_Get_Bits$10;
  return_value_Get_Bits$10=Get_Bits(5);
  frame_rate_extension_d = (signed int)return_value_Get_Bits$10;
  frame_rate = frame_rate_Table[(signed long int)frame_rate_code] * (double)((frame_rate_extension_n + 1) / (frame_rate_extension_d + 1));
  if(!((profile_and_level_indication >> 7 & 1) == 0))
  {
    if((15 & profile_and_level_indication) == 5)
    {
      profile = 128 + 5;
      level = 8;
    }

  }

  else
  {
    profile = profile_and_level_indication >> 4;
    level = profile_and_level_indication & 15;
  }
  horizontal_size = horizontal_size_extension << 12 | horizontal_size & 4095;
  vertical_size = vertical_size_extension << 12 | vertical_size & 4095;
  bit_rate_value = bit_rate_value + (bit_rate_extension << 18);
  bit_rate = (double)bit_rate_value * 400.000000;
  vbv_buffer_size = vbv_buffer_size + (vbv_buffer_size_extension << 10);
}

// c::sequence_header
// file src/gethdr.c line 255
static void sequence_header(void)
{
  signed int i;
  signed int pos = ld->Bitcnt;
  unsigned int return_value_Get_Bits$1;
  return_value_Get_Bits$1=Get_Bits(12);
  horizontal_size = (signed int)return_value_Get_Bits$1;
  unsigned int return_value_Get_Bits$2;
  return_value_Get_Bits$2=Get_Bits(12);
  vertical_size = (signed int)return_value_Get_Bits$2;
  unsigned int return_value_Get_Bits$3;
  return_value_Get_Bits$3=Get_Bits(4);
  aspect_ratio_information = (signed int)return_value_Get_Bits$3;
  unsigned int return_value_Get_Bits$4;
  return_value_Get_Bits$4=Get_Bits(4);
  frame_rate_code = (signed int)return_value_Get_Bits$4;
  unsigned int return_value_Get_Bits$5;
  return_value_Get_Bits$5=Get_Bits(18);
  bit_rate_value = (signed int)return_value_Get_Bits$5;
  marker_bit("sequence_header()");
  unsigned int return_value_Get_Bits$6;
  return_value_Get_Bits$6=Get_Bits(10);
  vbv_buffer_size = (signed int)return_value_Get_Bits$6;
  unsigned int return_value_Get_Bits$7;
  return_value_Get_Bits$7=Get_Bits(1);
  constrained_parameters_flag = (signed int)return_value_Get_Bits$7;
  unsigned int return_value_Get_Bits$9;
  return_value_Get_Bits$9=Get_Bits(1);
  ld->load_intra_quantizer_matrix = (signed int)return_value_Get_Bits$9;
  unsigned int return_value_Get_Bits$8;
  if(!(ld->load_intra_quantizer_matrix == 0))
  {
    i = 0;
    while(i < 64)
    {
      return_value_Get_Bits$8=Get_Bits(8);
      ld->intra_quantizer_matrix[(signed long int)scan[(signed long int)0][(signed long int)i]] = (signed int)return_value_Get_Bits$8;
      i = i + 1;
    }
  }

  else
  {
    i = 0;
    while(i < 64)
    {
      ld->intra_quantizer_matrix[(signed long int)i] = (signed int)default_intra_quantizer_matrix[(signed long int)i];
      i = i + 1;
    }
  }
  unsigned int return_value_Get_Bits$11;
  return_value_Get_Bits$11=Get_Bits(1);
  ld->load_non_intra_quantizer_matrix = (signed int)return_value_Get_Bits$11;
  unsigned int return_value_Get_Bits$10;
  if(!(ld->load_non_intra_quantizer_matrix == 0))
  {
    i = 0;
    while(i < 64)
    {
      return_value_Get_Bits$10=Get_Bits(8);
      ld->non_intra_quantizer_matrix[(signed long int)scan[(signed long int)0][(signed long int)i]] = (signed int)return_value_Get_Bits$10;
      i = i + 1;
    }
  }

  else
  {
    i = 0;
    while(i < 64)
    {
      ld->non_intra_quantizer_matrix[(signed long int)i] = 16;
      i = i + 1;
    }
  }
  i = 0;
  while(i < 64)
  {
    ld->chroma_intra_quantizer_matrix[(signed long int)i] = ld->intra_quantizer_matrix[(signed long int)i];
    ld->chroma_non_intra_quantizer_matrix[(signed long int)i] = ld->non_intra_quantizer_matrix[(signed long int)i];
    i = i + 1;
  }
  extension_and_user_data();
}

// c::sequence_scalable_extension
// file src/gethdr.c line 789
static void sequence_scalable_extension(void)
{
  signed int pos = ld->Bitcnt;
  unsigned int return_value_Get_Bits$1;
  return_value_Get_Bits$1=Get_Bits(2);
  ld->scalable_mode = (signed int)(return_value_Get_Bits$1 + (unsigned int)1);
  unsigned int return_value_Get_Bits$2;
  return_value_Get_Bits$2=Get_Bits(4);
  layer_id = (signed int)return_value_Get_Bits$2;
  if(ld->scalable_mode == 2)
  {
    unsigned int return_value_Get_Bits$3;
    return_value_Get_Bits$3=Get_Bits(14);
    lower_layer_prediction_horizontal_size = (signed int)return_value_Get_Bits$3;
    marker_bit("sequence_scalable_extension()");
    unsigned int return_value_Get_Bits$4;
    return_value_Get_Bits$4=Get_Bits(14);
    lower_layer_prediction_vertical_size = (signed int)return_value_Get_Bits$4;
    unsigned int return_value_Get_Bits$5;
    return_value_Get_Bits$5=Get_Bits(5);
    horizontal_subsampling_factor_m = (signed int)return_value_Get_Bits$5;
    unsigned int return_value_Get_Bits$6;
    return_value_Get_Bits$6=Get_Bits(5);
    horizontal_subsampling_factor_n = (signed int)return_value_Get_Bits$6;
    unsigned int return_value_Get_Bits$7;
    return_value_Get_Bits$7=Get_Bits(5);
    vertical_subsampling_factor_m = (signed int)return_value_Get_Bits$7;
    unsigned int return_value_Get_Bits$8;
    return_value_Get_Bits$8=Get_Bits(5);
    vertical_subsampling_factor_n = (signed int)return_value_Get_Bits$8;
  }

  if(ld->scalable_mode == 4)
    Error("temporal scalability not implemented\n");

}

// c::slice_header
// file src/gethdr.c line 441
signed int slice_header(void)
{
  signed int slice_vertical_position_extension;
  signed int quantizer_scale_code;
  signed int pos;
  signed int slice_picture_id_enable = 0;
  signed int slice_picture_id = 0;
  signed int extra_information_slice = 0;
  pos = ld->Bitcnt;
  unsigned int tmp_if_expr$2;
  unsigned int return_value_Get_Bits$1;
  if(vertical_size > 2800 && !(ld->MPEG2_Flag == 0))
  {
    return_value_Get_Bits$1=Get_Bits(3);
    tmp_if_expr$2 = return_value_Get_Bits$1;
  }

  else
    tmp_if_expr$2 = (unsigned int)0;
  slice_vertical_position_extension = (signed int)tmp_if_expr$2;
  unsigned int return_value_Get_Bits$3;
  if(ld->scalable_mode == 1)
  {
    return_value_Get_Bits$3=Get_Bits(7);
    ld->priority_breakpoint = (signed int)return_value_Get_Bits$3;
  }

  unsigned int return_value_Get_Bits$4;
  return_value_Get_Bits$4=Get_Bits(5);
  quantizer_scale_code = (signed int)return_value_Get_Bits$4;
  signed int tmp_if_expr$6;
  signed int tmp_if_expr$5;
  if(!(ld->MPEG2_Flag == 0))
  {
    if(!(ld->q_scale_type == 0))
      tmp_if_expr$5 = (signed int)Non_Linear_quantizer_scale[(signed long int)quantizer_scale_code];

    else
      tmp_if_expr$5 = quantizer_scale_code << 1;
    tmp_if_expr$6 = tmp_if_expr$5;
  }

  else
    tmp_if_expr$6 = quantizer_scale_code;
  ld->quantizer_scale = tmp_if_expr$6;
  unsigned int return_value_Get_Bits$10;
  return_value_Get_Bits$10=Get_Bits(1);
  if(!(return_value_Get_Bits$10 == 0u))
  {
    unsigned int return_value_Get_Bits$7;
    return_value_Get_Bits$7=Get_Bits(1);
    ld->intra_slice = (signed int)return_value_Get_Bits$7;
    unsigned int return_value_Get_Bits$8;
    return_value_Get_Bits$8=Get_Bits(1);
    slice_picture_id_enable = (signed int)return_value_Get_Bits$8;
    unsigned int return_value_Get_Bits$9;
    return_value_Get_Bits$9=Get_Bits(6);
    slice_picture_id = (signed int)return_value_Get_Bits$9;
    extra_information_slice=extra_bit_information();
  }

  else
    ld->intra_slice = 0;
  return slice_vertical_position_extension;
}

// c::snprintf
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 61
signed int snprintf(char * restrict __s, unsigned long int __n, const char * restrict __fmt, ...)
{
  void *return_value___builtin_va_arg_pack$1;
  return_value___builtin_va_arg_pack$1=__builtin_va_arg_pack();
  signed int return_value___builtin___snprintf_chk$2;
  return_value___builtin___snprintf_chk$2=__builtin___snprintf_chk(__s, __n, 2 - 1, 18446744073709551615ul, __fmt, return_value___builtin_va_arg_pack$1);
  return return_value___builtin___snprintf_chk$2;
}

// c::sprintf
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 31
signed int sprintf(char * restrict __s, const char * restrict __fmt, ...)
{
  void *return_value___builtin_va_arg_pack$1;
  return_value___builtin_va_arg_pack$1=__builtin_va_arg_pack();
  signed int return_value___builtin___sprintf_chk$2;
  return_value___builtin___sprintf_chk$2=__builtin___sprintf_chk(__s, 2 - 1, 18446744073709551615ul, __fmt, return_value___builtin_va_arg_pack$1);
  return return_value___builtin___sprintf_chk$2;
}

// c::store_one
// file src/store.c line 144
static void store_one(char *outname, unsigned char **src, signed int offset, signed int incr, signed int height)
{
  switch(Output_Type)
  {

    case 0:
      {
        if(incr == Coded_Picture_Width)
          store_yuv_progressive(outname, src, offset, incr, height);

        else
          store_yuv(outname, src, offset, incr, height);
        goto __CPROVER_DUMP_L7;
      }
    case 1:
      {
        store_sif(outname, src, offset, incr, height);
        goto __CPROVER_DUMP_L7;
      }
    case 2:
      {
        store_ppm_tga(outname, src, offset, incr, height, 1);
        goto __CPROVER_DUMP_L7;
      }
    case 3:
      store_ppm_tga(outname, src, offset, incr, height, 0);
    default:

      __CPROVER_DUMP_L7:
        ;
  }
}

// c::store_ppm_tga
// file src/store.c line 365
static void store_ppm_tga(char *outname, unsigned char **src, signed int offset, signed int incr, signed int height, signed int tgaflag)
{
  static unsigned char tga24[14l] = { (unsigned char)0, (unsigned char)0, (unsigned char)2, (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)24, (unsigned char)32 };
  static unsigned char *u422;
  static unsigned char *u444;
  static unsigned char *v422;
  static unsigned char *v444;
  signed int i;
  signed int j;
  signed int y;
  signed int u;
  signed int v;
  signed int r;
  signed int g;
  signed int b;
  signed int crv;
  signed int cbu;
  signed int cgu;
  signed int cgv;
  unsigned char *py;
  unsigned char *pu;
  unsigned char *pv;
  char header[256l];
  if(chroma_format == 3)
  {
    u444 = src[(signed long int)1];
    v444 = src[(signed long int)2];
  }

  else
  {
    if(u444 == ((unsigned char *)NULL))
    {
      if(chroma_format == 1)
      {
        void *return_value_malloc$1;
        return_value_malloc$1=malloc((unsigned long int)((Coded_Picture_Width >> 1) * Coded_Picture_Height));
        u422 = (unsigned char *)return_value_malloc$1;
        if(u422 == ((unsigned char *)NULL))
          Error("malloc failed");

        void *return_value_malloc$2;
        return_value_malloc$2=malloc((unsigned long int)((Coded_Picture_Width >> 1) * Coded_Picture_Height));
        v422 = (unsigned char *)return_value_malloc$2;
        if(v422 == ((unsigned char *)NULL))
          Error("malloc failed");

      }

      void *return_value_malloc$3;
      return_value_malloc$3=malloc((unsigned long int)(Coded_Picture_Width * Coded_Picture_Height));
      u444 = (unsigned char *)return_value_malloc$3;
      if(u444 == ((unsigned char *)NULL))
        Error("malloc failed");

      void *return_value_malloc$4;
      return_value_malloc$4=malloc((unsigned long int)(Coded_Picture_Width * Coded_Picture_Height));
      v444 = (unsigned char *)return_value_malloc$4;
      if(v444 == ((unsigned char *)NULL))
        Error("malloc failed");

    }

    if(chroma_format == 1)
    {
      conv420to422(src[(signed long int)1], u422);
      conv420to422(src[(signed long int)2], v422);
      conv422to444(u422, u444);
      conv422to444(v422, v444);
    }

    else
    {
      conv422to444(src[(signed long int)1], u444);
      conv422to444(src[(signed long int)2], v444);
    }
  }
  strcat(outname, tgaflag != 0 ? ".tga" : ".ppm");
  if(Quiet_Flag == 0)
    fprintf(stderr, "saving %s\n", outname);

  outfile=open(outname, 64 | 512 | 1 | 0, 438);
  if(outfile == -1)
  {
    sprintf(Error_Text, "Couldn't create %s\n", outname);
    Error(Error_Text);
  }

  optr = obfr;
  if(!(tgaflag == 0))
  {
    i = 0;
    while(i < 12)
    {
      putbyte((signed int)tga24[(signed long int)i]);
      i = i + 1;
    }
    putword(horizontal_size);
    putword(height);
    putbyte((signed int)tga24[(signed long int)12]);
    putbyte((signed int)tga24[(signed long int)13]);
  }

  else
  {
    sprintf(header, "P6\n%d %d\n255\n", horizontal_size, height);
    i = 0;
    while(!((signed int)header[(signed long int)i] == 0))
    {
      putbyte((signed int)header[(signed long int)i]);
      i = i + 1;
    }
  }
  crv = Inverse_Table_6_9[(signed long int)matrix_coefficients][(signed long int)0];
  cbu = Inverse_Table_6_9[(signed long int)matrix_coefficients][(signed long int)1];
  cgu = Inverse_Table_6_9[(signed long int)matrix_coefficients][(signed long int)2];
  cgv = Inverse_Table_6_9[(signed long int)matrix_coefficients][(signed long int)3];
  i = 0;
  unsigned char *tmp_post$5;
  unsigned char *tmp_post$6;
  unsigned char *tmp_post$7;
  while(!(i >= height))
  {
    py = src[(signed long int)0] + (signed long int)offset + (signed long int)(incr * i);
    pu = u444 + (signed long int)offset + (signed long int)(incr * i);
    pv = v444 + (signed long int)offset + (signed long int)(incr * i);
    j = 0;
    while(!(j >= horizontal_size))
    {
      tmp_post$5 = pu;
      pu = pu + 1l;
      u = (signed int)*tmp_post$5 - 128;
      tmp_post$6 = pv;
      pv = pv + 1l;
      v = (signed int)*tmp_post$6 - 128;
      tmp_post$7 = py;
      py = py + 1l;
      y = 76309 * ((signed int)*tmp_post$7 - 16);
      r = (signed int)Clip[(signed long int)(y + crv * v + 32768 >> 16)];
      g = (signed int)Clip[(signed long int)(((y - cgu * u) - cgv * v) + 32768 >> 16)];
      b = (signed int)Clip[(signed long int)(y + cbu * u + 32786 >> 16)];
      if(!(tgaflag == 0))
      {
        putbyte(b);
        putbyte(g);
        putbyte(r);
      }

      else
      {
        putbyte(r);
        putbyte(g);
        putbyte(b);
      }
      j = j + 1;
    }
    i = i + 1;
  }
  if(!(optr == obfr))
    write(outfile, (const void *)obfr, (unsigned long int)(optr - obfr));

  close(outfile);
}

// c::store_sif
// file src/store.c line 295
static void store_sif(char *outname, unsigned char **src, signed int offset, signed int incr, signed int height)
{
  static unsigned char *u422;
  static unsigned char *v422;
  signed int i;
  signed int j;
  unsigned char *py;
  unsigned char *pu;
  unsigned char *pv;
  if(chroma_format == 3)
    Error("4:4:4 not supported for SIF format");

  if(chroma_format == 2)
  {
    u422 = src[(signed long int)1];
    v422 = src[(signed long int)2];
  }

  else
  {
    if(u422 == ((unsigned char *)NULL))
    {
      void *return_value_malloc$1;
      return_value_malloc$1=malloc((unsigned long int)((Coded_Picture_Width >> 1) * Coded_Picture_Height));
      u422 = (unsigned char *)return_value_malloc$1;
      if(u422 == ((unsigned char *)NULL))
        Error("malloc failed");

      void *return_value_malloc$2;
      return_value_malloc$2=malloc((unsigned long int)((Coded_Picture_Width >> 1) * Coded_Picture_Height));
      v422 = (unsigned char *)return_value_malloc$2;
      if(v422 == ((unsigned char *)NULL))
        Error("malloc failed");

    }

    conv420to422(src[(signed long int)1], u422);
    conv420to422(src[(signed long int)2], v422);
  }
  strcat(outname, (const void *)".SIF");
  if(Quiet_Flag == 0)
    fprintf(stderr, "saving %s\n", outname);

  outfile=open(outname, 64 | 512 | 1 | 0, 438);
  if(outfile == -1)
  {
    sprintf(Error_Text, "Couldn't create %s\n", outname);
    Error(Error_Text);
  }

  optr = obfr;
  i = 0;
  unsigned char *tmp_post$3;
  unsigned char *tmp_post$4;
  unsigned char *tmp_post$5;
  unsigned char *tmp_post$6;
  while(!(i >= height))
  {
    py = src[(signed long int)0] + (signed long int)offset + (signed long int)(incr * i);
    pu = u422 + (signed long int)(offset >> 1) + (signed long int)((incr >> 1) * i);
    pv = v422 + (signed long int)(offset >> 1) + (signed long int)((incr >> 1) * i);
    j = 0;
    while(!(j >= horizontal_size))
    {
      tmp_post$3 = pu;
      pu = pu + 1l;
      putbyte((signed int)*tmp_post$3);
      tmp_post$4 = py;
      py = py + 1l;
      putbyte((signed int)*tmp_post$4);
      tmp_post$5 = pv;
      pv = pv + 1l;
      putbyte((signed int)*tmp_post$5);
      tmp_post$6 = py;
      py = py + 1l;
      putbyte((signed int)*tmp_post$6);
      j = j + 2;
    }
    i = i + 1;
  }
  if(!(optr == obfr))
    write(outfile, (const void *)obfr, (unsigned long int)(optr - obfr));

  close(outfile);
}

// c::store_yuv
// file src/store.c line 229
static void store_yuv(char *outname, unsigned char **src, signed int offset, signed int incr, signed int height)
{
  signed int hsize;
  char tmpname[256l];
  hsize = horizontal_size;
  sprintf(tmpname, "%s.Y", outname);
  store_yuv1(tmpname, src[(signed long int)0], offset, incr, hsize, height);
  if(!(chroma_format == 3))
  {
    offset = offset >> 1;
    incr = incr >> 1;
    hsize = hsize >> 1;
  }

  if(chroma_format == 1)
    height = height >> 1;

  sprintf(tmpname, "%s.U", outname);
  store_yuv1(tmpname, src[(signed long int)1], offset, incr, hsize, height);
  sprintf(tmpname, "%s.V", outname);
  store_yuv1(tmpname, src[(signed long int)2], offset, incr, hsize, height);
}

// c::store_yuv1
// file src/store.c line 260
static void store_yuv1(char *name, unsigned char *src, signed int offset, signed int incr, signed int width, signed int height)
{
  signed int i;
  signed int j;
  unsigned char *p;
  if(Quiet_Flag == 0)
    fprintf(stderr, "saving %s\n", name);

  outfile=open(name, 64 | 512 | 1 | 0, 438);
  if(outfile == -1)
  {
    sprintf(Error_Text, "Couldn't create %s\n", name);
    Error(Error_Text);
  }

  optr = obfr;
  i = 0;
  unsigned char *tmp_post$1;
  while(!(i >= height))
  {
    p = src + (signed long int)offset + (signed long int)(incr * i);
    j = 0;
    while(!(j >= width))
    {
      tmp_post$1 = p;
      p = p + 1l;
      putbyte((signed int)*tmp_post$1);
      j = j + 1;
    }
    i = i + 1;
  }
  if(!(optr == obfr))
    write(outfile, (const void *)obfr, (unsigned long int)(optr - obfr));

  close(outfile);
}

// c::store_yuv_progressive
// file src/store.c line 198
static void store_yuv_progressive(char *outname, unsigned char **src, signed int offset, signed int incr, signed int height)
{
  signed int hsize;
  char tmpname[256l];
  hsize = horizontal_size;
  sprintf(tmpname, "%s.Y", outname);
  store_yuvp(tmpname, src[(signed long int)0], offset, incr, hsize, height);
  if(!(chroma_format == 3))
  {
    offset = offset >> 1;
    incr = incr >> 1;
    hsize = hsize >> 1;
  }

  if(chroma_format == 1)
    height = height >> 1;

  sprintf(tmpname, "%s.U", outname);
  store_yuvp(tmpname, src[(signed long int)1], offset, incr, hsize, height);
  sprintf(tmpname, "%s.V", outname);
  store_yuvp(tmpname, src[(signed long int)2], offset, incr, hsize, height);
}

// c::store_yuvp
// file src/store.c line 176
static void store_yuvp(char *name, unsigned char *src, signed int offset, signed int incr, signed int width, signed int height)
{
  signed int i;
  signed int j;
  unsigned char *p;
  if(Quiet_Flag == 0)
    fprintf(stderr, "saving %s\n", name);

  outfile=open(name, 64 | 512 | 1 | 0, 438);
  if(outfile == -1)
  {
    sprintf(Error_Text, "Couldn't create %s\n", name);
    Error(Error_Text);
  }

  signed long int return_value_write$1;
  return_value_write$1=write(outfile, (const void *)src, (unsigned long int)(width * height));
  if(return_value_write$1 == (signed long int)height * (signed long int)width)
    (void)0;

  else
    /* assertion write(outfile,src,width*height)==width*height && "frame write problem\n" */
    assert(FALSE);
  close(outfile);
}

// c::tolower
// file /usr/include/ctype.h line 216
signed int tolower(signed int __c)
{
  signed int tmp_if_expr$2;
  const signed int **return_value___ctype_tolower_loc$1;
  if(__c >= -128)
  {
    if(!(__c < 256))
      goto __CPROVER_DUMP_L1;

    return_value___ctype_tolower_loc$1=__ctype_tolower_loc();
    tmp_if_expr$2 = (*return_value___ctype_tolower_loc$1)[(signed long int)__c];
  }

  else
  {

  __CPROVER_DUMP_L1:
    ;
    tmp_if_expr$2 = __c;
  }
  return tmp_if_expr$2;
}

// c::toupper
// file /usr/include/ctype.h line 222
signed int toupper(signed int __c)
{
  signed int tmp_if_expr$2;
  const signed int **return_value___ctype_toupper_loc$1;
  if(__c >= -128)
  {
    if(!(__c < 256))
      goto __CPROVER_DUMP_L1;

    return_value___ctype_toupper_loc$1=__ctype_toupper_loc();
    tmp_if_expr$2 = (*return_value___ctype_toupper_loc$1)[(signed long int)__c];
  }

  else
  {

  __CPROVER_DUMP_L1:
    ;
    tmp_if_expr$2 = __c;
  }
  return tmp_if_expr$2;
}

// c::ttyname_r
// file /usr/include/x86_64-linux-gnu/bits/unistd.h line 291
signed int ttyname_r(signed int __fd, char *__buf, unsigned long int __buflen)
{
  signed int return_value___ttyname_r_chk$1;
  signed int return_value___ttyname_r_chk_warn$2;
  signed int return_value___ttyname_r_alias$3;
  return_value___ttyname_r_alias$3=__ttyname_r_alias(__fd, __buf, __buflen);
  return return_value___ttyname_r_alias$3;
}

// c::user_data
// file src/gethdr.c line 1099
static void user_data(void)
{
  next_start_code();
}

// c::vdprintf
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 150
signed int vdprintf(signed int __fd, const char * restrict __fmt, void **__ap)
{
  signed int return_value___vdprintf_chk$1;
  return_value___vdprintf_chk$1=__vdprintf_chk(__fd, 2 - 1, __fmt, __ap);
  return return_value___vdprintf_chk$1;
}

// c::vfprintf
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 124
signed int vfprintf(struct _IO_FILE * restrict __stream, const char * restrict __fmt, void **__ap)
{
  signed int return_value___vfprintf_chk$1;
  return_value___vfprintf_chk$1=__vfprintf_chk(__stream, 2 - 1, __fmt, __ap);
  return return_value___vfprintf_chk$1;
}

// c::video_sequence
// file src/mpeg2dec.c line 736
static signed int video_sequence(signed int *Bitstream_Framenumber)
{
  signed int Bitstream_Framenum;
  signed int Sequence_Framenum;
  signed int Return_Value;
  Bitstream_Framenum = *Bitstream_Framenumber;
  Sequence_Framenum = 0;
  Initialize_Sequence();
  Decode_Picture(Bitstream_Framenum, Sequence_Framenum);
  if(Second_Field == 0)
  {
    Bitstream_Framenum = Bitstream_Framenum + 1;
    Sequence_Framenum = Sequence_Framenum + 1;
  }

  do
  {
    Return_Value=Headers();
    if(Return_Value == 0)
      goto __CPROVER_DUMP_L3;

    Decode_Picture(Bitstream_Framenum, Sequence_Framenum);
    if(Second_Field == 0)
    {
      Bitstream_Framenum = Bitstream_Framenum + 1;
      Sequence_Framenum = Sequence_Framenum + 1;
    }

  }
  while(TRUE);

__CPROVER_DUMP_L3:
  ;
  if(!(Sequence_Framenum == 0))
    Output_Last_Frame_of_Sequence(Bitstream_Framenum);

  Deinitialize_Sequence();
  *Bitstream_Framenumber = Bitstream_Framenum;
  return Return_Value;
}

// c::vprintf
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 114
signed int vprintf(const char * restrict __fmt, void **__ap)
{
  signed int return_value___vfprintf_chk$1;
  return_value___vfprintf_chk$1=__vfprintf_chk(stdout, 2 - 1, __fmt, __ap);
  return return_value___vfprintf_chk$1;
}

// c::vsnprintf
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 74
signed int vsnprintf(char * restrict __s, unsigned long int __n, const char * restrict __fmt, void **__ap)
{
  signed int return_value___builtin___vsnprintf_chk$1;
  return_value___builtin___vsnprintf_chk$1=__builtin___vsnprintf_chk(__s, __n, 2 - 1, 18446744073709551615ul, __fmt, __ap);
  return return_value___builtin___vsnprintf_chk$1;
}

// c::vsprintf
// file /usr/include/x86_64-linux-gnu/bits/stdio2.h line 43
signed int vsprintf(char * restrict __s, const char * restrict __fmt, void **__ap)
{
  signed int return_value___builtin___vsprintf_chk$1;
  return_value___builtin___vsprintf_chk$1=__builtin___vsprintf_chk(__s, 2 - 1, 18446744073709551615ul, __fmt, __ap);
  return return_value___builtin___vsprintf_chk$1;
}

// c::wcstombs
// file /usr/include/x86_64-linux-gnu/bits/stdlib.h line 144
unsigned long int wcstombs(char * restrict __dst, const signed int * restrict __src, unsigned long int __len)
{
  unsigned long int return_value___wcstombs_chk$1;
  unsigned long int return_value___wcstombs_chk_warn$2;
  unsigned long int return_value___wcstombs_alias$3;
  return_value___wcstombs_alias$3=__wcstombs_alias(__dst, __src, __len);
  return return_value___wcstombs_alias$3;
}

// c::wctomb
// file /usr/include/x86_64-linux-gnu/bits/stdlib.h line 83
signed int wctomb(char *__s, signed int __wchar)
{
  signed int return_value___wctomb_chk$1;
  signed int return_value___wctomb_alias$2;
  return_value___wctomb_alias$2=__wctomb_alias(__s, __wchar);
  return return_value___wctomb_alias$2;
}

// c::write_frame_buf32
// file src/getpic.c line 1448
void write_frame_buf32(signed int t, unsigned int data)
{
  write_frame_buf8(t, (unsigned char)(data >> 24));
  write_frame_buf8(t, (unsigned char)(data >> 16));
  write_frame_buf8(t, (unsigned char)(data >> 8));
  write_frame_buf8(t, (unsigned char)data);
}

// c::write_frame_buf8
// file src/getpic.c line 1428
void write_frame_buf8(signed int t, unsigned char data)
{
  if(tb[(signed long int)t].frame_buf_offset == tb[(signed long int)t].frame_buf_size)
  {
    tb[(signed long int)t].frame_buf_size = tb[(signed long int)t].frame_buf_size << 1;
    void *return_value_realloc$1;
    return_value_realloc$1=realloc((void *)tb[(signed long int)t].frame_buf, 1ul /*[[unsigned char]]*/ * (unsigned long int)tb[(signed long int)t].frame_buf_size);
    tb[(signed long int)t].frame_buf = (unsigned char *)return_value_realloc$1;
  }

  unsigned int tmp_post$2 = tb[(signed long int)t].frame_buf_offset;
  tb[(signed long int)t].frame_buf_offset = tb[(signed long int)t].frame_buf_offset + 1u;
  tb[(signed long int)t].frame_buf[(signed long int)tmp_post$2] = data;
}

