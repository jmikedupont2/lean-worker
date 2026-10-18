// Lean compiler output
// Module: CommandExecution
// Imports: public import Init public import Std
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* lp_RequestProject_CommandExecution_resultSummary___closed__1;
static lean_object* lp_RequestProject_CommandExecution_resultSummary___closed__0;
lean_object* l_List_lengthTR___redArg(lean_object*);
static lean_object* lp_RequestProject_CommandExecution_exampleLog___closed__5;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* lp_RequestProject_CommandExecution_resultSummarized___closed__1;
LEAN_EXPORT lean_object* lp_RequestProject_CommandExecution_contextBudget;
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CommandExecution_resultFitsBudget___boxed(lean_object*);
static lean_object* lp_RequestProject_CommandExecution_exampleLog___closed__7;
static lean_object* lp_RequestProject_CommandExecution_resultSummary___closed__2;
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* lp_RequestProject_CommandExecution_stringTake___closed__0;
lean_object* l_String_splitOnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_RequestProject_CommandExecution_resultSummary___closed__3;
static lean_object* lp_RequestProject_CommandExecution_exampleLog___closed__3;
static lean_object* lp_RequestProject_CommandExecution_exampleLog___closed__2;
static lean_object* lp_RequestProject_CommandExecution_resultSummary___closed__6;
LEAN_EXPORT lean_object* lp_RequestProject_CommandExecution_resultSummarized(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CommandExecution_truncateString(lean_object*, lean_object*);
static lean_object* lp_RequestProject_CommandExecution_resultSummarized___closed__0;
static lean_object* lp_RequestProject_CommandExecution_exampleLog___closed__9;
LEAN_EXPORT lean_object* lp_RequestProject_CommandExecution_ExecResultBounded;
LEAN_EXPORT lean_object* lp_RequestProject_CommandExecution_stringTake(lean_object*, lean_object*);
static lean_object* lp_RequestProject_CommandExecution_truncateString___closed__0;
lean_object* lean_string_data(lean_object*);
static lean_object* lp_RequestProject_CommandExecution_exampleLog___closed__0;
static lean_object* lp_RequestProject_CommandExecution_exampleLog___closed__1;
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_RequestProject_CommandExecution_resultFitsBudget(lean_object*);
static lean_object* lp_RequestProject_CommandExecution_exampleLog___closed__10;
static lean_object* lp_RequestProject_CommandExecution_resultSummary___closed__5;
LEAN_EXPORT lean_object* lp_RequestProject_CommandExecution_exampleLog;
static lean_object* lp_RequestProject_CommandExecution_exampleLog___closed__4;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* lp_RequestProject_CommandExecution_exampleLog___closed__6;
static lean_object* lp_RequestProject_CommandExecution_exampleLog___closed__8;
static lean_object* lp_RequestProject_CommandExecution_resultSummary___closed__4;
LEAN_EXPORT lean_object* lp_RequestProject_CommandExecution_makeResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_mk(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CommandExecution_resultSummary(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* lp_RequestProject_CommandExecution_resultSummary___closed__7;
static lean_object* _init_lp_RequestProject_CommandExecution_ExecResultBounded() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(5000u);
return x_1;
}
}
static lean_object* _init_lp_RequestProject_CommandExecution_stringTake___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CommandExecution_stringTake(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_string_data(x_1);
x_4 = lp_RequestProject_CommandExecution_stringTake___closed__0;
lean_inc(x_3);
x_5 = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(x_3, x_3, x_2, x_4);
lean_dec(x_3);
x_6 = lean_string_mk(x_5);
return x_6;
}
}
static lean_object* _init_lp_RequestProject_CommandExecution_truncateString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("...", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CommandExecution_truncateString(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_string_length(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = lean_box(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lp_RequestProject_CommandExecution_stringTake(x_2, x_1);
x_8 = lp_RequestProject_CommandExecution_truncateString___closed__0;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_box(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CommandExecution_makeResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_unsigned_to_nat(5000u);
x_7 = lp_RequestProject_CommandExecution_truncateString(x_6, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lp_RequestProject_CommandExecution_truncateString(x_6, x_4);
x_11 = lean_unbox(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_8);
lean_ctor_set(x_14, 3, x_12);
lean_ctor_set(x_14, 4, x_5);
x_15 = lean_unbox(x_13);
lean_dec(x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*5, x_15);
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec_ref(x_10);
x_17 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_8);
lean_ctor_set(x_17, 3, x_16);
lean_ctor_set(x_17, 4, x_5);
x_18 = lean_unbox(x_9);
lean_dec(x_9);
lean_ctor_set_uint8(x_17, sizeof(void*)*5, x_18);
return x_17;
}
}
}
static lean_object* _init_lp_RequestProject_CommandExecution_resultSummary___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ERR ", 4, 4);
return x_1;
}
}
static lean_object* _init_lp_RequestProject_CommandExecution_resultSummary___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" code=", 6, 6);
return x_1;
}
}
static lean_object* _init_lp_RequestProject_CommandExecution_resultSummary___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
static lean_object* _init_lp_RequestProject_CommandExecution_resultSummary___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("OK ", 3, 3);
return x_1;
}
}
static lean_object* _init_lp_RequestProject_CommandExecution_resultSummary___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" lines=", 7, 7);
return x_1;
}
}
static lean_object* _init_lp_RequestProject_CommandExecution_resultSummary___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_lp_RequestProject_CommandExecution_resultSummary___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" duration=", 10, 10);
return x_1;
}
}
static lean_object* _init_lp_RequestProject_CommandExecution_resultSummary___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ms", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CommandExecution_resultSummary(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_8 = lp_RequestProject_CommandExecution_resultSummary___closed__0;
x_9 = lean_string_append(x_8, x_2);
lean_dec_ref(x_2);
x_10 = lp_RequestProject_CommandExecution_resultSummary___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Nat_reprFast(x_3);
x_13 = lean_string_append(x_11, x_12);
lean_dec_ref(x_12);
x_14 = lp_RequestProject_CommandExecution_resultSummary___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_unsigned_to_nat(80u);
x_17 = lp_RequestProject_CommandExecution_stringTake(x_4, x_16);
x_18 = lean_string_append(x_15, x_17);
lean_dec_ref(x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_3);
x_19 = lp_RequestProject_CommandExecution_resultSummary___closed__3;
x_20 = lean_string_append(x_19, x_2);
lean_dec_ref(x_2);
x_21 = lp_RequestProject_CommandExecution_resultSummary___closed__4;
x_22 = lean_string_append(x_20, x_21);
x_23 = lp_RequestProject_CommandExecution_resultSummary___closed__5;
x_24 = lean_box(0);
x_25 = l_String_splitOnAux(x_4, x_23, x_6, x_6, x_6, x_24);
lean_dec_ref(x_4);
x_26 = l_List_lengthTR___redArg(x_25);
lean_dec(x_25);
x_27 = l_Nat_reprFast(x_26);
x_28 = lean_string_append(x_22, x_27);
lean_dec_ref(x_27);
x_29 = lp_RequestProject_CommandExecution_resultSummary___closed__6;
x_30 = lean_string_append(x_28, x_29);
x_31 = l_Nat_reprFast(x_5);
x_32 = lean_string_append(x_30, x_31);
lean_dec_ref(x_31);
x_33 = lp_RequestProject_CommandExecution_resultSummary___closed__7;
x_34 = lean_string_append(x_32, x_33);
return x_34;
}
}
}
static lean_object* _init_lp_RequestProject_CommandExecution_contextBudget() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1500u);
return x_1;
}
}
LEAN_EXPORT uint8_t lp_RequestProject_CommandExecution_resultFitsBudget(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_1, 3);
x_4 = lean_string_length(x_2);
x_5 = lean_string_length(x_3);
x_6 = lean_nat_add(x_4, x_5);
x_7 = lean_unsigned_to_nat(1500u);
x_8 = lean_nat_dec_le(x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CommandExecution_resultFitsBudget___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_RequestProject_CommandExecution_resultFitsBudget(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_lp_RequestProject_CommandExecution_resultSummarized___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("TRUNCATED[", 10, 10);
return x_1;
}
}
static lean_object* _init_lp_RequestProject_CommandExecution_resultSummarized___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" chars]", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_CommandExecution_resultSummarized(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lp_RequestProject_CommandExecution_resultFitsBudget(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lp_RequestProject_CommandExecution_resultSummarized___closed__0;
x_5 = lean_string_length(x_3);
x_6 = l_Nat_reprFast(x_5);
x_7 = lean_string_append(x_4, x_6);
lean_dec_ref(x_6);
x_8 = lp_RequestProject_CommandExecution_resultSummarized___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_unsigned_to_nat(200u);
x_11 = lp_RequestProject_CommandExecution_stringTake(x_3, x_10);
x_12 = lean_string_append(x_9, x_11);
lean_dec_ref(x_11);
x_13 = lp_RequestProject_CommandExecution_truncateString___closed__0;
x_14 = lean_string_append(x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_15);
lean_dec_ref(x_1);
return x_15;
}
}
}
static lean_object* _init_lp_RequestProject_CommandExecution_exampleLog___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ls /opt/baal-agent/workspace", 28, 28);
return x_1;
}
}
static lean_object* _init_lp_RequestProject_CommandExecution_exampleLog___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("MEMORY.md\nTwin.lean\nCommandExecution.lean", 41, 41);
return x_1;
}
}
static lean_object* _init_lp_RequestProject_CommandExecution_exampleLog___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_lp_RequestProject_CommandExecution_exampleLog___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lp_RequestProject_CommandExecution_exampleLog___closed__2;
x_3 = lp_RequestProject_CommandExecution_exampleLog___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lp_RequestProject_CommandExecution_exampleLog___closed__0;
x_6 = lp_RequestProject_CommandExecution_makeResult(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_lp_RequestProject_CommandExecution_exampleLog___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = lp_RequestProject_CommandExecution_exampleLog___closed__3;
x_3 = lp_RequestProject_CommandExecution_exampleLog___closed__0;
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_1);
return x_5;
}
}
static lean_object* _init_lp_RequestProject_CommandExecution_exampleLog___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("git status --short", 18, 18);
return x_1;
}
}
static lean_object* _init_lp_RequestProject_CommandExecution_exampleLog___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("M Twin.lean\nA CommandExecution.lean", 35, 35);
return x_1;
}
}
static lean_object* _init_lp_RequestProject_CommandExecution_exampleLog___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lp_RequestProject_CommandExecution_exampleLog___closed__2;
x_3 = lp_RequestProject_CommandExecution_exampleLog___closed__6;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lp_RequestProject_CommandExecution_exampleLog___closed__5;
x_6 = lp_RequestProject_CommandExecution_makeResult(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_lp_RequestProject_CommandExecution_exampleLog___closed__8() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = lp_RequestProject_CommandExecution_exampleLog___closed__7;
x_3 = lp_RequestProject_CommandExecution_exampleLog___closed__5;
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_1);
return x_5;
}
}
static lean_object* _init_lp_RequestProject_CommandExecution_exampleLog___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lp_RequestProject_CommandExecution_exampleLog___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_RequestProject_CommandExecution_exampleLog___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_RequestProject_CommandExecution_exampleLog___closed__9;
x_2 = lp_RequestProject_CommandExecution_exampleLog___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_RequestProject_CommandExecution_exampleLog() {
_start:
{
lean_object* x_1; 
x_1 = lp_RequestProject_CommandExecution_exampleLog___closed__10;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Std(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_CommandExecution(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_RequestProject_CommandExecution_ExecResultBounded = _init_lp_RequestProject_CommandExecution_ExecResultBounded();
lean_mark_persistent(lp_RequestProject_CommandExecution_ExecResultBounded);
lp_RequestProject_CommandExecution_stringTake___closed__0 = _init_lp_RequestProject_CommandExecution_stringTake___closed__0();
lean_mark_persistent(lp_RequestProject_CommandExecution_stringTake___closed__0);
lp_RequestProject_CommandExecution_truncateString___closed__0 = _init_lp_RequestProject_CommandExecution_truncateString___closed__0();
lean_mark_persistent(lp_RequestProject_CommandExecution_truncateString___closed__0);
lp_RequestProject_CommandExecution_resultSummary___closed__0 = _init_lp_RequestProject_CommandExecution_resultSummary___closed__0();
lean_mark_persistent(lp_RequestProject_CommandExecution_resultSummary___closed__0);
lp_RequestProject_CommandExecution_resultSummary___closed__1 = _init_lp_RequestProject_CommandExecution_resultSummary___closed__1();
lean_mark_persistent(lp_RequestProject_CommandExecution_resultSummary___closed__1);
lp_RequestProject_CommandExecution_resultSummary___closed__2 = _init_lp_RequestProject_CommandExecution_resultSummary___closed__2();
lean_mark_persistent(lp_RequestProject_CommandExecution_resultSummary___closed__2);
lp_RequestProject_CommandExecution_resultSummary___closed__3 = _init_lp_RequestProject_CommandExecution_resultSummary___closed__3();
lean_mark_persistent(lp_RequestProject_CommandExecution_resultSummary___closed__3);
lp_RequestProject_CommandExecution_resultSummary___closed__4 = _init_lp_RequestProject_CommandExecution_resultSummary___closed__4();
lean_mark_persistent(lp_RequestProject_CommandExecution_resultSummary___closed__4);
lp_RequestProject_CommandExecution_resultSummary___closed__5 = _init_lp_RequestProject_CommandExecution_resultSummary___closed__5();
lean_mark_persistent(lp_RequestProject_CommandExecution_resultSummary___closed__5);
lp_RequestProject_CommandExecution_resultSummary___closed__6 = _init_lp_RequestProject_CommandExecution_resultSummary___closed__6();
lean_mark_persistent(lp_RequestProject_CommandExecution_resultSummary___closed__6);
lp_RequestProject_CommandExecution_resultSummary___closed__7 = _init_lp_RequestProject_CommandExecution_resultSummary___closed__7();
lean_mark_persistent(lp_RequestProject_CommandExecution_resultSummary___closed__7);
lp_RequestProject_CommandExecution_contextBudget = _init_lp_RequestProject_CommandExecution_contextBudget();
lean_mark_persistent(lp_RequestProject_CommandExecution_contextBudget);
lp_RequestProject_CommandExecution_resultSummarized___closed__0 = _init_lp_RequestProject_CommandExecution_resultSummarized___closed__0();
lean_mark_persistent(lp_RequestProject_CommandExecution_resultSummarized___closed__0);
lp_RequestProject_CommandExecution_resultSummarized___closed__1 = _init_lp_RequestProject_CommandExecution_resultSummarized___closed__1();
lean_mark_persistent(lp_RequestProject_CommandExecution_resultSummarized___closed__1);
lp_RequestProject_CommandExecution_exampleLog___closed__0 = _init_lp_RequestProject_CommandExecution_exampleLog___closed__0();
lean_mark_persistent(lp_RequestProject_CommandExecution_exampleLog___closed__0);
lp_RequestProject_CommandExecution_exampleLog___closed__1 = _init_lp_RequestProject_CommandExecution_exampleLog___closed__1();
lean_mark_persistent(lp_RequestProject_CommandExecution_exampleLog___closed__1);
lp_RequestProject_CommandExecution_exampleLog___closed__2 = _init_lp_RequestProject_CommandExecution_exampleLog___closed__2();
lean_mark_persistent(lp_RequestProject_CommandExecution_exampleLog___closed__2);
lp_RequestProject_CommandExecution_exampleLog___closed__3 = _init_lp_RequestProject_CommandExecution_exampleLog___closed__3();
lean_mark_persistent(lp_RequestProject_CommandExecution_exampleLog___closed__3);
lp_RequestProject_CommandExecution_exampleLog___closed__4 = _init_lp_RequestProject_CommandExecution_exampleLog___closed__4();
lean_mark_persistent(lp_RequestProject_CommandExecution_exampleLog___closed__4);
lp_RequestProject_CommandExecution_exampleLog___closed__5 = _init_lp_RequestProject_CommandExecution_exampleLog___closed__5();
lean_mark_persistent(lp_RequestProject_CommandExecution_exampleLog___closed__5);
lp_RequestProject_CommandExecution_exampleLog___closed__6 = _init_lp_RequestProject_CommandExecution_exampleLog___closed__6();
lean_mark_persistent(lp_RequestProject_CommandExecution_exampleLog___closed__6);
lp_RequestProject_CommandExecution_exampleLog___closed__7 = _init_lp_RequestProject_CommandExecution_exampleLog___closed__7();
lean_mark_persistent(lp_RequestProject_CommandExecution_exampleLog___closed__7);
lp_RequestProject_CommandExecution_exampleLog___closed__8 = _init_lp_RequestProject_CommandExecution_exampleLog___closed__8();
lean_mark_persistent(lp_RequestProject_CommandExecution_exampleLog___closed__8);
lp_RequestProject_CommandExecution_exampleLog___closed__9 = _init_lp_RequestProject_CommandExecution_exampleLog___closed__9();
lean_mark_persistent(lp_RequestProject_CommandExecution_exampleLog___closed__9);
lp_RequestProject_CommandExecution_exampleLog___closed__10 = _init_lp_RequestProject_CommandExecution_exampleLog___closed__10();
lean_mark_persistent(lp_RequestProject_CommandExecution_exampleLog___closed__10);
lp_RequestProject_CommandExecution_exampleLog = _init_lp_RequestProject_CommandExecution_exampleLog();
lean_mark_persistent(lp_RequestProject_CommandExecution_exampleLog);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
