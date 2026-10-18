// Lean compiler output
// Module: CreditUsage
// Imports: public import Init
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
LEAN_EXPORT lean_object* lp_RequestProject_Twin_creditStatus(lean_object*);
static lean_object* lp_RequestProject_Twin_creditStatus___closed__0;
static lean_object* lp_RequestProject_Twin_creditStatus___closed__2;
LEAN_EXPORT lean_object* lp_RequestProject_Twin_contextWithCredit;
static lean_object* lp_RequestProject_Twin_creditTracking___closed__3;
static lean_object* lp_RequestProject_Twin_creditTracking___closed__0;
LEAN_EXPORT lean_object* lp_RequestProject_Twin_creditCritical;
static lean_object* lp_RequestProject_Twin_creditStatus___closed__1;
LEAN_EXPORT lean_object* lp_RequestProject_Twin_creditTracking;
LEAN_EXPORT lean_object* lp_RequestProject_Twin_creditWarning;
static lean_object* lp_RequestProject_Twin_sessionTokenCount___closed__0;
static lean_object* lp_RequestProject_Twin_creditTracking___closed__2;
static lean_object* lp_RequestProject_Twin_creditTracking___closed__1;
static lean_object* lp_RequestProject_Twin_contextWithCredit___closed__0;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_Twin_creditStatus___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_Twin_sessionTokenCount;
static lean_object* _init_lp_RequestProject_Twin_creditWarning() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(75u);
return x_1;
}
}
static lean_object* _init_lp_RequestProject_Twin_creditCritical() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(90u);
return x_1;
}
}
static lean_object* _init_lp_RequestProject_Twin_creditStatus___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("active", 6, 6);
return x_1;
}
}
static lean_object* _init_lp_RequestProject_Twin_creditStatus___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("caution", 7, 7);
return x_1;
}
}
static lean_object* _init_lp_RequestProject_Twin_creditStatus___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("critical", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_RequestProject_Twin_creditStatus(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_unsigned_to_nat(90u);
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(75u);
x_6 = lean_nat_dec_le(x_5, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lp_RequestProject_Twin_creditStatus___closed__0;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lp_RequestProject_Twin_creditStatus___closed__1;
return x_8;
}
}
else
{
lean_object* x_9; 
x_9 = lp_RequestProject_Twin_creditStatus___closed__2;
return x_9;
}
}
}
LEAN_EXPORT lean_object* lp_RequestProject_Twin_creditStatus___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_RequestProject_Twin_creditStatus(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_lp_RequestProject_Twin_creditTracking___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Active", 6, 6);
return x_1;
}
}
static lean_object* _init_lp_RequestProject_Twin_creditTracking___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("minimize tool calls, batch operations, cache locally", 52, 52);
return x_1;
}
}
static lean_object* _init_lp_RequestProject_Twin_creditTracking___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("2026-09-17", 10, 10);
return x_1;
}
}
static lean_object* _init_lp_RequestProject_Twin_creditTracking___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lp_RequestProject_Twin_creditTracking___closed__2;
x_2 = lp_RequestProject_Twin_creditTracking___closed__1;
x_3 = lp_RequestProject_Twin_creditTracking___closed__0;
x_4 = lean_unsigned_to_nat(65u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_lp_RequestProject_Twin_creditTracking() {
_start:
{
lean_object* x_1; 
x_1 = lp_RequestProject_Twin_creditTracking___closed__3;
return x_1;
}
}
static lean_object* _init_lp_RequestProject_Twin_sessionTokenCount___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(143u);
x_3 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
return x_3;
}
}
static lean_object* _init_lp_RequestProject_Twin_sessionTokenCount() {
_start:
{
lean_object* x_1; 
x_1 = lp_RequestProject_Twin_sessionTokenCount___closed__0;
return x_1;
}
}
static lean_object* _init_lp_RequestProject_Twin_contextWithCredit___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_RequestProject_Twin_sessionTokenCount;
x_2 = lp_RequestProject_Twin_creditTracking;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_RequestProject_Twin_contextWithCredit() {
_start:
{
lean_object* x_1; 
x_1 = lp_RequestProject_Twin_contextWithCredit___closed__0;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_CreditUsage(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_RequestProject_Twin_creditWarning = _init_lp_RequestProject_Twin_creditWarning();
lean_mark_persistent(lp_RequestProject_Twin_creditWarning);
lp_RequestProject_Twin_creditCritical = _init_lp_RequestProject_Twin_creditCritical();
lean_mark_persistent(lp_RequestProject_Twin_creditCritical);
lp_RequestProject_Twin_creditStatus___closed__0 = _init_lp_RequestProject_Twin_creditStatus___closed__0();
lean_mark_persistent(lp_RequestProject_Twin_creditStatus___closed__0);
lp_RequestProject_Twin_creditStatus___closed__1 = _init_lp_RequestProject_Twin_creditStatus___closed__1();
lean_mark_persistent(lp_RequestProject_Twin_creditStatus___closed__1);
lp_RequestProject_Twin_creditStatus___closed__2 = _init_lp_RequestProject_Twin_creditStatus___closed__2();
lean_mark_persistent(lp_RequestProject_Twin_creditStatus___closed__2);
lp_RequestProject_Twin_creditTracking___closed__0 = _init_lp_RequestProject_Twin_creditTracking___closed__0();
lean_mark_persistent(lp_RequestProject_Twin_creditTracking___closed__0);
lp_RequestProject_Twin_creditTracking___closed__1 = _init_lp_RequestProject_Twin_creditTracking___closed__1();
lean_mark_persistent(lp_RequestProject_Twin_creditTracking___closed__1);
lp_RequestProject_Twin_creditTracking___closed__2 = _init_lp_RequestProject_Twin_creditTracking___closed__2();
lean_mark_persistent(lp_RequestProject_Twin_creditTracking___closed__2);
lp_RequestProject_Twin_creditTracking___closed__3 = _init_lp_RequestProject_Twin_creditTracking___closed__3();
lean_mark_persistent(lp_RequestProject_Twin_creditTracking___closed__3);
lp_RequestProject_Twin_creditTracking = _init_lp_RequestProject_Twin_creditTracking();
lean_mark_persistent(lp_RequestProject_Twin_creditTracking);
lp_RequestProject_Twin_sessionTokenCount___closed__0 = _init_lp_RequestProject_Twin_sessionTokenCount___closed__0();
lean_mark_persistent(lp_RequestProject_Twin_sessionTokenCount___closed__0);
lp_RequestProject_Twin_sessionTokenCount = _init_lp_RequestProject_Twin_sessionTokenCount();
lean_mark_persistent(lp_RequestProject_Twin_sessionTokenCount);
lp_RequestProject_Twin_contextWithCredit___closed__0 = _init_lp_RequestProject_Twin_contextWithCredit___closed__0();
lean_mark_persistent(lp_RequestProject_Twin_contextWithCredit___closed__0);
lp_RequestProject_Twin_contextWithCredit = _init_lp_RequestProject_Twin_contextWithCredit();
lean_mark_persistent(lp_RequestProject_Twin_contextWithCredit);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
