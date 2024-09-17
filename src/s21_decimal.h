#ifndef TESTS_TEST_DECIMAL_H
#define TESTS_TEST_DECIMAL_H

#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#define SIGN_MASK 0x80000000
#define GET_MASK 0x00000001
#define GET_EXP_MASK 0x000000ff
#define MAX_INT 0xffffffff
#define SIGN_SHIFT 31
#define EXP_SHIFT 16
#define s21_MAXDEC 2e96 - 1
#define s21_MAXEXP 28

typedef struct {
  unsigned int bits[4];
} s21_decimal;

typedef struct {
  int sign;
  int exp;
  unsigned int bits[6];
} s21_big_decimal;

typedef union {
  int ui;
  float fl;
} floatbits;

int s21_add(s21_decimal value_1, s21_decimal value_2, s21_decimal *result);
int s21_sub(s21_decimal value_1, s21_decimal value_2, s21_decimal *result);
int s21_mul(s21_decimal value_1, s21_decimal value_2, s21_decimal *result);
int s21_div(s21_decimal value_1, s21_decimal value_2, s21_decimal *result);

int s21_is_less(s21_decimal vValueOne, s21_decimal vValueTwo);
int s21_is_less_or_equal(s21_decimal, s21_decimal);
int s21_is_greater(s21_decimal, s21_decimal);
int s21_is_greater_or_equal(s21_decimal, s21_decimal);
int s21_is_equal(s21_decimal, s21_decimal);
int s21_is_not_equal(s21_decimal, s21_decimal);

int s21_from_int_to_decimal(int src, s21_decimal *dst);
int s21_from_float_to_decimal(float src, s21_decimal *dst);
int s21_from_decimal_to_int(s21_decimal src, int *dst);
int s21_from_decimal_to_float(s21_decimal src, float *dst);

int s21_floor(s21_decimal value, s21_decimal *result);
int s21_round(s21_decimal value, s21_decimal *result);
int s21_truncate(s21_decimal value, s21_decimal *result);
int s21_negate(s21_decimal value, s21_decimal *result);

int s21_get_exp(s21_decimal value);
void s21_set_exp(s21_decimal *value, int exp);
int s21_get_bit(s21_decimal value, int num);
int s21_get_sign(s21_decimal value);
void s21_set_sign(s21_decimal *value, int sign);
void s21_shift_less(s21_decimal *value, unsigned int shift);
void s21_normalize(s21_decimal *value1, s21_decimal *value2);
int s21_zerro_check(s21_decimal value);
void s21_decimal_copy(s21_decimal src, s21_decimal *dst);

//----------------------------------------big_decimal----------------------------------------

void s21_from_decimal_to_big(s21_decimal src, s21_big_decimal *dst);
int s21_from_big_to_decimal(s21_big_decimal src, s21_decimal *dst);
int s21_big_normalize(s21_big_decimal *value1, s21_big_decimal *value2);
void s21_big_10_mult(s21_big_decimal *value);
int s21_big_10_div(s21_big_decimal *value);
int s21_big_shift_more(s21_big_decimal *value, unsigned int shift);
int s21_big_get_bit(s21_big_decimal value, int num);
void s21_big_decimal_copy(s21_big_decimal src, s21_big_decimal *dst);
unsigned long long int s21_big_simple_add(s21_big_decimal value_1,
                                          s21_big_decimal value_2,
                                          s21_big_decimal *result);
long long int s21_big_simple_sub(s21_big_decimal value_1,
                                 s21_big_decimal value_2,
                                 s21_big_decimal *result);
unsigned int s21_big_smart_shift_less(s21_big_decimal *value,
                                      unsigned int shift);
int s21_big_simple_round(s21_big_decimal *value, unsigned int round);
int s21_big_string_round(char *string, int len, s21_big_decimal roundable);
int s21_big_smart_add(s21_decimal value_1, s21_decimal value_2,
                      s21_decimal *result);
int s21_big_is_less(s21_big_decimal vValueOneBig, s21_big_decimal vValueTwoBig);
int s21_big_get_high_bit(s21_big_decimal vValue);
int s21_big_zerro_check(s21_big_decimal value);
void s21_big_string_shift_less(s21_big_decimal *value, unsigned int shift,
                               char *remainder);

#endif  //  TESTS_TEST_DECIMAL_H
