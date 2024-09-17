#include "s21_decimal.h"

int s21_get_sign(s21_decimal value) {
  unsigned int vBuffer = value.bits[3];
  vBuffer >>= SIGN_SHIFT;
  vBuffer &= GET_MASK;
  return (vBuffer);
}

void s21_set_sign(s21_decimal *value, int sign) {
  int vSign = SIGN_MASK;
  if (sign) {
    value->bits[3] |= vSign;
  } else {
    value->bits[3] &= (~vSign);
  }
}

int s21_get_exp(s21_decimal value) {
  int vExp = 0;
  int vBuffer = value.bits[3];
  vExp = vBuffer >> EXP_SHIFT;
  vExp &= GET_EXP_MASK;
  return (vExp);
}

void s21_set_exp(s21_decimal *value, int exp) {
  unsigned int vExp = exp << EXP_SHIFT;
  value->bits[3] &= SIGN_MASK;
  value->bits[3] |= vExp;
}

int s21_get_bit(s21_decimal value, int num) {
  unsigned int vBuffer = value.bits[(int)((num) / 32)];
  vBuffer >>= num % 32;
  vBuffer &= GET_MASK;
  return vBuffer;
}

void s21_shift_less(s21_decimal *value, unsigned int shift) {
  int vShiftBuffer1 = 0;
  int vShiftBuffer2 = 0;
  for (; shift > 0; shift--) {
    vShiftBuffer2 = s21_get_bit(*value, 64);
    vShiftBuffer1 = s21_get_bit(*value, 32);
    value->bits[0] >>= 1;
    value->bits[1] >>= 1;
    value->bits[2] >>= 1;
    vShiftBuffer2 <<= 31;
    vShiftBuffer1 <<= 31;
    value->bits[1] |= vShiftBuffer2;
    value->bits[0] |= vShiftBuffer1;
  }
}

int s21_zerro_check(s21_decimal value) {
  int vAns = 1;
  for (int i = 0; i < 3; i++) {
    if (value.bits[i] != 0) vAns = 0;
  }
  return vAns;
}

void s21_decimal_copy(s21_decimal src, s21_decimal *dst) {
  for (int i = 0; i < 4; i++) dst->bits[i] = src.bits[i];
}

void s21_init_decimal(s21_decimal *value) {
  for (int i = 0; i < 4; i++) {
    value->bits[i] = 0x00000000;
  }
}

//----------------------------------------big_decimal----------------------------------------

void s21_from_decimal_to_big(s21_decimal src, s21_big_decimal *dst) {
  dst->sign = s21_get_sign(src);
  dst->exp = s21_get_exp(src);
  for (int i = 0; i < 3; i++) {
    dst->bits[i] = src.bits[i];
  }
  for (int i = 3; i < 6; i++) {
    dst->bits[i] = 0;
  }
}

//  если нормализуем первую вернёт 0
int s21_big_normalize(s21_big_decimal *value1, s21_big_decimal *value2) {
  int vRet = 0;
  if (value1->exp > value2->exp) {
    for (; value1->exp != value2->exp;) {
      s21_big_10_mult(value2);
    }
    vRet = 1;
  } else {
    for (; value2->exp != value1->exp;) {
      s21_big_10_mult(value1);
    }
  }
  return vRet;
}

void s21_big_10_mult(s21_big_decimal *value) {
  s21_big_decimal vShift1 = {0, 0, {0}};
  s21_big_decimal vShift3 = {0, 0, {0}};
  s21_big_decimal_copy(*value, &vShift1);
  s21_big_decimal_copy(*value, &vShift3);
  s21_big_shift_more(&vShift1, 1);
  s21_big_shift_more(&vShift3, 3);
  s21_big_simple_add(vShift1, vShift3, value);
  value->exp++;
}

int s21_big_shift_more(s21_big_decimal *value, unsigned int shift) {
  int vError = 0;
  int vShiftBuffer[7] = {0};
  for (; shift > 0; shift--) {
    for (int i = 0; (i < 6) && (!vError); i++) {
      vShiftBuffer[i + 1] = s21_big_get_bit(*value, (31 + (i * 32)));
      value->bits[i] <<= 1;
      value->bits[i] |= vShiftBuffer[i];
    }
    if (vShiftBuffer[6]) vError = 1;
  }
  return vError;
}

void s21_big_decimal_copy(s21_big_decimal src, s21_big_decimal *dst) {
  dst->exp = src.exp;
  dst->sign = src.sign;
  for (int i = 0; i < 6; i++) dst->bits[i] = src.bits[i];
}

unsigned long long int s21_big_simple_add(s21_big_decimal value_1,
                                          s21_big_decimal value_2,
                                          s21_big_decimal *result) {
  unsigned long long int vBuffer = 0;
  for (int i = 0; i < 6; i++) {
    vBuffer = (unsigned long long)value_1.bits[i] +
              (unsigned long long)value_2.bits[i] + vBuffer;
    result->bits[i] = vBuffer & 0xffffffff;
    vBuffer >>= 32;
  }
  result->exp = value_1.exp;
  return vBuffer;
}

long long int s21_big_simple_sub(s21_big_decimal value_1,
                                 s21_big_decimal value_2,
                                 s21_big_decimal *result) {
  long long int vBuffer = 0;
  for (int i = 0; i < 6; i++) {
    vBuffer = (long long)value_1.bits[i] - (long long)value_2.bits[i] - vBuffer;
    if (vBuffer < 0) {
      result->bits[i] = 0xffffffff + vBuffer + 1;
      vBuffer = 1;
    } else {
      result->bits[i] = vBuffer;
      vBuffer = 0;
    }
  }
  result->exp = value_1.exp;
  result->sign = value_1.sign;
  return vBuffer;
}

int s21_big_10_div(s21_big_decimal *value) {
  unsigned long long vBufferInt = 0;
  unsigned long long vBufferRem = 0;
  for (int i = 5; i >= 0; i--) {
    vBufferInt += value->bits[i];
    vBufferRem = vBufferInt % 10;
    value->bits[i] = (int)(vBufferInt / 10);
    vBufferInt = vBufferRem << 32;
  }
  value->exp--;
  return vBufferRem;
}

unsigned int s21_big_smart_shift_less(s21_big_decimal *value,
                                      unsigned int shift) {
  unsigned int vAdd = 0;
  char vRemainder[50] = {'\0'};
  s21_big_string_shift_less(value, shift, vRemainder);
  if (vRemainder[0] > '5') {
    vAdd = 1;
  } else if (vRemainder[0] == '5') {
    for (unsigned int i = 1; i < shift; i++) {
      if (vRemainder[i] != '0') vAdd = 1;
    }
    if (vAdd == 0) {
      int vBuffer = s21_big_10_div(value);
      vAdd = vBuffer % 2;
      s21_big_10_mult(value);
      value->bits[0] += vBuffer;
    }
  }
  return vAdd;
}

void s21_big_string_shift_less(s21_big_decimal *value, unsigned int shift,
                               char *remainder) {
  for (; shift > 0; shift--) {
    remainder[shift - 1] = ('0' + s21_big_10_div(value));
  }
}

int s21_big_simple_round(s21_big_decimal *value, unsigned int round) {
  int vError = 0;
  s21_big_decimal vRoundAdd = {value->sign, value->exp, {0}};
  vRoundAdd.bits[0] = s21_big_smart_shift_less(value, round);
  vError = (int)s21_big_simple_add(*value, vRoundAdd, value);
  return vError;
}

int s21_from_big_to_decimal(s21_big_decimal src, s21_decimal *dst) {
  int vError = 0;
  char vRemainder[50] = {'\0'};
  int vShift = 0;
  s21_big_decimal vBuffer = {0, 0, {0}};
  s21_big_decimal vRoundAdd = {0, 0, {0}};
  s21_big_decimal_copy(src, &vBuffer);
  for (; (vBuffer.bits[5] != 0) || (vBuffer.bits[4] != 0) ||
         (vBuffer.bits[3] != 0) || (vBuffer.exp > s21_MAXEXP);
       vShift++) {
    vRemainder[vShift] = ('0' + s21_big_10_div(&vBuffer));
  }
  vRoundAdd.bits[0] = s21_big_string_round(vRemainder, vShift, vBuffer);
  if ((vRoundAdd.bits[0]) && (vBuffer.bits[0] == MAX_INT) &&
      (vBuffer.bits[1] == MAX_INT) && (vBuffer.bits[2] == MAX_INT)) {
    if (vBuffer.exp > 0) {
      vShift++;
      vRemainder[vShift] = ('0' + s21_big_10_div(&vBuffer));
      vRoundAdd.bits[0] = s21_big_string_round(vRemainder, vShift, vBuffer);
    } else {
      vError = 1;
      if (vBuffer.sign) vError = 2;
    }
  }
  s21_big_simple_add(vBuffer, vRoundAdd, &vBuffer);
  if (vBuffer.exp < 0) {
    vError = 1;
    if (vBuffer.sign) vError = 2;
  } else if (vError == 0) {
    s21_set_exp(dst, vBuffer.exp);
    s21_set_sign(dst, vBuffer.sign);
    for (int i = 0; i < 3; i++) dst->bits[i] = vBuffer.bits[i];
  }
  return vError;
}

int s21_big_string_round(char *string, int len, s21_big_decimal roundable) {
  int vAdd = 0;
  if (len) len--;
  if (string[len] > '5') {
    vAdd = 1;
  } else if (string[len] == '5') {
    for (; (len) > 0; len--) {
      if (string[len - 1] != '0') vAdd = 1;
    }
    if (vAdd == 0) {
      int vNext = s21_big_10_div(&roundable);
      vAdd = vNext % 2;
    }
  }
  return vAdd;
}

int s21_big_smart_add(s21_decimal value_1, s21_decimal value_2,
                      s21_decimal *result) {
  int vError = 0;
  s21_big_decimal vBig1 = {0, 0, {0}};
  s21_big_decimal vBig2 = {0, 0, {0}};
  s21_big_decimal vBigRes = {0, 0, {0}};
  if (s21_zerro_check(value_1)) {
    s21_decimal_copy(value_2, result);
  } else if (s21_zerro_check(value_2)) {
    s21_decimal_copy(value_1, result);
  } else if (s21_get_sign(value_1) ^ s21_get_sign(value_2)) {
    s21_from_decimal_to_big(value_1, &vBig1);
    s21_from_decimal_to_big(value_2, &vBig2);
    if (s21_big_is_less(vBig1, vBig2) == -1) {
      s21_init_decimal(result);
    } else {
      s21_big_normalize(&vBig1, &vBig2);
      if (s21_big_is_less(vBig1, vBig2) == 1) {
        s21_big_simple_sub(vBig2, vBig1, &vBigRes);
      } else {
        s21_big_simple_sub(vBig1, vBig2, &vBigRes);
      }
      vError = s21_from_big_to_decimal(vBigRes, result);
    }
  } else {
    s21_from_decimal_to_big(value_1, &vBig1);
    s21_from_decimal_to_big(value_2, &vBig2);
    s21_big_normalize(&vBig1, &vBig2);
    s21_big_simple_add(vBig1, vBig2, &vBigRes);
    vBigRes.sign = vBig1.sign;
    vError = s21_from_big_to_decimal(vBigRes, result);
  }
  return vError;
}

int s21_big_is_less(s21_big_decimal vValueOneBig,
                    s21_big_decimal vValueTwoBig) {
  int vResult = -1;
  int vCntResult = 191;
  for (; vCntResult >= 0 && vResult == -1; vCntResult--) {
    if (s21_big_get_bit(vValueOneBig, vCntResult) <
        s21_big_get_bit(vValueTwoBig, vCntResult)) {
      vResult = 1;
    } else if (s21_big_get_bit(vValueOneBig, vCntResult) >
               s21_big_get_bit(vValueTwoBig, vCntResult)) {
      vResult = 0;
    }
  }
  return vResult;
}

int s21_big_get_bit(s21_big_decimal value, int num) {
  unsigned int vBuffer = value.bits[(int)((num) / 32)];
  vBuffer >>= num % 32;
  vBuffer &= GET_MASK;
  return vBuffer;
}

int s21_big_get_high_bit(s21_big_decimal vValue) {
  int vCnt = 191;
  for (; !s21_big_get_bit(vValue, vCnt) && vCnt > 0; vCnt--)
    ;
  return vCnt;
}

int s21_big_zerro_check(s21_big_decimal value) {
  int vAns = 1;
  for (int i = 0; i < 6; i++) {
    if (value.bits[i] != 0) vAns = 0;
  }
  return vAns;
}

//----------------------------------------answer----------------------------------------

int s21_add(s21_decimal value_1, s21_decimal value_2, s21_decimal *result) {
  int vError = 0;
  vError = s21_big_smart_add(value_1, value_2, result);
  return vError;
}

int s21_sub(s21_decimal value_1, s21_decimal value_2, s21_decimal *result) {
  int vError = 0;
  s21_decimal vValue_2 = {0};
  s21_decimal_copy(value_2, &vValue_2);
  s21_negate(vValue_2, &vValue_2);
  vError = s21_big_smart_add(value_1, vValue_2, result);
  return vError;
}

int s21_mul(s21_decimal value_1, s21_decimal value_2, s21_decimal *result) {
  int vError = 0;
  s21_big_decimal vBigRes = {(s21_get_sign(value_1) ^ s21_get_sign(value_2)),
                             (s21_get_exp(value_1) + s21_get_exp(value_2)),
                             {0}};
  s21_big_decimal vValueBig_1 = {
      s21_get_sign(value_1),
      s21_get_exp(value_1),
      {value_1.bits[0], value_1.bits[1], value_1.bits[2], 0, 0, 0}};
  if (s21_zerro_check(value_1) || s21_zerro_check(value_2)) {
    s21_init_decimal(result);
  } else {
    while (s21_zerro_check(value_2) != 1) {
      if (s21_get_bit(value_2, 0))
        s21_big_simple_add(vBigRes, vValueBig_1, &vBigRes);
      s21_shift_less(&value_2, 1);
      s21_big_shift_more(&vValueBig_1, 1);
    }
  }
  vError = s21_from_big_to_decimal(vBigRes, result);
  return vError;
}

/**
 * @brief Инвертирует знак числа типа Decimal.
 *
 * Возвращает результат умножения указанного Decimal на -1.
 *
 * @param value Десятичное число, знак которого требуется инвертировать.
 * @param result Указатель на переменную, в которую будет сохранен результат.
 * @return 0 в случае успешного выполнения, или 1 в случае ошибки.
 */
int s21_negate(s21_decimal value, s21_decimal *result) {
  int error = 0;
  if (result != NULL) {
    int sign = s21_get_sign(value);
    *result = value;
    s21_set_sign(result, !sign);
  } else
    error = 1;
  return error;
}

/**
 * @brief Отсекает десятичную часть числа.
 *
 *Возвращает целые цифры указанного Decimal числа; любые дробные цифры
 *отбрасываются, включая конечные нули.
 *
 * @param vValue Десятичное число, которое требуется отсечь.
 * @param vResult Указатель на переменную, в которую будет сохранен результат.
 * @return 0 в случае успешного выполнения, или 1 в случае ошибки.
 */
int s21_truncate(s21_decimal vValue, s21_decimal *vResult) {
  int vError = 0;
  int vExp = s21_get_exp(vValue);
  if (vResult != NULL && vExp <= 28) {
    s21_init_decimal(vResult);
    s21_big_decimal vTmp;
    s21_from_decimal_to_big(vValue, &vTmp);
    while (vTmp.exp != 0) {
      s21_big_10_div(&vTmp);
    }
    for (int j = 2; j >= 0; j--) {
      vResult->bits[j] = vTmp.bits[j];
    }
    if (s21_get_sign(vValue)) s21_set_sign(vResult, 1);
  } else {
    s21_init_decimal(vResult);
    vError = 1;
  }
  return vError;
}

/**
 * @brief Преобразует число типа decimal в число с плавающей точкой.
 *
 * Эта функция преобразует десятичное число src типа s21_decimal в число с
 * плавающей точкой одинарной точности dst типа float.
 *
 * @param src Число типа decimal, которое нужно преобразовать.
 * @param dst Указатель на переменную, в которую будет записан результат
 * преобразования.
 * @return 0 в случае успешного преобразования, в противном случае ненулевое
 * значение указывает на ошибку.
 */
int s21_from_decimal_to_float(s21_decimal src, float *dst) {
  int error = 0;
  *dst = 0.0;
  if (dst != NULL) {
    for (int i = 0; i < 96; i++) {
      if (s21_get_bit(src, i)) {
        *dst += pow(2, i);
      }
    }
    int scale = s21_get_exp(src);
    while (scale != 0) {
      *dst /= 10;
      scale--;
    }
    if (s21_get_sign(src)) *dst = -*dst;
  } else
    error = 1;
  return error;
}

/**
 * @brief Преобразует число с плавающей точкой в число типа decimal.
 *
 * Эта функция преобразует число с плавающей точкой одинарной точности src типа
 * float в десятичное число dst типа s21_decimal.
 *
 * @param src Число с плавающей точкой одинарной точности, которое нужно
 * преобразовать.
 * @param dst Указатель на переменную типа decimal, в которую будет записан
 * результат преобразования.
 * @return 0 в случае успешного преобразования, в противном случае ненулевое
 * значение указывает на ошибку.
 */
int s21_from_float_to_decimal(float src, s21_decimal *dst) {
  s21_init_decimal(dst);
  int return_value = 0;
  if (!dst || isinf(src) || isnan(src)) {
    return_value = 1;
  } else {
    if (src != 0) {
      int *p = (void *)&src;
      int bits = *p;
      int sign = bits >> 31;
      int exp = ((*(int *)&src & ~SIGN_MASK) >> 23) - 127;
      double temp = (double)fabs(src);
      int scale = 0;
      for (; !((int)temp); temp *= 10, scale++) {
      }
      for (; (int)temp < 1000000 && scale < 28; temp *= 10, scale++) {
      }
      temp = round(temp);
      if (scale <= 28 && (exp >= -94 && exp <= 95)) {
        floatbits mant = {0};
        temp = (float)temp;
        for (; fmod(temp, 10) == 0 && scale > 0; scale--, temp /= 10) {
        }
        mant.fl = temp;
        exp = ((*(int *)&mant.fl & ~SIGN_MASK) >> 23) - 127;
        dst->bits[exp / 32] |= 1 << exp % 32;
        int bitIndex = exp - 1;
        for (int j = 22; j >= 0; j--) {
          if ((mant.ui & (1 << j)) != 0) {
            int arrayIndex = bitIndex / 32;
            int bitOffset = bitIndex % 32;
            dst->bits[arrayIndex] |= 1 << bitOffset;
          }
          bitIndex--;
        }
        dst->bits[3] = (sign << 31) | (scale << 16);
      } else {
        return_value = 1;
      }
    }
  }
  return return_value;
}

/**
 * @brief Преобразует число типа decimal в целое число.
 *
 * Эта функция преобразует десятичное число vSrc типа s21_decimal в целое число
 * vDst типа int.
 *
 * @param vSrc Число типа decimal, которое нужно преобразовать.
 * @param vDst Указатель на переменную, в которую будет записан результат
 * преобразования.
 * @return 0 в случае успешного преобразования, в противном случае ненулевое
 * значение указывает на ошибку.
 */

int s21_from_decimal_to_int(s21_decimal vSrc, int *vDst) {
  s21_decimal vTmp;
  int vError = s21_truncate(vSrc, &vTmp);
  if (vDst && !(vTmp.bits[1] || vTmp.bits[2]) && !vError) {
    *vDst = vTmp.bits[0];
    if (s21_get_sign(vSrc)) *vDst *= -1;
  } else
    vError = 1;
  return vError;
}

/**
 * @brief Преобразует целое число в число типа decimal.
 *
 * Эта функция преобразует целое число vSrc типа int в десятичное число vDst
 * типа s21_decimal.
 *
 * @param vSrc Целое число, которое нужно преобразовать.
 * @param vDst Указатель на переменную типа decimal, в которую будет записан
 * результат преобразования.
 * @return 0 в случае успешного преобразования, в противном случае ненулевое
 * значение указывает на ошибку.
 */
int s21_from_int_to_decimal(int src, s21_decimal *dst) {
  int error = 0;
  if (abs(src) < s21_MAXDEC) {
    s21_init_decimal(dst);
    dst->bits[0] = abs(src);
    if (src < 0) s21_negate(*dst, dst);
  } else
    error = 1;
  return error;
}

int s21_is_less(s21_decimal vValueOne, s21_decimal vValueTwo) {
  int vResult = -1;
  s21_big_decimal vValueOneBig = {0};
  s21_big_decimal vValueTwoBig = {0};
  s21_from_decimal_to_big(vValueOne, &vValueOneBig);
  s21_from_decimal_to_big(vValueTwo, &vValueTwoBig);
  if (s21_is_equal(vValueOne, vValueTwo) == 0) {
    if (vValueOneBig.exp < 28 && vValueTwoBig.exp < 28 &&
        vValueOneBig.sign == vValueTwoBig.sign) {
      s21_big_normalize(&vValueOneBig, &vValueTwoBig);
      vResult = s21_big_is_less(vValueOneBig, vValueTwoBig);
    } else if (vValueOneBig.sign < vValueTwoBig.sign) {
      vResult = 0;
    } else if (vValueOneBig.sign > vValueTwoBig.sign) {
      vResult = 1;
    }
    if (vValueOneBig.sign == 1 && vValueTwoBig.sign == 1) vResult = 1 - vResult;
  } else {
    vResult = 0;
  }
  if (vResult == -1) vResult = 0;
  return vResult;
}

int s21_is_greater_or_equal(s21_decimal vValueOne, s21_decimal vValueTwo) {
  return 1 - s21_is_less(vValueOne, vValueTwo);
}

int s21_is_not_equal(s21_decimal vValueOne, s21_decimal vValueTwo) {
  return 1 - s21_is_equal(vValueOne, vValueTwo);
}

int s21_is_equal(s21_decimal vValueOne, s21_decimal vValueTwo) {
  int vResult = 1;
  int vCntResult = 191;
  s21_big_decimal vValueOneBig = {0};
  s21_big_decimal vValueTwoBig = {0};
  s21_from_decimal_to_big(vValueOne, &vValueOneBig);
  s21_from_decimal_to_big(vValueTwo, &vValueTwoBig);
  if (s21_zerro_check(vValueOne) != 1 && s21_zerro_check(vValueTwo) != 1) {
    if (vValueOneBig.exp < 28 && vValueTwoBig.exp < 28 &&
        vValueOneBig.sign == vValueTwoBig.sign) {
      s21_big_normalize(&vValueOneBig, &vValueTwoBig);
      for (; vCntResult >= 0 && vResult != 0; vCntResult--) {
        if (s21_big_get_bit(vValueOneBig, vCntResult) !=
            s21_big_get_bit(vValueTwoBig, vCntResult))
          vResult = 0;
      }
    } else {
      vResult = 0;
    }
  } else if (s21_zerro_check(vValueOne) != s21_zerro_check(vValueTwo)) {
    vResult = 0;
  }
  return vResult;
}

int s21_is_greater(s21_decimal vValueOne, s21_decimal vValueTwo) {
  int vResult = 1 - s21_is_less(vValueOne, vValueTwo);
  if (vResult == 1 && s21_is_equal(vValueOne, vValueTwo) == 1) vResult = 0;
  return vResult;
}

int s21_is_less_or_equal(s21_decimal vValueOne, s21_decimal vValueTwo) {
  int vResult = s21_is_less(vValueOne, vValueTwo);
  if (vResult == 0 && s21_is_equal(vValueOne, vValueTwo) == 1) vResult = 1;
  return vResult;
}

int s21_round(s21_decimal value, s21_decimal *result) {
  int vError = 0;
  s21_init_decimal(result);
  if (result == NULL || (s21_get_exp(value) > 28))
    vError = 1;
  else {
    s21_big_decimal vBuffer = {0};
    s21_from_decimal_to_big(value, &vBuffer);
    vError = s21_big_simple_round(&vBuffer, vBuffer.exp);
    s21_from_big_to_decimal(vBuffer, result);
  }
  return vError;
}

int s21_floor(s21_decimal value, s21_decimal *result) {
  int vError = 0;
  s21_init_decimal(result);
  if (result == NULL || (s21_get_exp(value) > 28))
    vError = 1;
  else {
    s21_big_decimal vBuffer = {0};
    s21_from_decimal_to_big(value, &vBuffer);
    char vRemainder[60] = {'\0'};
    s21_big_string_shift_less(&vBuffer, vBuffer.exp, vRemainder);
    int vFlag = 0;
    for (int i = 0; (i < s21_get_exp(value)) && !vFlag; i++) {
      if (vRemainder[i] != '0') vFlag = 1;
    }
    if ((vBuffer.sign == 0) || ((vBuffer.sign == 1) && vFlag == 0)) {
      s21_from_big_to_decimal(vBuffer, result);
      vError = s21_truncate(value, result);
    } else {
      s21_from_big_to_decimal(vBuffer, result);
      vError = s21_truncate(value, result);
      s21_decimal one = {{1, 0, 0, 0}};
      vError = s21_sub(*result, one, result);
      if (vError == 2) vError = 1;
    }
  }
  return vError;
}

int s21_div(s21_decimal value_1, s21_decimal value_2, s21_decimal *result) {
  int vError = 0;
  int vHighBitOne = 0;
  int vHighBitTwo = 0;
  s21_big_decimal vBigRes = {
      (s21_get_sign(value_1) ^ s21_get_sign(value_2)), 0, {0}};
  s21_big_decimal vBigAdd = {0, 0, {1, 0, 0, 0, 0, 0}};
  s21_big_decimal vBig1 = {0, 0, {0}};
  s21_big_decimal vBig2 = {0, 0, {0}};
  int vExpCnt = 0;
  int vHighCnt = 0;
  if (s21_zerro_check(value_2)) {
    vError = 3;
  } else if (s21_zerro_check(value_1)) {
    s21_init_decimal(result);
  } else {
    s21_from_decimal_to_big(value_1, &vBig1);
    s21_from_decimal_to_big(value_2, &vBig2);
    s21_big_normalize(&vBig1, &vBig2);
    vHighBitOne = s21_big_get_high_bit(vBig1);
    vHighBitTwo = s21_big_get_high_bit(vBig2);
    for (; vHighBitOne - 4 > vHighBitTwo; vHighCnt++) {
      s21_big_10_mult(&vBig2);
      vHighBitTwo = s21_big_get_high_bit(vBig2);
    }
    if (vHighCnt > 29 && vBigRes.sign == 0) {
      vError = 1;
    } else if (vHighCnt > 29 && vBigRes.sign == 1) {
      vError = 2;
    } else {
      while (vExpCnt < 31 && !s21_big_zerro_check(vBig1)) {
        while (s21_big_is_less(vBig2, vBig1)) {
          s21_big_simple_sub(vBig1, vBig2, &vBig1);
          s21_big_simple_add(vBigRes, vBigAdd, &vBigRes);
        }
        if (!s21_big_zerro_check(vBig1)) {
          s21_big_10_mult(&vBig1);
          s21_big_10_mult(&vBigRes);
          vExpCnt++;
        }
      }
      for (int i = 0; i < vHighCnt; i++) {
        s21_big_10_mult(&vBigRes);
      }
      vBigRes.exp = vExpCnt;
      vError = s21_from_big_to_decimal(vBigRes, result);
    }
  }
  return vError;
}
