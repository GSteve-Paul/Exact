/*******************************************************************************************[Int.h]
Copyright (c) 2005-2010, Niklas Een, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef Int_h
#define Int_h

#include <cstdint>

#ifdef _MSC_VER
typedef INT64 int64;
typedef UINT64 uint64;
typedef INT_PTR intp;
typedef UINT_PTR uintp;
#define I64_fmt "I64d"
#else
typedef long long int64;
typedef unsigned long long uint64;
typedef __PTRDIFF_TYPE__ intp;
typedef unsigned __PTRDIFF_TYPE__ uintp;
#define I64_fmt "lld"
#endif

typedef signed char schar;
typedef unsigned char uchar;
typedef unsigned int uint;
typedef unsigned long ulong;
typedef const char cchar;
typedef short int16;
typedef unsigned short uint16;
typedef int int32;
typedef unsigned uint32;

template <class T>
static inline T *xmalloc(size_t size)
{
  T *tmp = (T *)malloc(size * sizeof(T));
  assert(size == 0 || tmp != NULL);
  if (size != 0 && tmp == NULL)
  { // M. Piotrow 11.10.2017
    exit(0);
    // std::bad_alloc exc; throw exc;
  }
  return tmp;
}

template <class T>
static inline T *xrealloc(T *ptr, size_t size)
{
  T *tmp = (T *)realloc((void *)ptr, size * sizeof(T));
  assert(size == 0 || tmp != NULL);
  if (size != 0 && tmp == NULL)
  { // M. Piotrow 11.10.2017
    exit(0);
    // std::bad_alloc exc; throw exc;
  }
  return tmp;
}

template <class T>
static inline void xfree(T *ptr)
{
  if (ptr != NULL)
    free((void *)ptr);
}

static inline char *Xstrdup(cchar *src);
static inline char *Xstrdup(cchar *src)
{
  int size = strlen(src) + 1;
  char *tmp = xmalloc<char>(size);
  memcpy(tmp, src, size);
  return tmp;
}
#define xstrdup(s) Xstrdup(s)

#ifdef __LP64__
#define LP64 // LP : int=32 long,ptr=64 (unix model -- the windows model is LLP : int,long=32 ptr=64)
#endif

//=================================================================================================

struct Exception_IntOverflow
{
  char *where;
  Exception_IntOverflow(char *w) : where(w) {} // (takes ownership of string)
};
// #define NO_GMP

#ifdef NO_GMP
//=================================================================================================
// Fake bignums using 'int64':
//=================================================================================================

#define Int_Max__ 9223372036854775807LL
#define Int_Min__ (-Int_Max__)
#define Int_Undef__ (-Int_Max__ - 1LL)

//-------------------------------------------------------------------------------------------------

#define A1 assert(data != Int_Undef__);
#define A2 assert(data != Int_Undef__), assert(other.data != Int_Undef__);

// NOTE! This is not a proper abstraction of big numbers. It just includes the
// operators used in 'PbSolver'. It should be easy enough to add the missing
// operators on demand.
//
class Int
{
  int64 data;
  bool small() const { return (Int_Min__ < data && data < Int_Max__); }

public:
  Int() : data(Int_Undef__) {}
  Int(int x) : data(x) {}
  Int(long x) : data(x) {}
  Int(int64 x) : data(x) {}
  Int(uint64_t x) : data(x) {}

  // "operator =" and copy-constructor "Int(const Int& src)" are default defined
  // to the right thing.

  uint hash() const { A1 return (uint)data ^ (uint)(data >> 32); }

  bool operator==(Int other) const { A2 return data == other.data; }
  bool operator!=(Int other) const { A2 return data != other.data; }
  bool operator<(Int other) const { A2 return data < other.data; }
  bool operator>(Int other) const { A2 return data > other.data; }
  bool operator<=(Int other) const { A2 return data <= other.data; }
  bool operator>=(Int other) const { A2 return data >= other.data; }

  Int operator&(Int other) const { A2 return Int(data & other.data); }
  Int &operator>>=(int n)
  {
    A1 data >>= n;
    return *this;
  }

  Int operator-() const { A1 return Int(-data); }
  Int &operator++()
  {
    A1++ data;
    return *this;
  }
  Int &operator--()
  {
    A1-- data;
    return *this;
  }
  Int &operator-=(Int other)
  {
    A2 data -= other.data;
    return *this;
  }
  Int &operator+=(Int other)
  {
    A2 data += other.data;
    return *this;
  }
  Int &operator*=(Int other)
  {
    A2 data *= other.data;
    return *this;
  }
  Int &operator/=(Int other)
  {
    A2 data /= other.data;
    return *this;
  }
  Int operator+(Int other) const { A2 return Int(data + other.data); }
  Int operator-(Int other) const { A2 return Int(data - other.data); }
  Int operator*(Int other) const { A2 return Int(data * other.data); }
  Int operator/(Int other) const { A2 return Int(data / other.data); }
  Int operator%(Int other) const { A2 return Int(data % other.data); }

  // addition that allowed infinity (not allowed as 2nd parameter)
  Int add(Int other) const
  {
    if (!small())
      return *this;
    else
      return Int(data + other.data);
  }

  friend char *toString(Int num)
  {
    char buf[32];
    sprintf(buf, "%lld", num.data);
    return xstrdup(buf);
  } // Caller must free string.
  friend int toint(Int num)
  {
    if (num > INT_MAX || num < INT_MIN)
      throw Exception_IntOverflow(xstrdup("toint"));
    return (int)num.data;
  }
  friend int64_t tolong(Int num)
  {
    if (num > INT64_MAX || num < INT64_MIN)
      throw Exception_IntOverflow(xstrdup("tolong"));
    return (long int)num.data;
  }
  friend uint64_t toulong(Int num)
  {
    if (num > UINT64_MAX || num < 0)
      throw Exception_IntOverflow(xstrdup("toulong"));
    return (unsigned long int)num.data;
  }
};

#define Int_MAX Int(Int_Max__)
#define Int_MIN Int(Int_Min__)

#undef A1
#undef A2

#else
//=================================================================================================
// Real bignums using "GNU Multiple Precision Arithmetic Library"
//=================================================================================================

#include "gmp.h"

//=================================================================================================

#define A1 assert(!small());
#define A2          \
  assert(!small()); \
  assert(!other.small());

//- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
//- - - - - - - - - -

#define Int_MIN Int((mpz_t *)-1)
#define Int_MAX Int((mpz_t *)1)

class Int
{
  mpz_t *data; // This pointer is meant to contain small integers when bit 0 is
               // set (for efficiency). Currently the only small integers used
               // are the special values 'Int_MIN' and 'Int_MAX'.
  bool small() const { return ((intp)data & 1) != 0; }

public:
  // Constructors/Destructor (+assignment operator)
  //
  explicit Int(mpz_t *d) : data(d) {} // Low-level constructor -- don't use!

  Int()
  {
    data = xmalloc<mpz_t>(1);
    assert(((intp)data & 1) == 0);
    mpz_init(*data);
  }

  explicit Int(int x)
  {
    data = xmalloc<mpz_t>(1);
    assert(((intp)data & 1) == 0);
    mpz_init_set_si(*data, x);
  }

  Int(int64_t x)
  {
    data = xmalloc<mpz_t>(1);
    assert(((intp)data & 1) == 0);
#if defined(_MSC_VER) || defined(__MINGW32__) || defined(__MINGW64__)
    bool neg = false, int64_min = false;
    if (x < 0)
    {
      if (x == INT64_MIN)
        int64_min = true, x++;
      x = -x, neg = true;
    }
    mpz_init(*data);
    mpz_import(*data, 1, 1, sizeof(x), 0, 0, &x);
    if (neg)
      mpz_neg(*data, *data);
    if (int64_min)
      mpz_sub_ui(*data, *data, 1);
#else
    mpz_init_set_si(*data, x);
#endif
  }

  explicit Int(uint64_t x)
  {
    data = xmalloc<mpz_t>(1);
    assert(((intp)data & 1) == 0);
#if defined(_MSC_VER) || defined(__MINGW32__) || defined(__MINGW64__)
    mpz_init(*data);
    mpz_import(*data, 1, 1, sizeof(x), 0, 0, &x);
#else
    mpz_init_set_ui(*data, x);
#endif
  }

  Int(const Int &src)
  {
    if (src.small())
      data = src.data;
    else
    {
      data = xmalloc<mpz_t>(1);
      assert(((intp)data & 1) == 0);
      mpz_init_set(*data, *src.data);
    }
  }

  Int(Int &&src)
  {
    data = src.data;
    src.data = (mpz_t *)1;
  }

  ~Int()
  {
    if (!small())
    {
      mpz_clear(*data);
      xfree(data);
    }
    data = 0;
  }

  Int &operator=(const Int &other)
  {
    if (&other != this)
    {
      if (other.small())
      {
        this->~Int();
        data = other.data;
      }
      else
      {
        if (small())
        {
          data = xmalloc<mpz_t>(1);
          assert(((intp)data & 1) == 0);
          mpz_init_set(*data, *other.data);
        }
        else
          mpz_set(*data, *other.data);
      }
    }
    return *this;
  }

  Int &operator=(Int &&other)
  {
    if (&other != this)
    {
      this->~Int();
      data = other.data;
      other.data = (mpz_t *)1;
    }
    return *this;
  }

  // Operators:
  //

  // -- Comparison (supports infinity)
  //    '+oo' and '-oo' are treated as two unique points beyond the integers.
  //    For instanse '+oo' is not < than itself, but <= than itself.
  bool operator==(const Int &other) const
  {
    if (small())
      return other.small() ? (data == other.data) : false;
    else
      return other.small() ? false : mpz_cmp(*data, *other.data) == 0;
  }

  bool operator<(const Int &other) const
  {
    if (small())
    {
      if (data == Int_MIN.data)
        return (!other.small() || other.data != Int_MIN.data);
      else
      {
        assert(data == Int_MAX.data);
        return false;
      }
    }
    else
    {
      if (other.small())
      {
        if (other.data == Int_MIN.data)
          return false;
        else
        {
          assert(other.data == Int_MAX.data);
          return true;
        }
      }
      else
        return mpz_cmp(*data, *other.data) < 0;
    }
  }

  bool operator!=(const Int &other) const { return !(*this == other); }
  bool operator>=(const Int &other) const { return !(*this < other); }
  bool operator>(const Int &other) const { return other < *this; }
  bool operator<=(const Int &other) const { return !(*this > other); }

  // -- Arithmetic (not allowed on infinity except for unary '-')
  Int operator+(const Int &other) const
  {
    A2 Int ret;
    mpz_add(*ret.data, *data, *other.data);
    return ret;
  }
  Int operator-(const Int &other) const
  {
    A2 Int ret;
    mpz_sub(*ret.data, *data, *other.data);
    return ret;
  }
  Int operator*(const Int &other) const
  {
    A2 Int ret;
    mpz_mul(*ret.data, *data, *other.data);
    return ret;
  }
  Int operator/(const Int &other) const
  {
    A2 Int ret;
    mpz_tdiv_q(*ret.data, *data, *other.data);
    return ret;
  }
  Int operator%(const Int &other) const
  {
    A2 Int ret;
    mpz_tdiv_r(*ret.data, *data, *other.data);
    return ret;
  }

  Int &operator+=(const Int &other)
  {
    A2 mpz_add(*data, *data, *other.data);
    return *this;
  }
  Int &operator-=(const Int &other)
  {
    A2 mpz_sub(*data, *data, *other.data);
    return *this;
  }
  Int &operator*=(const Int &other)
  {
    A2 mpz_mul(*data, *data, *other.data);
    return *this;
  }
  Int &operator/=(const Int &other)
  {
    A2 mpz_tdiv_q(*data, *data, *other.data);
    return *this;
  }
  Int &operator%=(const Int &other)
  {
    A2 mpz_tdiv_r(*data, *data, *other.data);
    return *this;
  }
  Int &operator++() { return *this += Int(1); }
  Int &operator--() { return *this -= Int(1); }

  Int operator-() const
  {
    if (small())
      return Int((mpz_t *)(-(intp)data));
    else
    {
      Int ret;
      mpz_neg(*ret.data, *data);
      return ret;
    }
  }

  Int abs() const
  {
    Int result(*this);                  // Copy the current object
    mpz_abs(*result.data, *this->data); // Calculate abs without modifying the original
    return result;
  }

  void applyRandom(gmp_randstate_t randState, const Int &x)
  {
    mpz_urandomm(*data, randState, *x.data);
  }

  // -- Bit operators (incomplete; we don't need more at the moment)
  Int operator&(const Int &other) const
  {
    A2 Int ret;
    mpz_and(*ret.data, *data, *other.data);
    return ret;
  }
  Int &operator>>=(int n)
  {
    A1 mpz_fdiv_q_2exp(*data, *data, n);
    return *this;
  }

  // addition that allowed infinity (not allowed as 2nd parameter)
  Int add(const Int &other) const
  {
    if (small())
      return *this;
    else
    {
      Int ret;
      mpz_add(*ret.data, *data, *other.data);
      return ret;
    }
  }

  // Methods:
  //
  friend char *toString(Int num)
  {
    if (num == Int_MIN)
      return xstrdup("-oo");
    else if (num == Int_MAX)
      return xstrdup("+oo");
    assert(!num.small());
    char *tmp = xmalloc<char>(mpz_sizeinbase(*num.data, 10) + 2);
    mpz_get_str(tmp, 10, *num.data);
    return tmp;
  }

  friend int toint(Int num)
  {
    if (num.small() || !mpz_fits_sint_p(*num.data))
      throw Exception_IntOverflow(xstrdup("toint"));
    return (int)mpz_get_si(*num.data);
  }

  friend int64_t tolong(Int num)
  {
    if (num.small())
      throw Exception_IntOverflow(xstrdup("tolong"));
    int64_t res;
#if defined(_MSC_VER) || defined(__MINGW32__) || defined(__MINGW64__)
    size_t cnt = 0;
    bool neg = mpz_sgn(*num.data) < 0;
    uint64_t ures[20];
    mpz_export(ures, &cnt, 1, sizeof(uint64_t), 0, 0, *num.data);
    if (cnt > 1 || neg && ures[0] > 1ULL - (INT64_MIN + 1) ||
        !neg && ures[0] > (uint64_t)INT64_MAX)
      throw Exception_IntOverflow(xstrdup("toulong"));
    res = (cnt == 0 ? 0 : (neg ? -(int64_t)ures[0] : (int64_t)ures[0]));
#else
    if (!mpz_fits_slong_p(*num.data))
      throw Exception_IntOverflow(xstrdup("tolong"));
    res = mpz_get_si(*num.data);
#endif
    return res;
  }

  friend uint64_t toulong(Int num)
  {
    if (num.small())
      throw Exception_IntOverflow(xstrdup("toulong"));
    uint64_t res;
#if defined(_MSC_VER) || defined(__MINGW32__) || defined(__MINGW64__)
    size_t cnt = 0;
    uint64_t ures[20];
    mpz_export(ures, &cnt, 1, sizeof(uint64_t), 0, 0, *num.data);
    if (mpz_sgn(*num.data) < 0 || cnt > 1)
      throw Exception_IntOverflow(xstrdup("toulong"));
    res = (cnt == 0 ? 0 : ures[0]);
#else
    if (!mpz_fits_ulong_p(*num.data))
      throw Exception_IntOverflow(xstrdup("toulong"));
    res = mpz_get_ui(*num.data);
#endif
    return res;
  }

  explicit operator double()
  {
    if (this->small())
      throw Exception_IntOverflow(xstrdup("double"));
    return mpz_get_d(*this->data);
  }

  uint hash() const
  { // primitive hash function -- not good with bit-shifts
    mp_size_t size = mpz_size(*data);
    mp_limb_t val = 0;
    for (mp_size_t i = 0; i < size; i++)
    {
      mp_limb_t limb = mpz_getlimbn(*data, i);
      val ^= limb;
    }
#ifdef LP64
    return (uint)val | (uint)(val >> 32);
#else
    return (uint)val;
#endif
  }
};

Int absInt(const Int &number)
{
  return number.abs(); // Utilize the member function to calculate the absolute value
}

Int randInt(const Int &x)
{
  static gmp_randstate_t randState;
  static bool initialized = false;
  if (!initialized)
  {
    gmp_randinit_default(randState);
    mpz_t seed;
    mpz_init(seed);
    mpz_set_ui(seed, time(NULL));
    gmp_randseed(randState, seed);
    mpz_clear(seed);
    initialized = true;
  }

  Int result;
  result.applyRandom(randState, x); // Use member function to apply the random operation
  return result;
}

//=================================================================================================
#endif

#endif