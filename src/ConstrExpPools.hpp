/**********************************************************************
This file is part of the Exact program

Copyright (c) 2021 Jo Devriendt, KU Leuven

Exact is distributed under the terms of the MIT License.
You should have received a copy of the MIT License along with Exact.
See the file LICENSE or run with the flag --license=MIT.
**********************************************************************/

/**********************************************************************
Copyright (c) 2014-2020, Jan Elffers
Copyright (c) 2019-2021, Jo Devriendt
Copyright (c) 2020-2021, Stephan Gocht
Copyright (c) 2014-2021, Jakob Nordström

Parts of the code were copied or adapted from MiniSat.

MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
           Copyright (c) 2007-2010  Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**********************************************************************/

#pragma once

#include <memory>
#include "typedefs.hpp"

namespace rs {

// shared_ptr-like wrapper around ConstrExp, ensuring it gets released back to the pool when no longer needed.
template <typename CE>
struct CePtr {
  CE* ce;

  // default constructor
  CePtr() : ce(nullptr) {}
  // regular constructor
  explicit CePtr(CE* c) : ce(c) {
    if (ce) ce->increaseUsage();
  }
  // copy constructor
  CePtr(const CePtr<CE>& other) : ce{other.ce} {
    if (ce) ce->increaseUsage();
  }
  // copy constructor allowing for polymorphism
  template <typename T, typename = std::enable_if_t<std::is_convertible_v<T&, CE&>>>
  CePtr(const CePtr<T>& other) : ce{other.ce} {
    if (ce) ce->increaseUsage();
  }
  // move constructor
  CePtr(CePtr<CE>&& other) noexcept : ce{other.ce} { other.ce = nullptr; }
  // move constructor allowing for polymorphism
  template <typename T, typename = std::enable_if_t<std::is_convertible_v<T&, CE&>>>
  CePtr(CePtr<T>&& other) : ce{other.ce} {
    other.ce = nullptr;
  }
  // destructor
  ~CePtr() {
    if (ce) ce->decreaseUsage();
  }
  // assignment operator
  CePtr<CE>& operator=(const CePtr<CE>& other) {
    if (this == &other) return *this;
    if (ce) ce->decreaseUsage();
    ce = other.ce;
    if (ce) ce->increaseUsage();
    return *this;
  }
  // move assignment operator
  CePtr<CE>& operator=(CePtr<CE>&& other) noexcept {
    if (this == &other) return *this;
    if (ce) ce->decreaseUsage();
    ce = other.ce;
    other.ce = nullptr;
    return *this;
  }

  CE& operator*() const { return *ce; }
  CE* operator->() const { return ce; }
  explicit operator bool() const { return ce; }
  void makeNull() {
    if (ce) ce->decreaseUsage();
    ce = nullptr;
  }
};

template <typename SMALL, typename LARGE>
struct ConstrExp;
class ActualLogger;

template <typename SMALL, typename LARGE>
class ConstrExpPool {  // TODO: private constructor for ConstrExp, only accessible to ConstrExpPool?
  size_t n = 0;
  std::vector<ConstrExp<SMALL, LARGE>*> ces;
  std::vector<ConstrExp<SMALL, LARGE>*> availables;
  std::shared_ptr<ActualLogger> plogger;

 public:
  ~ConstrExpPool();

  void resize(size_t newn);
  void initializeLogging(std::shared_ptr<ActualLogger>& lgr);
  CePtr<ConstrExp<SMALL, LARGE>> take();
  void release(ConstrExp<SMALL, LARGE>* ce);
};

class ConstrExpPools {
  ConstrExpPool<int, long long> ce32s;
  ConstrExpPool<long long, int128> ce64s;
  ConstrExpPool<int128, int128> ce96s;
  ConstrExpPool<int128, int256> ce128s;
  ConstrExpPool<bigint, bigint> ceArbs;

 public:
  void resize(size_t newn);
  void initializeLogging(std::shared_ptr<ActualLogger> lgr);

  template <typename SMALL, typename LARGE>
  CePtr<ConstrExp<SMALL, LARGE>> take();  // NOTE: only call specializations

  Ce32 take32();
  Ce64 take64();
  Ce96 take96();
  Ce128 take128();
  CeArb takeArb();
};

}  // namespace rs
