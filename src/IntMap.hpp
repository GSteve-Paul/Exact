/**********************************************************************
This file is part of the Exact program

Copyright (c) 2021 Jo Devriendt, KU Leuven

Exact is distributed under the terms of the MIT License.
You should have received a copy of the MIT License along with Exact.
See the file LICENSE or run with the flag --license=MIT.
**********************************************************************/

#pragma once

#include "typedefs.hpp"

namespace rs {

template <typename T>
class IntMap {
  std::vector<T> _int2type;
  typename std::vector<T>::iterator int2type;

 public:
  T& operator[](int index) {
    assert(std::abs(index) <= (int)_int2type.size() / 2);
    return int2type[index];
  }

  const T& operator[](int index) const {
    assert(std::abs(index) <= (int)_int2type.size() / 2);
    return int2type[index];
  }

  void resize(int size, const T& init) {  // should always be called before use, as int2type is not set otherwise
    assert(size >= 0);
    int oldsize = (_int2type.size() - 1) / 2;  // NOTE: oldsize can be -1, which is useful in for loops below
    if (oldsize >= size) return;
    long long newsize = std::max(0, oldsize);
    while (newsize < size) {
      newsize = newsize * resize_factor + 1;
    }
    _int2type.resize(2 * newsize + 1);
    int2type = _int2type.begin() + newsize;
    long long i = _int2type.size() - 1;
    for (; i > newsize + oldsize; --i) _int2type[i] = init;
    for (; i >= newsize - oldsize; --i) _int2type[i] = std::move(_int2type[i - newsize + oldsize]);
    for (; i >= 0; --i) _int2type[i] = init;
  }

  typename std::vector<T>::iterator begin() { return _int2type.begin(); }
  typename std::vector<T>::const_iterator begin() const { return _int2type.begin(); }
  typename std::vector<T>::iterator end() { return _int2type.end(); }
  typename std::vector<T>::const_iterator end() const { return _int2type.end(); }

  size_t reserved() const { return _int2type.size(); }
};

}  // namespace rs