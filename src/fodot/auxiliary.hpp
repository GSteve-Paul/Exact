/**********************************************************************
This file is part of Exact.

Copyright (c) 2022 Jo Devriendt

Exact is free software: you can redistribute it and/or modify it under
the terms of the GNU Affero General Public License version 3 as
published by the Free Software Foundation.

Exact is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE. See the GNU Affero General Public
License version 3 for more details.

You should have received a copy of the GNU Affero General Public
License version 3 along with Exact. See the file used_licenses/COPYING
or run with the flag --license=AGPLv3. If not, see
<https://www.gnu.org/licenses/>.
**********************************************************************/

#pragma once

namespace fodot {

template <typename T, typename U>
std::ostream& operator<<(std::ostream& o, const std::pair<T, U>& p) {
  o << p.first << "," << p.second;
  return o;
}
template <typename T, typename U, typename HASH>
std::ostream& operator<<(std::ostream& o, const std::unordered_map<T, U, HASH>& m) {
  for (const auto& e : m) o << e << ";";
  return o;
}
template <typename T, typename HASH>
std::ostream& operator<<(std::ostream& o, const std::unordered_set<T, HASH>& m) {
  for (const auto& e : m) o << e << " ";
  return o;
}
template <typename T>
std::ostream& operator<<(std::ostream& o, const std::vector<T>& m) {
  for (const auto& e : m) o << e << " ";
  return o;
}
template <typename T>
std::ostream& operator<<(std::ostream& o, const std::list<T>& m) {
  for (const auto& e : m) o << e << " ";
  return o;
}

template <class T>
struct streamer {
  const T& val;
};
template <class T>
streamer(T) -> streamer<T>;

template <class T>
std::ostream& operator<<(std::ostream& os, streamer<T> s) {
  os << s.val;
  return os;
}

template <class... Ts>
std::ostream& operator<<(std::ostream& os, streamer<std::variant<Ts...>> sv) {
  std::visit([&os](const auto& v) { os << streamer{v}; }, sv.val);
  return os;
}

namespace aux {
// TODO: c++20 - https://en.cppreference.com/w/cpp/container/unordered_map/erase_if
template <class Key, class T, class Hash, class KeyEqual, class Alloc, class Pred>
typename std::unordered_map<Key, T, Hash, KeyEqual, Alloc>::size_type erase_if(
    std::unordered_map<Key, T, Hash, KeyEqual, Alloc>& c, Pred pred) {
  auto old_size = c.size();
  for (auto i = c.begin(), last = c.end(); i != last;) {
    if (pred(*i)) {
      i = c.erase(i);
    } else {
      ++i;
    }
  }
  return old_size - c.size();
}

template <typename T>
T concat(const T& v1, const T& v2) {
  T res(v1);
  res.reserve(v1.size() + v2.size());
  res.insert(res.end(), v2.begin(), v2.end());
  return res;
}

template <typename T>
bool disjoint(const T& coll1, const T& coll2) {
  for (const auto& x : coll2) {
    if (coll1.count(x)) return false;
  }
  return true;
}

template <typename T, typename S, typename LAMBDA>
void addCombinations(T& collection, const S& iterable, LAMBDA&& join) {
  T old;
  std::swap(collection, old);
  collection.reserve(old.size() * iterable.size());
  for (const auto& i : old) {
    for (const auto& j : iterable) {
      collection.push_back(join(i, j));
    }
  }
}

}  // namespace aux

}  // namespace fodot