/**********************************************************************
This file is part of Exact.

Copyright (c) 2022-2023 Jo Devriendt, Nonfiction Software

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

#include "Logger.hpp"
#include "constraints/ConstrExp.hpp"

namespace xct {

Logger::Logger(const Stats& s) : stats(s), active(false), last_formID(ID_Trivial), last_proofID(ID_Trivial) {}

std::ostream& Logger::proofStream() {
#if WITHZLIB
  if (proof_is_zip)
    return proof_out_zip;
  else
#endif  // WITHZLIB
    return proof_out;
}

void Logger::activate(const std::string& proof_log_name, [[maybe_unused]] const bool zip) {
  if (proof_log_name == "") return;
  flush();
  formula_out = std::ofstream(proof_log_name + ".formula");
  formula_out << "* #variable= 0 #constraint= 0\n";
  formula_out << " >= 0 ;\n";

#if WITHZLIB
  proof_is_zip = zip;
  if (proof_is_zip)
    proof_out_zip.open((proof_log_name + ".proof.zip").c_str());
  else
#endif  // WITHZLIB
    proof_out.open(proof_log_name + ".proof");

  proofStream() << "pseudo-Boolean proof version 1.1\n";
  proofStream() << "l 1\n";
  active = true;
}

void Logger::deactivate() {
  flush();
  active = false;
}

bool Logger::isActive() { return active; }

void Logger::flush() {
  if (!active) return;
  formula_out.flush();
  proof_out.flush();
}

void Logger::logComment([[maybe_unused]] const std::string& comment) {
  if (!active) return;
#if !NDEBUG
  proofStream() << "* " << comment << " " << stats.getDetTime() << "\n";
#endif
}

ID Logger::logInput(const CeSuper& ce) {
  if (!active) return ++last_proofID;
  formula_out << *ce << "\n";
  proofStream() << "l " << ++last_formID << "\n";
  ++last_proofID;
  ce->resetBuffer(last_proofID);  // ensure consistent proofBuffer
  return last_proofID;
}

ID Logger::logAssumption(const CeSuper& ce) {
  if (!active) return ++last_proofID;
  proofStream() << "a " << *ce << "\n";
  ++last_proofID;
  ce->resetBuffer(last_proofID);  // ensure consistent proofBuffer
  return last_proofID;
}

ID Logger::logProofLine(const CeSuper& ce) {
  if (!active) return ++last_proofID;
  std::string buffer = ce->proofBuffer.str();
  assert(buffer.back() == ' ');
  long long spacecount = 0;
  for (char const& c : buffer) {
    spacecount += (c == ' ');
    if (spacecount > 1) break;
  }
  ID id;
  if (spacecount > 1) {  // non-trivial line
    id = ++last_proofID;
    proofStream() << "pol " << buffer << "\n";
    ce->resetBuffer(id);
  } else {  // line is just one id, don't print it
    id = std::stoll(buffer);
  }
#if !NDEBUG
  proofStream() << "e " << id << " : " << *ce << "\n";
#endif
  return id;
}

ID Logger::logProofLineWithInfo(const CeSuper& ce, [[maybe_unused]] const std::string& info) {
  if (!active) return ++last_proofID;
#if !NDEBUG
  logComment(info);
#endif
  return logProofLine(ce);
}

void Logger::logInconsistency(const CeSuper& ce, const IntMap<int>& level, const std::vector<int>& position) {
  if (!active) return;
  ce->removeUnitsAndZeroes(level, position);
  assert(ce->isInconsistency());
  ID id = logProofLineWithInfo(ce, "Inconsistency");
  proofStream() << "c " << id << "" << std::endl;
}

void Logger::logUnit(const CeSuper& ce) {
  if (!active) return;
  assert(ce->isUnitConstraint());
  unitIDs.push_back(logProofLineWithInfo(ce, "Unit"));
}

ID Logger::logRUP(Lit l, Lit ll) {
  if (!active) return ++last_proofID;
  proofStream() << "u " << (std::pair<int, Lit>{1, l}) << " " << (std::pair<int, Lit>{1, ll}) << " >= 1 ;\n";
  return ++last_proofID;
}

ID Logger::logImpliedUnit(Lit implying, Lit implied) {
  if (!active) return ++last_proofID;
#if !NDEBUG
  logComment("Implied unit");
#endif
  ID result = logResolvent(logRUP(implying, implied), logRUP(-implying, implied));
#if !NDEBUG
  proofStream() << "e " << result << " : " << (std::pair<int, Lit>{1, implied}) << " >= 1 ;\n";
#endif
  return result;
}

ID Logger::logPure(const CeSuper& ce) {
  if (!active) return ++last_proofID;
  assert(ce->vars.size() == 1);
#if !NDEBUG
  logComment("Pure");
#endif
  Lit l = ce->getLit(ce->vars[0]);
  proofStream() << "red " << (std::pair<int, Lit>{1, l}) << " >= 1 ; x" << toVar(l) << " " << (l > 0) << "\n";
  ++last_proofID;
  ce->resetBuffer(last_proofID);  // ensure consistent proofBuffer
  return last_proofID;
}

ID Logger::logDomBreaker(const CeSuper& ce) {
  if (!active) return ++last_proofID;
  assert(ce->vars.size() == 2);
#if !NDEBUG
  logComment("Dominance breaking");
#endif
  Lit a = ce->getLit(ce->vars[0]);
  Lit b = ce->getLit(ce->vars[1]);
  proofStream() << "red " << (std::pair<int, Lit>{1, a}) << " " << (std::pair<int, Lit>{1, b}) << " >= 1 ; x"
                << toVar(a) << " )" << (a < 0) << " x" << toVar(b) << " " << (b > 0) << "\n";
  ++last_proofID;
  ce->resetBuffer(last_proofID);  // ensure consistent proofBuffer
  return last_proofID;
}

ID Logger::logAtMostOne(const ConstrSimple32& c, const CeSuper& ce) {
  if (!active) return ++last_proofID;
  assert(c.size() > 1);
#if !NDEBUG
  logComment("Implied at-most-one");
#endif
  std::stringstream buffer;
  ID previous = ID_Trivial;
  for (int i = 1; i < (int)c.size(); ++i) {
    buffer << "pol " << previous << " ";
    if (i > 2) buffer << i - 1 << " * ";
    for (int j = 0; j < i; ++j) {
      buffer << logRUP(c.terms[i].l, c.terms[j].l) << " + ";
    }
    if (i > 1) buffer << i << " d";
    proofStream() << buffer.rdbuf() << "\n";
    previous = ++last_proofID;
  }
#if !NDEBUG
  proofStream() << "e " << last_proofID << " : ";
  c.toStreamAsOPB(proof_out);
  proofStream() << "\n";
#endif
  ce->resetBuffer(last_proofID);
  return last_proofID;
}

ID Logger::logResolvent(ID id1, ID id2) {  // should be clauses
  if (!active) return ++last_proofID;
  assert(isValid(id1));
  assert(isValid(id2));
#if !NDEBUG
  logComment("Resolve");
#endif
  if (id1 == ID_Trivial) return id2;
  if (id2 == ID_Trivial) return id1;
  proofStream() << "pol " << id1 << " " << id2 << " + s\n";
  return ++last_proofID;
}

std::pair<ID, ID> Logger::logEquality(Lit a, Lit b, ID aImpReprA, ID reprAImplA, ID bImpReprB, ID reprBImplB,
                                      [[maybe_unused]] Lit reprA, [[maybe_unused]] Lit reprB) {
  if (!active) {
    last_proofID += 2;
    return {last_proofID - 1, last_proofID};
  }
#if !NDEBUG
  logComment("Equality");
#endif
  ID aImpliesB = logRUP(-a, b);
  proofStream() << "pol " << reprAImplA << " " << aImpliesB << " + " << bImpReprB << " + s\n";
  ID reprAImpReprB = ++last_proofID;
#if !NDEBUG
  proofStream() << "e " << reprAImpReprB << " : " << (std::pair<int, Lit>{1, -reprA}) << " "
                << (std::pair<int, Lit>{1, reprB}) << " >= 1 ;\n";
#endif
  ID bImpliesA = logRUP(-b, a);
  proofStream() << "pol " << reprBImplB << " " << bImpliesA << " + " << aImpReprA << " + s\n";
  ID reprBImpReprA = ++last_proofID;
#if !NDEBUG
  proofStream() << "e " << reprBImpReprA << " : " << (std::pair<int, Lit>{1, -reprB}) << " "
                << (std::pair<int, Lit>{1, reprA}) << " >= 1 ;\n";
#endif
  return {reprAImpReprB, reprBImpReprA};
}
}  // namespace xct
