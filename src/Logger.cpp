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
#include "ConstrExp.hpp"

namespace rs {

Logger::Logger(const std::string& proof_log_name) {
  formula_out = std::ofstream(proof_log_name + ".formula");
  formula_out << "* #variable= 0 #constraint= 0\n";
  formula_out << " >= 0 ;\n";
  ++last_formID;
  proof_out = std::ofstream(proof_log_name + ".proof");
  proof_out << "pseudo-Boolean proof version 1.1\n";
  proof_out << "l 1\n";
  ++last_proofID;
}

void Logger::flush() {
  formula_out.flush();
  proof_out.flush();
}

void Logger::logComment([[maybe_unused]] const std::string& comment) {
#if !NDEBUG
  proof_out << "* " << stats.getDetTime() << " " << comment << "\n";
#endif
}

ID Logger::logAsInput(const CeSuper& ce) {
  formula_out << *ce << "\n";
  proof_out << "l " << ++last_formID << "\n";
  ID id = ++last_proofID;
  ce->resetBuffer(id);  // ensure consistent proofBuffer
  return id;
}

ID Logger::logProofLine(const CeSuper& ce) {
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
    proof_out << "p " << buffer << "0\n";
    ce->resetBuffer(id);
  } else {  // line is just one id, don't print it
    id = std::stoll(buffer);
  }
#if !NDEBUG
  proof_out << "e " << id << " " << *ce << "\n";
#endif
  return id;
}

ID Logger::logProofLineWithInfo(const CeSuper& ce, [[maybe_unused]] const std::string& info) {
#if !NDEBUG
  logComment(info);
#endif
  return logProofLine(ce);
}

void Logger::logInconsistency(const CeSuper& ce) {
  assert(ce->isInconsistency());
  ID id = logProofLineWithInfo(ce, "Inconsistency");
  proof_out << "c " << id << " 0" << std::endl;
}

void Logger::logUnit(const CeSuper& ce) {
  assert(ce->isUnitConstraint());
  unitIDs.push_back(logProofLineWithInfo(ce, "Unit"));
}

}  // namespace rs
