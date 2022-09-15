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

#include "Theory.hpp"
#include <boost/tokenizer.hpp>
#include <fstream>
#include <memory>
#include "../ILP.hpp"
#include "Expression.hpp"
#include "IneqExpr.hpp"
#include "auxiliary.hpp"
#include "doctest/doctest.h"

namespace fodot {

std::string toBuiltin(const std::string& s) { return BUILTINPRE + s + BUILTINPOST; }
std::string fromBuiltin(const std::string& s) {
  assert(!s.empty());
  assert(s[0] == BUILTINPRE);
  assert(s.back() == BUILTINPOST);
  return s.substr(1, s.size() - 1);
}

Functor* Vocabulary::createFunctor(const std::string& name, const std::vector<Type>& types,
                                   const std::vector<DomEl>& range) {
  assert(!hasFunctor(name));
  return name2functor.emplace(name, std::make_unique<Functor>(name, types, range)).first->second.get();
}
Functor* Vocabulary::createFunctor(const std::string& name, const std::vector<Type>& types, const Functor& r) {
  assert(!hasFunctor(name));
  return name2functor.emplace(name, std::make_unique<Functor>(name, types, r.getInterAsSet())).first->second.get();
}
Functor* Vocabulary::createBoolean(const std::string& name, const std::vector<Type>& types) {
  assert(!hasFunctor(name));
  return name2functor.emplace(name, std::make_unique<Functor>(name, types)).first->second.get();
}
Functor* Vocabulary::createType(const std::string& name, const std::vector<DomEl>& inter) {
  return createInterpreted(name,
                           xct::aux::comprehension(inter,
                                                   [](const DomEl& de) {
                                                     return Tup{de, DomEl(true)};
                                                   }),
                           DomEl(false));
}
Functor* Vocabulary::createInterpreted(const std::string& name, const std::vector<Tup>& inter, const DomEl& otherwise) {
  assert(!inter.empty());
  std::vector<Type> types = xct::aux::comprehension(inter[0], [](const DomEl& de) { return getType(de); });
  std::vector<DomEl> range;
  range.reserve(inter.size() + 1);
  if (otherwise != _unknown_) range.push_back(otherwise);
  for (const Tup& t : inter) {
    range.push_back(t.back());
  }
  if (getType(range[0]) == Type::INT) {
    range = getIntRange(getExtrema(range));
  }
  Functor* f = createFunctor(name, types, range);
  for (const Tup& t : inter) {
    f->setInter(Tup(t.begin(), t.end() - 1), t.back());
  }
  f->setDefault(otherwise);
  return f;
}
void tupToConstructedString(std::ostream& ss, const Tup& t) {
  for (const DomEl& de : t) {
    if (std::holds_alternative<std::string>(de)) {
      ss << std::get<std::string>(de);
    } else {
      ss << de;
    }
    ss << ",";
  }
}
std::vector<Functor*> Vocabulary::createConstructed(const std::string& type, const std::string& constructor,
                                                    const std::vector<std::pair<std::string, Functor*>>& attributes) {
  std::vector<std::string> domels = {};
  std::vector<std::string> newdomels = {constructor + '('};
  std::vector<Tup> interpretation = {};
  std::vector<Tup> newInterpretation = {{}};
  for (const std::pair<std::string, Functor*>& attr : attributes) {
    std::vector<Tup> scpe = attr.second->getInterAsRange();
    std::swap(domels, newdomels);
    newdomels.clear();
    std::swap(interpretation, newInterpretation);
    newInterpretation.clear();
    for (const Tup& t : scpe) {
      for (const Tup& t2 : interpretation) {
        newInterpretation.push_back(aux::concat(t2, t));
      }
      for (const std::string& domel : domels) {
        std::stringstream ss;
        ss << domel;
        tupToConstructedString(ss, t);
        newdomels.push_back(ss.str());
      }
    }
  }
  std::vector<DomEl> inter = xct::aux::comprehension(newdomels, [](std::string& s) {
    s.pop_back();
    s.push_back(')');
    return DomEl(s);
  });

  // construct type functor
  Functor* typeFunc = createType(type, inter);

  // construct constructor functor
  assert(inter.size() == newInterpretation.size());
  for (int i = 0; i < (int)inter.size(); ++i) {
    newInterpretation[i].push_back(inter[i]);
  }
  Functor* constrFunc = createInterpreted(constructor, newInterpretation, _unknown_);

  // construct attribute functors
  std::vector<Functor*> res = {typeFunc, constrFunc};
  res.reserve(2 + attributes.size());
  for (int i = 0; i < (int)attributes.size(); ++i) {
    std::vector<Tup> newInter = xct::aux::comprehension(newInterpretation, [i](const Tup& x) {
      return Tup{x.back(), x[i]};
    });
    res.push_back(createInterpreted(attributes[i].first, newInter, _unknown_));
    [[mayb_unused]] std::vector<DomEl> attrange = attributes[i].second->getInterAsSet();
    assert(attrange.size() == res.back()->range.size());
    assert(
        std::all_of(attrange.begin(), attrange.end(), [res](const DomEl& de) { return res.back()->range.count(de); }));
  }
  return res;
}
Functor* Vocabulary::createTseitin(const std::string& repr) {
  std::string name = toBuiltin(repr);
  if (hasFunctor(name)) return nullptr;
  return createBoolean(name, {});
}

bool Vocabulary::hasFunctor(const std::string& name) { return name2functor.find(name) != name2functor.cend(); }

Functor* Vocabulary::getFunctor(const std::string& name) {
  assert(hasFunctor(name));
  return name2functor.find(name)->second.get();
}

Vocabulary::Vocabulary() { addBuiltins(); }

void Vocabulary::addBuiltins() {
  // TODO: using procedural interpretation. They may have infinite range, but this is ok with finite interpretation.
}

void Vocabulary::parseCsv(const std::string& filename) {
  std::string line;
  std::ifstream csv;
  csv.open(filename);

  if (!csv.is_open()) {
    throw std::invalid_argument("Could not open " + filename);
  }

  std::vector<std::vector<std::string>> data;

  boost::char_separator<char> sep(",;", "", boost::keep_empty_tokens);

  while (std::getline(csv, line)) {
    boost::tokenizer<boost::char_separator<char>> tok(line, sep);
    data.emplace_back();
    data.back().assign(tok.begin(), tok.end());
  }

  for (int i = 0; i < (int)data[0].size(); ++i) {
    std::unordered_set<DomEl> range;
    range.reserve((int)data.size() - 1);
    for (int j = 1; j < (int)data.size(); ++j) {
      DomEl de = toDomEl(data[j][i]);
      range.insert(de);
    }
    if (i > 0) {
      Functor* ftor = createFunctor(data[0][i], {Type::STRING, getType(*range.cbegin())},
                                    std::vector<DomEl>(range.cbegin(), range.cend()));
      if (ftor->getReturnType() == Type::BOOL) {
        ftor->setDefault(false);
      }
    } else {  // add type predicate
      Functor* ftor = createFunctor(data[0][i], {Type::STRING, Type::BOOL}, {false, true});
      ftor->setDefault(false);
      for (const DomEl& de : range) {
        ftor->setInter({de}, true);
      }
    }
  }

  for (int i = 1; i < (int)data[0].size(); ++i) {
    for (int j = 1; j < (int)data.size(); ++j) {
      getFunctor(data[0][i])->setInter({data[j][0]}, data[j][i]);
    }
  }

  for (const auto& header : data[0]) {
    std::cout << getFunctor(header) << std::endl;
  }
}
void Vocabulary::addTo(xct::ILP& ilp) {
  for (const auto& el : name2functor) {
    el.second->addTo(ilp);
  }
}
void Vocabulary::readModel(xct::ILP& ilp) {
  assert(ilp.hasSolution());
  for (const auto& el : name2functor) {
    el.second->readExtension(ilp);
  }
}

std::ostream& operator<<(std::ostream& o, const Vocabulary& v) {
  for (const auto& pair : v.name2functor) {
    o << *pair.second << std::endl;
  }
  return o;
}

void Theory::addTo(xct::ILP& ilp) {
  std::vector<std::pair<Term, IneqTerm>> tseitin2constr;
  for (const Term& tt : constraints) {
    std::cout << "TRANSLATING " << tt << std::endl;
    std::vector<Term> stripped;
    tt->instantiateVars(InstVarState::ATTOP)->stripTopAnds(stripped);
    for (const Term& t : stripped) {
      assert(t->type == Type::BOOL);
      std::string name = t->getRepr();
      Functor* tseitin = voc.createTseitin(name);
      if (!tseitin) continue;  // apparently already exists
      std::vector<Term> args;
      Term t_tseitin = std::make_shared<Application>(*tseitin, args);
      args = {std::make_shared<Unary>(Op::Not, t_tseitin), t};
      Term t2 = std::make_shared<Nary>(Op::Or, args);
      IneqTerm it = t2->translateFull();
      it->collectDomains();
      tseitin2constr.push_back({t_tseitin, it});
    }
  }
  voc.addTo(ilp);
  std::vector<xct::IntVar*> assumptions;
  assumptions.reserve(tseitin2constr.size());
  for (const auto& tc : tseitin2constr) {
    xct::IntVar* iv = ilp.getVarFor(tc.first->getRepr());
    if (iv) {
      assumptions.push_back(iv);
      tc.second->addToAsTop(ilp);
    }  // else tc.second is tautology // TODO: add assert!
  }
  ilp.setAssumptions(std::vector<bigint>(assumptions.size(), 1), assumptions);
}

void Theory::addMijnCollega() {
  Functor& Locatie = *voc.createType("Locatie", {"adam", "bdam", "cdam"});
  Functor& afstand = *voc.createInterpreted("afstand",
                                            {{"adam", "bdam", 10},
                                             {"adam", "cdam", 20},
                                             {"bdam", "adam", 10},
                                             {"bdam", "cdam", 10},
                                             {"cdam", "adam", 20},
                                             {"cdam", "bdam", 10}},
                                            0);

  Functor& Professional = *voc.createType(
      "Professional", {"Truus", "Quentin",  "Nette",  "Miro", "Rune",    "Olaf", "Bert",  "Dirk",   "Carlo", "Ine",
                       "Els",   "Patricia", "Fatima", "Gino", "Hillary", "Jos",  "Klaas", "Selene", "Ahmed", "Louis"});
  Functor& locatie = *voc.createInterpreted(
      "locatie", {{"Truus", "bdam"}, {"Quentin", "bdam"},  {"Nette", "bdam"},  {"Miro", "adam"},  {"Rune", "adam"},
                  {"Olaf", "adam"},  {"Bert", "bdam"},     {"Dirk", "bdam"},   {"Carlo", "adam"}, {"Ine", "adam"},
                  {"Els", "adam"},   {"Patricia", "adam"}, {"Fatima", "bdam"}, {"Gino", "adam"},  {"Hillary", "bdam"},
                  {"Jos", "bdam"},   {"Klaas", "adam"},    {"Selene", "bdam"}, {"Ahmed", "adam"}, {"Louis", "bdam"}},
      _unknown_);
  Functor& maxAfstand = *voc.createInterpreted(
      "maxAfstand",
      {{"Truus", 10},   {"Quentin", 20}, {"Nette", 15}, {"Miro", 10},   {"Rune", 10},     {"Olaf", 20},   {"Bert", 15},
       {"Dirk", 10},    {"Carlo", 20},   {"Ine", 20},   {"Els", 15},    {"Patricia", 15}, {"Fatima", 20}, {"Gino", 10},
       {"Hillary", 15}, {"Jos", 10},     {"Klaas", 15}, {"Selene", 15}, {"Ahmed", 10},    {"Louis", 20}},
      0);
  Functor& maxPerWeek = *voc.createInterpreted(
      "maxPerWeek",
      {{"Truus", 5},   {"Quentin", 7}, {"Nette", 8}, {"Miro", 7},   {"Rune", 8},     {"Olaf", 9},   {"Bert", 6},
       {"Dirk", 8},    {"Carlo", 7},   {"Ine", 8},   {"Els", 9},    {"Patricia", 6}, {"Fatima", 5}, {"Gino", 6},
       {"Hillary", 7}, {"Jos", 9},     {"Klaas", 5}, {"Selene", 9}, {"Ahmed", 5},    {"Louis", 6}},
      _unknown_);

  Functor& Shift = *voc.createType("Shift", {"avond consult", "avond visite", "nacht", "vroeg visite", "vroeg consult",
                                             "laat visite", "laat consult"});
  int maxDagen = 14;
  Functor& Dag = *voc.createType("Dag", getIntRange({0, maxDagen - 1}));
  Functor& Uur = *voc.createType("Uur", getIntRange({0, 23}));
  Functor& Moment = *voc.createType("Moment", getIntRange({0, (maxDagen + 1) * 24}));

  Functor& Week = *voc.createType("Week", getIntRange({0, maxDagen / 7 - 1}));

  Functor& Dienst = *voc.createBoolean("Dienst", {Type::STRING});
  Functor& dag = *voc.createFunctor("dag", {Type::STRING, Type::INT}, Dag);
  Functor& week = *voc.createFunctor("week", {Type::STRING, Type::INT}, Week);
  Functor& loc = *voc.createFunctor("loc", {Type::STRING, Type::STRING}, Locatie);
  Functor& start = *voc.createFunctor("start", {Type::STRING, Type::INT}, Moment);
  Functor& eind = *voc.createFunctor("eind", {Type::STRING, Type::INT}, Moment);
  Functor& shift = *voc.createFunctor("shift", {Type::STRING, Type::STRING}, Shift);
  Functor& weekdag =
      *voc.createFunctor("weekdag", {Type::STRING, Type::STRING},
                         {"maandag", "dinsdag", "woensdag", "donderdag", "vrijdag", "zaterdag", "zondag"});

  std::vector<std::string> weekdagen = {"maandag", "dinsdag", "woensdag", "donderdag", "vrijdag"};
  std::vector<std::string> weekenddagen = {"zaterdag", "zondag"};
  std::vector<std::tuple<std::string, int, int>> weekshifts = {
      {"avond consult", 18, 23}, {"avond visite", 17, 23}, {"nacht", 23, 8}};
  std::vector<std::tuple<std::string, int, int>> weekendshifts = {
      {"vroeg consult", 8, 23}, {"vroeg visite", 8, 23}, {"laat consult", 23, 8}, {"laat visite", 23, 8}};

  for (const auto& l : Locatie.getInterAsSet()) {
    fo_int dagcounter = 0;
    for (const auto& w : Week.getInterAsSet()) {
      for (const auto& wd : weekdagen) {
        for (const auto& ws : weekshifts) {
          std::string s =
              "d" + std::to_string(dagcounter) + " " + std::get<std::string>(l) + " " + wd + " " + std::get<0>(ws);
          Dienst.setInter({s}, true);
          dag.setInter({s}, dagcounter);
          week.setInter({s}, w);
          loc.setInter({s}, l);
          fo_int strt = std::get<1>(ws);
          fo_int end = std::get<2>(ws);
          start.setInter({s}, dagcounter * 24 + strt);
          eind.setInter({s}, (strt >= end ? 24 : 0) + dagcounter * 24 + end);
          shift.setInter({s}, std::get<0>(ws));
          weekdag.setInter({s}, wd);
        }
        ++dagcounter;
      }
      for (const auto& wkd : weekenddagen) {
        for (const auto& wks : weekendshifts) {
          std::string s =
              "d" + std::to_string(dagcounter) + " " + std::get<std::string>(l) + " " + wkd + " " + std::get<0>(wks);
          Dienst.setInter({s}, true);
          dag.setInter({s}, dagcounter);
          week.setInter({s}, w);
          loc.setInter({s}, l);
          fo_int strt = std::get<1>(wks);
          fo_int end = std::get<2>(wks);
          start.setInter({s}, dagcounter * 24 + strt);
          eind.setInter({s}, (strt >= end ? 24 : 0) + dagcounter * 24 + end);
          shift.setInter({s}, std::get<0>(wks));
          weekdag.setInter({s}, wkd);
        }
        ++dagcounter;
      }
    }
  }
  Dienst.setDefault(false);
  std::cout << Dienst << std::endl;

  Functor& maxDiensten = *voc.createFunctor("maxDiensten", {Type::STRING, Type::INT}, getIntRange({0, 500}));
  for (const auto& p : Professional.getInterAsSet()) {
    maxDiensten.setInter({p}, 15);
  }

  int maxOnbeschikbaar = 4;
  Functor& onbeschikbaar = *voc.createBoolean("onbeschikbaar", {Type::STRING, Type::INT});
  for (const auto& p : Professional.getInterAsSet()) {
    for (int i = 0; i < maxOnbeschikbaar; ++i) {
      for (int j = 0; j < maxOnbeschikbaar; ++j) {
        fo_int rdag = xct::aux::getRand(0, maxDagen);
        fo_int ruur = xct::aux::getRand(0, 24);
        const Tup tup = {p, rdag * 24 + ruur};
        if (onbeschikbaar.getInter(tup) == _unknown_) {
          onbeschikbaar.setInter(tup, true);
        }
      }
    }
  }
  onbeschikbaar.setDefault(false);

  Functor& toegewezen = *voc.createFunctor("toegewezen", {Type::STRING, Type::STRING}, Professional);

  std::shared_ptr<Var> d = V("d");
  std::shared_ptr<Var> d2 = V("d2");
  std::shared_ptr<Var> r = V("r");
  std::shared_ptr<Var> p = V("p");
  std::shared_ptr<Var> l1 = V("l1");
  std::shared_ptr<Var> l2 = V("l2");
  std::shared_ptr<Var> w = V("w");
  std::shared_ptr<Var> m = V("m");

  // Een professional werkt niet meer diensten dan aangegeven
  // !p in Professional: #{d : toegewezen(d)=p}=<maxDiensten(p).
  Term t1 = all({"p"}, Professional, O(">=", A(maxDiensten, p), count({"d"}, Dienst, O("=", p, A(toegewezen, d)))));
  constraints.push_back(t1);
  // Een professional werkt enkel op een dienst die dichtbij is
  // !p in Professional, d in Dienst: toegewezen(d)=p => afstand(locatie(p),loc(d)) =< maxAfstand(p).
  Term t2 =
      all({{{"p"}, Professional}, {{"d"}, Dienst}},
          O("implies", O("=", A(toegewezen, p), d), O("=<", A(afstand, A(locatie, p), A(loc, d)), A(maxAfstand, p))));
  constraints.push_back(t2);
  // Een professional werkt niet op een dienst waarvoor die onbeschikbaar is
  // !p in Professional, d in Dienst, m in Moment: toegewezen(p)=d & onbeschikbaar(p,m) => m<start(d) | eind(d)<=m.
  Term t3 = all({{{"p"}, Professional}, {{"d"}, Dienst}, {{"m"}, Moment}},
                O("implies", O("and", O("=", A(toegewezen, d), p), A(onbeschikbaar, p, m)),
                  O("or", O(">", A(start, d), m), O(">=", m, A(eind, d)))));
  constraints.push_back(t3);
  // Een professional werkt op hoogstens één locatie tegelijk.
  // !p in Professional, d in Dag: #{d2 in Dienst: toegewezen(p)=d2 & dag(d2)=d} =< 1.
  Term t4 = all({{{"p"}, Professional}, {{"d"}, Dag}},
                O(">=", D(1), count({"d2"}, Dienst, O("and", O("=", A(toegewezen, d2), p), O("=", A(dag, d2), d)))));
  std::cout << t4->translateFull() << std::endl;
  constraints.push_back(t4);
  // Beperking opeenvolgende diensten
  // !p in Professional, d in Dienst, d2 in Dienst: ingeroosterd(p,d) & ingeroosterd(p,volgende(d)) =>
  // opeenvolgend(p).
  //  Term t4 = all({{{"p"}, Professional}, {{"d"}, Dienst}},
  //                O("implies", O("and", A(ingeroosterd, p, d), A(ingeroosterd, p, A(volgende, d))), A(opeenvolgend,
  //                p)));
  //  constraints.push_back(t4);
  // Beperkt aantal diensten per week
  // !p in Professional, w in Week: #{d in Dienst: week(d)=w & ingeroosterd(p,d)} =< maxPerWeek(p).
  //  Term t5 =
  //      all({{{"p"}, Professional}, {{"w"}, Week}},
  //          O("=<", count({"d"}, Dienst, O("and", O("=", A(week, d), w), A(ingeroosterd, p, d))), A(maxPerWeek,
  //          p)));
  //  constraints.push_back(t5);
}

std::ostream& operator<<(std::ostream& o, const Theory& theo) {
  o << "definitions:\n";
  o << theo.voc << std::endl;
  o << "constraints:\n";
  for (const Term& t : theo.constraints) o << t << std::endl;
  return o;
}

}  // namespace fodot

using namespace fodot;

TEST_CASE("Add vocabulary to ILP") {
  Vocabulary voc;

  Term t_a = D("a");
  Functor* f_D = voc.createFunctor("D", {Type::STRING, Type::STRING}, {"a", "b", "c"});
  f_D->setInter({"a"}, "b");

  std::vector<Term> args = {t_a};
  Term t_Da = std::make_shared<Application>(*f_D, args);
  Term t_eq = std::make_shared<Binary>(Op::Equals, t_Da, t_a);

  args = {};
  Functor* f_P = voc.createFunctor("P", {Type::INT, Type::BOOL}, {true, false});
  f_P->setInter({1}, true);
  f_P->setDefault(false);

  Functor* f_C = voc.createFunctor("C", {Type::INT}, {0, 1, 2, 3});
  f_C->setInter({}, 3);
  Term t_C = std::make_shared<Application>(*f_C, args);
  Term t_1 = D(1);
  args = {t_1};
  Term t_P = std::make_shared<Application>(*f_P, args);
  Term t_eq2 = std::make_shared<Binary>(Op::Equals, t_C, t_1);
  Term t_iff = std::make_shared<Binary>(Op::Iff, t_P, t_eq2);

  xct::ILP ilp(true);
  IneqTerm ti_eq = t_eq->translate()->pushNegation()->toIneq()->flatten();
  ti_eq->collectDomains();
  t_iff = t_iff->translate();
  t_iff = t_iff->pushNegation();
  IneqTerm ti_iff = t_iff->toIneq();
  ti_iff->collectDomains();

  voc.addTo(ilp);

  std::stringstream ss;
  ilp.printInput(ss);

  CHECK(ss.str() ==
        "OBJ >= 0\n"
        "1 >= 1 D(\"a\")=\"a\" 1 D(\"a\")=\"b\" 1 D(\"a\")=\"c\" >= 1\n"
        "1 >= 1 D(\"a\")=\"b\" >= 1\n"
        "1 >= 1 P(1) >= 1\n"
        "3 >= 1 C[0,3] >= 3\n");
}

TEST_CASE("Add full theory to ILP") {
  Theory theo;

  xct::ILP ilp(true);
  Term t_a = D("a");
  Functor* f_D = theo.voc.createFunctor("D", {Type::STRING, Type::STRING}, {"a", "b", "c"});
  std::vector<Term> args = {t_a};
  Term t_Da = std::make_shared<Application>(*f_D, args);
  Term t_eq = std::make_shared<Binary>(Op::Equals, t_Da, t_a);
  Functor* f_P = theo.voc.createFunctor("P", {Type::BOOL}, {false, true});
  args = {};
  Term t_P = std::make_shared<Application>(*f_P, args);
  args = {t_eq, t_P};
  Term t_or = std::make_shared<Nary>(Op::Or, args);
  theo.constraints.push_back(t_or);
  std::vector<Term> stripped;
  t_or->instantiateVars(InstVarState::ATTOP)->stripTopAnds(stripped);
  CHECK(stripped.size() == 1);
  CHECK(stripped[0]->getRepr() == t_or->getRepr());

  ilp.global.stats.startTime = std::chrono::steady_clock::now();

  theo.addTo(ilp);
  ilp.init(true, false);

  std::stringstream ss;
  ilp.printFormula(ss);
  CHECK(ss.str() ==
        "* #variable= 5 #constraint= 3\n"
        "min: ;\n"
        "+1 x3 +1 x4 +1 x5 >= 1 ;\n"
        "+1 ~x3 +1 ~x4 +1 ~x5 >= 2 ;\n"
        "+1 ~x1 +1 x2 +1 x5 >= 1 ;\n");
}

TEST_CASE("Small satisfiable problem") {
  Theory theo;
  std::vector<Term> args;
  Term t_g = D("green");
  Term t_France = D("France");
  Functor* f_Col = theo.voc.createFunctor("Col", {Type::STRING, Type::STRING}, {"green", "blue"});
  args = {t_France};
  Term t_Col_France = std::make_shared<Application>(*f_Col, args);
  Term t_eq = std::make_shared<Binary>(Op::Equals, t_g, t_Col_France);
  Term t_not_eq = std::make_shared<Unary>(Op::Not, t_eq);

  theo.constraints.push_back(t_not_eq);

  xct::ILP ilp(true);

  ilp.global.stats.startTime = std::chrono::steady_clock::now();
  theo.addTo(ilp);
  ilp.init(false, false);
  ilp.global.options.verbosity.parse("0");
  [[maybe_unused]] SolveState state = ilp.runFull();
  REQUIRE(state == SolveState::SAT);
  theo.voc.readModel(ilp);
  CHECK(f_Col->getExtension({"France"}) == DomEl("blue"));

  std::stringstream ss;
  ilp.printInput(ss);
  CHECK(ss.str() ==
        "OBJ >= 0\n"
        "-1 Col(\"France\")=\"green\" -1 [not \"green\"=Col(\"France\")] >= -1\n"
        "1 >= 1 Col(\"France\")=\"blue\" 1 Col(\"France\")=\"green\" >= 1\n");
}

TEST_CASE("Small unsatisfiable problem") {
  Theory theo;
  std::vector<Term> args;
  Term t_g = D("green");
  Term t_France = D("France");
  Functor* f_Col = theo.voc.createFunctor("Col", {Type::STRING, Type::STRING}, {"green", "blue"});
  Term t = O("=", A(*f_Col, D("France")), D("red"));

  theo.constraints.push_back(t);

  xct::ILP ilp(true);
  theo.addTo(ilp);
  ilp.init(false, false);
  ilp.global.options.verbosity.parse("0");
  [[maybe_unused]] SolveState state = ilp.runFull();
  REQUIRE(state == SolveState::INCONSISTENT);
  std::unordered_set<xct::IntVar*> core = ilp.getLastCore();
  CHECK(core.size() == 1);
  auto iv = *core.begin();
  CHECK(iv->getName() == "[\"red\"=Col(\"France\")]");
}

TEST_CASE("Small unsatisfiable problem 2") {
  Theory theo;
  std::vector<Term> args;
  Term t_g = D("green");
  Term t_France = D("France");
  Functor* f_Col = theo.voc.createFunctor("Col", {Type::STRING, Type::STRING}, {"green", "blue"});
  theo.constraints.push_back(O("not", O("=", A(*f_Col, D("France")), D("red"))));
  theo.constraints.push_back(O("not", O("=", A(*f_Col, D("France")), D("green"))));
  theo.constraints.push_back(O("not", O("=", A(*f_Col, D("France")), D("blue"))));

  xct::ILP ilp(true);
  theo.addTo(ilp);
  ilp.init(false, false);
  ilp.global.options.verbosity.parse("0");
  [[maybe_unused]] SolveState state = ilp.runFull();
  REQUIRE(state == SolveState::INCONSISTENT);
  std::unordered_set<xct::IntVar*> core = ilp.getLastCore();
  CHECK(core.size() == 2);
  for (const auto& iv : core) {
    CHECK(iv->getName() != "[\"red\"=Col(\"France\")]");
  }
}

TEST_CASE("Small unsatisfiable problem 3") {
  Theory theo;
  Functor& p = *theo.voc.createType("P", {0, 1, 2});
  Functor& q = *theo.voc.createBoolean("Q", {Type::INT});
  Term t = O("and", all({"x"}, p, A(q, V("x"))), any({"x"}, p, O("and", O("not", A(q, V("x"))), O(">", V("x"), D(1)))));
  theo.constraints.push_back(t);

  xct::ILP ilp(true);
  theo.addTo(ilp);
  ilp.init(false, false);
  ilp.global.options.verbosity.parse("0");
  [[maybe_unused]] SolveState state = ilp.runFull();
  REQUIRE(state == SolveState::INCONSISTENT);
  std::unordered_set<xct::IntVar*> core = ilp.getLastCore();
  CHECK(core.size() == 2);
  std::unordered_set<std::string> toTest = {"[Q(2)]", "[any(and(not Q(x),x>1) for x in P)]"};
  for (const auto& iv : core) {
    CHECK(toTest.count(iv->getName()));
  }
}

TEST_CASE("Empty conjunction and empty disjunction") {
  Theory theo;
  xct::ILP ilp(true);
  ilp.init(false, false);

  Term t = O("and", {});
  CHECK(t->reduceFull()->getRepr() == "true");
  IneqTerm it = t->translateFull();
  CHECK(it->getRepr() == "and()");

  theo.constraints.push_back(t);
  theo.addTo(ilp);
  CHECK(ilp.runFullCatchUnsat() == SolveState::SAT);

  t = O("or", {});
  CHECK(t->reduceFull()->getRepr() == "false");
  it = t->translateFull();
  CHECK(it->getRepr() == "or()");

  theo.constraints.push_back(t);
  theo.addTo(ilp);
  CHECK(ilp.runFullCatchUnsat() == SolveState::INCONSISTENT);
}

TEST_CASE("Finding error in graph coloring") {
  Theory theo;
  xct::ILP ilp(true);
  ilp.init(false, false);

  Functor& border = *theo.voc.createBoolean("border", {Type::STRING, Type::STRING});
  Functor& colortype = *theo.voc.createType("colortype", {"red", "green", "blue"});

  Functor& color = *theo.voc.createFunctor("color", {Type::STRING, Type::STRING}, {"red", "green", "blue"});
  border.setDefault(false);
  border.setInter({"Belgium", "France"}, true);
  border.setInter({"Belgium", "Luxembourg"}, true);
  border.setInter({"Belgium", "Germany"}, true);
  border.setInter({"France", "Germany"}, true);
  border.setInter({"France", "Luxembourg"}, true);
  border.setInter({"Luxembourg", "Germany"}, true);
  border.setInter({"Belgium", "The Netherlands"}, true);
  border.setInter({"Germany", "The Netherlands"}, true);
  Term t = all(
      {"x", "y"}, border,
      O("not", any({"z"}, colortype, O("and", O("=", A(color, V("x")), V("z")), O("=", A(color, V("y")), V("z"))))));
  // TODO: make nested example (without z quantification) after implementing unnested

  theo.constraints.push_back(t);
  theo.addTo(ilp);
  CHECK(ilp.runFullCatchUnsat() == SolveState::INCONSISTENT);

  std::vector<std::string> core =
      xct::aux::comprehension(ilp.getLastCore(), [](xct::IntVar* iv) { return iv->getName(); });
  std::sort(core.begin(), core.end());
  std::stringstream ss;
  ss << core;
  CHECK(ss.str() ==
        "[not any(and(color(\"Belgium\")=z,color(\"France\")=z) for z in colortype)] [not "
        "any(and(color(\"Belgium\")=z,color(\"Germany\")=z) for z in colortype)] [not "
        "any(and(color(\"Belgium\")=z,color(\"Luxembourg\")=z) for z in colortype)] [not "
        "any(and(color(\"France\")=z,color(\"Germany\")=z) for z in colortype)] [not "
        "any(and(color(\"France\")=z,color(\"Luxembourg\")=z) for z in colortype)] [not "
        "any(and(color(\"Germany\")=z,color(\"Luxembourg\")=z) for z in colortype)] ");
  // TODO: core minimization
}