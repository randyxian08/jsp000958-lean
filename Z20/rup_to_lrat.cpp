// Untrusted certificate elaborator: every produced LRAT step is replayed in
// Python and subsequently reconstructed as a Lean kernel proof term.
#include <algorithm>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>

struct Checker {
  int vars;
  std::vector<std::vector<int>> db, watches;
  std::vector<int> units, empty, values, queue;
  explicit Checker(int n) : vars(n), db(1), watches(2*(n+2)), values(n+1,-1) {}
  int index(int l) const { return 2*std::abs(l)+(l<0); }
  int value(int l) const {
    int v=values[std::abs(l)]; return v<0 ? -1 : int(v==(l>0));
  }
  void assign(int l) {
    if (value(l)==0) throw std::runtime_error("inconsistent enqueue");
    if (value(l)<0) { values[std::abs(l)]=(l>0); queue.push_back(l); }
  }
  int add(const std::vector<int>& c) {
    int id=int(db.size()); db.push_back(c);
    if (c.empty()) empty.push_back(id);
    else if (c.size()==1) units.push_back(id);
    else { watches[index(c[0])].push_back(id); watches[index(c[1])].push_back(id); }
    return id;
  }
  bool rup(const std::vector<int>& c, std::vector<int>& hints) {
    std::fill(values.begin(),values.end(),-1); queue.clear(); hints.clear();
    for (int l:c) {
      if (value(-l)==0) return true;
      assign(-l);
    }
    if (!empty.empty()) { hints.push_back(empty[0]); return true; }
    for (int id:units) {
      int l=db[id][0], v=value(l);
      if (v==0) { hints.push_back(id); return true; }
      if (v<0) { hints.push_back(id); assign(l); }
    }
    for (size_t q=0;q<queue.size();++q) {
      int falsified=-queue[q];
      auto& ws=watches[index(falsified)];
      size_t j=0;
      while (j<ws.size()) {
        int id=ws[j]; auto& clause=db[id];
        if (clause[0]!=falsified) {
          if (clause[1]!=falsified) throw std::runtime_error("bad watch invariant");
          std::swap(clause[0],clause[1]);
        }
        int other=clause[1];
        if (value(other)==1) { ++j; continue; }
        size_t k=2;
        while (k<clause.size() && value(clause[k])==0) ++k;
        if (k<clause.size()) {
          std::swap(clause[0],clause[k]);
          ws[j]=ws.back(); ws.pop_back();
          watches[index(clause[0])].push_back(id);
        } else {
          hints.push_back(id);
          if (value(other)==0) return true;
          assign(other); ++j;
        }
      }
    }
    return false;
  }
};

static std::vector<int> read_clause(std::istringstream& in,int vars) {
  std::vector<int> c; int x; bool ended=false;
  while (in>>x) {
    if (x==0) { ended=true; break; }
    if (std::abs(x)>vars) throw std::runtime_error("out-of-range literal");
    c.push_back(x);
  }
  if (!ended) throw std::runtime_error("unterminated clause");
  return c;
}

int main(int argc,char** argv) {
  try {
    if (argc!=4) throw std::runtime_error("usage: rup_to_lrat INPUT.cnf INPUT.drup OUTPUT.lrat");
    std::ifstream cnf(argv[1]), proof(argv[2]); std::ofstream out(argv[3]);
    if (!cnf || !proof || !out) throw std::runtime_error("cannot open file");
    std::string line, p, tag; int vars=-1, nc=-1;
    while (std::getline(cnf,line)) {
      if (line.empty() || line[0]=='c') continue;
      std::istringstream in(line);
      if (!(in>>p>>tag>>vars>>nc) || p!="p" || tag!="cnf" || vars<0 || nc<1)
        throw std::runtime_error("bad CNF header");
      break;
    }
    if (vars<0) throw std::runtime_error("missing CNF header");
    Checker check(vars); int read=0;
    while (std::getline(cnf,line)) {
      if (line.empty() || line[0]=='c') continue;
      std::istringstream in(line);
      check.add(read_clause(in,vars)); ++read;
    }
    if (read!=nc) throw std::runtime_error("CNF clause-count mismatch");
    size_t steps=0, skipped=0; bool finished=false;
    auto emit=[&](const std::vector<int>& c) {
      std::unordered_set<int> set(c.begin(),c.end());
      for (int l:c) if (set.count(-l)) { ++skipped; return; }
      std::vector<int> hints;
      if (!check.rup(c,hints)) throw std::runtime_error("non-RUP step "+std::to_string(steps+1));
      int id=check.add(c);
      out<<id<<' '; for (int l:c) out<<l<<' '; out<<"0 ";
      for (int h:hints) out<<h<<' '; out<<"0\n";
      ++steps; if (c.empty()) finished=true;
    };
    while (!finished && std::getline(proof,line)) {
      if (line.empty() || line[0]=='d' || line[0]=='c') continue;
      std::istringstream in(line); emit(read_clause(in,vars));
    }
    if (!finished) emit({});
    if (!finished) throw std::runtime_error("missing contradiction");
    std::cout<<"RUP_ELABORATED steps="<<steps<<" tautologies_ignored="<<skipped<<"\n";
    return 0;
  } catch (const std::exception& e) {
    std::cerr<<"RUP_REJECTED: "<<e.what()<<"\n"; return 1;
  }
}
