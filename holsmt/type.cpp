#include<iostream>
#include<numeric>
#include "type.h"

std::ostream& operator << (std::ostream& os, const Type& t) {
	if (t.type() == 0) {
		return os << "?'" << t.name();
	}
	else if (t.type() == 1) {
		return os << "'" << t.name();
	}
	else if (t.type() == 2) {
		std::vector<Type> args = t.getArgs();
		if (args.size() == 0) {
			return os << t.name();
		}
		else if (args.size() == 1) {
			if (args[0].is_fun()) {
				return os << "(" << args[0] << ") " << t.name();
			}
			else {
				return os << args[0] << " " << t.name();
			}
		}
		else if (t.is_fun()) {
			if (args[0].is_fun()) {
				return os << "(" << args[0] << ") => " << args[1];
			}
			else {
				return  os << args[0] << " => " << args[1];
			}
		}
		else {
			os << "(";
			for (auto s : args) {
				if (s == args.back()) {
					os << s <<") ";
				}
				else {
					os << s << ", ";
				}
			}
			return os << t.name();
		}
	}
}

inline std::string Type::name() const {
	return na;
}

inline std::vector<Type> Type::getArgs() const {
	if (ty == 2) {
		return args;
	}
	else {
		throw std::runtime_error("Type error.");
	}
}

inline int Type::type() const {
	return ty;
}

inline bool Type::is_stvar() const {
	return ty == 0;
}

inline bool Type::is_tvar() const {
	return ty == 1;
}

inline bool Type::is_tconst() const {
	return ty == 2;
}

inline bool Type::is_fun() const {
	return ty == 2 && na == "fun";
}

inline Type Type::domain_type() const{
	assert(this->is_fun());
	return args[0];
}

inline Type Type::range_type() const{
	assert(this->is_fun());
	return args[1];
}

std::pair<std::vector<Type>, Type> Type::strip_type() const{
	if(this->is_fun()){
		std::pair<std::vector<Type>, Type> p = this->range_type().strip_type();
		
		std::vector<Type> domain_ty = {this->domain_type()};

		domain_ty.insert(domain_ty.end(), p.first.begin(), p.first.end());

		std::pair<std::vector<Type>, Type> v_new = {domain_ty, p.second};

		return v_new;
	}else{
		std::vector<Type> v;
		std::pair<std::vector<Type>, Type> p = {v, *this};
		return p;
	}
}

int Type::size() const {
	if(this->is_stvar() || this->is_tvar()){
		return 1;
	}
	else if(this->is_tconst()){
		int n = 1;
		for(auto a : args){
			n += a.size();
		}
		return n;
	}
	else{
		throw std::runtime_error("Type error");
	}
}

Type subst(Type& t, std::map<STVar, Type>& s) {
	if(t.is_stvar()){
		STVar st = to_stvar(t);
		if(s.find(st) != s.end()){
			return s[st];
		}else{
			return t;
		}
	}else if(t.is_tvar()){
		return t;
	}else if(t.is_tconst()){
		std::vector<Type> v_args;
		for(auto a : t.getArgs()){
			Type ta = subst(a, s);
			v_args.push_back(ta);
		}
		return TConst(t.name(), v_args);
	}
}

bool Type::operator==(const Type& t) const{
	if (this == &t) {
		return true;
	}
	if(ty != t.type())	{
		return false;
	}
	else if (ty == 0 || ty == 1) {
		return na == t.name();
	}
	else if (ty == 2) {
		return na == t.name() && args == t.getArgs();
	}
	else {
		throw std::runtime_error("Bad type.");
	}
}

bool Type::operator<(const Type& t) const{
	if(ty != t.type()){
		return ty < t.type();
	}else if(ty == 0 || ty == 1){
		return na < t.name();
	}else if(ty == 2){
		if(na > t.name()){
			return false;
		}
		else if(na < t.name())
		{
			return true;
		}
		else
		{
			return this->size() < t.size(); //incorrect. 
		}
	}
}

bool Type::operator!=(const Type& t) const {
	return !(*this == t);
}

inline STVar to_stvar(Type& t){
	assert(t.type() == 0);
	return STVar(t.name());
}

inline TVar to_tvar(Type& t){
	assert(t.type() == 1);
	return TVar(t.name());
}

inline TConst to_tconst(Type& t){
	assert(t.type() == 2);
	return TConst(t.name(), t.getArgs());
}

std::map<std::string, Type> Type::match_incr
	(Type& t, std::map<std::string, Type> m) const {
	if (this->is_stvar()) {
		if (m.find(this->name()) != m.end()) {
			if (t != m[this->name()]) {
				throw std::runtime_error("Match error");
			}
		}
		else {
			m.insert({ this->name(), t });
			return m;
		}
	}
	else if (this->is_tvar()) {
		if (*this != t) {
			throw std::runtime_error("Match error");
			return m;
		}
	}
	else if (this->is_tconst()) {
		if (!t.is_tconst() || t.name() != na) {
			throw std::runtime_error("Match error");
		}
		else {
			for (int i = 0; i < args.size(); ++i) {
				m =args[i].match_incr(t.getArgs()[i], m);
			}
			return m;
		}
	}
}

std::map<std::string, Type> Type::match(Type& t) const {
	std::map<std::string, Type> m;
	m = match_incr(t, m);
	return m;
}



int main() {
	STVar st("a");
	std::cout << st << std::endl;
	TVar tv("b");
	std::cout << tv << std::endl;
	TConst bo("bool");
	TConst nat("nat");
	std::cout << bo << std::endl;
	std::vector<Type> v1{nat, bo};
	TConst fun = TConst("fun", v1);
	std::cout << fun << std::endl;
	std::cout << fun.domain_type() << " "<< fun.range_type() << std::endl;
	std::vector<Type> v2{ nat };
	TConst nat_list("list", v2);
	std::cout << nat_list << std::endl;
	std::vector<Type> v3{nat, fun };
	TConst nat_nat_bo("fun", v3);
	std::cout << nat_nat_bo << std::endl;
	std::cout << nat_nat_bo.range_type() << std::endl;
	std::cout << nat_nat_bo.size() << std::endl;
	std::cout << nat_nat_bo.strip_type().second << std::endl;
	for (auto& s : nat_nat_bo.strip_type().first) {
		std::cout << s << " ";
	}
	std::cout << std::endl;
	
	STVar b("b");
	std::map<STVar, Type> m = { {STVar("a"), TConst("bool")}, {STVar("b"), TConst("nat")} };
	std::vector<Type> v4{ st, b };
	TConst f4("fun", v4);
	std::cout << f4 << std::endl;
	std::cout << subst(f4, m) <<std::endl;
	std::map<std::string, Type> m1 = st.match(bo);
	for (auto it = m1.cbegin(); it != m1.cend(); ++it)
	{
		std::cout << it->first << ":=" << it->second << "\n";
	}
	STVar a("a");
	std::vector<Type> v5{ a, b };
	TConst p("fun", v5);
	std::map<std::string, Type> m2 = p.match(fun);
	for (auto it = m2.cbegin(); it != m2.cend(); ++it)
	{
		std::cout << it->first << ":=" << it->second << "\n";
	}
	
	return 0;
}