#ifndef __TYPE__
#define __TYPE__

#include<vector>
#include<string>
#include<stdexcept>
#include<cassert>
#include<map>
#include<set>

class Type;
class STVar;
class TVar;
class TConst;

class Type {
public:
	Type() = default;
	Type(const int ty, const std::string& name): ty(ty), na(name) {}
	Type(const int ty, const std::string& name,
		const std::vector<Type>& _args) :
		ty(ty), na(name), args(_args) {}

	int type() const;
	std::string name() const;
	std::vector<Type> getArgs() const;
	bool is_fun() const;
	bool is_stvar() const;
	bool is_tvar() const;
	bool is_tconst() const;
	Type domain_type() const;
	Type range_type() const;
	std::pair<std::vector<Type>, Type> strip_type() const;
	int size() const;
	bool operator== (const Type&) const;
	bool operator< (const Type&) const;
	bool operator!= (const Type&) const;
	std::map<std::string, Type> match_incr(Type& t,
		std::map<std::string, Type>) const;
	std::map<std::string, Type> match(Type& t) const;
	std::set<Type> get_stvars() const;
	std::set<Type> get_tvars() const;
	std::set<Type> get_tsubs() const;
	Type convert_stvar() const;
	bool is_numeral_type() const;

private:
	int ty=0;
	std::string na="";
	std::vector<Type> args;
};

class STVar: public Type {
public:
	STVar(const std::string& na): Type(0, na) {}
};

class TVar : public Type {
public:
	TVar(const std::string& na): Type(1, na) {}
};

class TConst : public Type {
public:
	TConst(const std::string& na, 
		const std::vector<Type>& args):
		Type(2, na, args) {}
	TConst(const std::string& na): Type(2, na) {}
};

STVar to_stvar(Type& t);
TVar to_tvar(Type& t);
TConst to_tconst(Type& t);
Type TFun(std::vector<Type>);

TConst BoolType = TConst("bool");
TConst NatType = TConst("nat");
TConst IntType = TConst("int");
TConst RealType = TConst("real");

#endif // !__TYPE__