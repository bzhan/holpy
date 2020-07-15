#ifndef __TYPE__
#define __TYPE__

#include<vector>
#include<string>
#include<memory>
#include<stdexcept>
#include<cassert>
#include<map>

class Type {
public:
	Type() = default;
	Type(const int ty, const std::string& name): ty(ty), na(name) {}
	Type(const int ty, const std::string& name,
		const std::vector<std::shared_ptr<Type>>& args):
		ty(ty), na(name), args(args) {}

	int type() const;
	std::string name() const;
	std::vector<std::shared_ptr<Type>> getArgs() const;
	bool is_fun() const;
	bool is_stvar() const;
	bool is_tvar() const;
	bool is_tconst() const;
	std::shared_ptr<Type> domain_type() const;
	std::shared_ptr<Type> range_type() const;
	std::pair<std::vector<std::shared_ptr<Type>>, 
		std::shared_ptr<Type>> strip_type() const;
	int size() const;
	bool operator== (const Type&) const;
	bool operator< (const Type&) const;

private:
	int ty=0;
	std::string na="";
	std::vector<std::shared_ptr<Type>> args;
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
		const std::vector<std::shared_ptr<Type>>& args):
		Type(2, na, args) {}
	TConst(const std::string& na): Type(2, na) {}
};

STVar to_stvar(Type& t);
TVar to_tvar(Type& t);
TConst to_tconst(Type& t);

#endif // !__TYPE__