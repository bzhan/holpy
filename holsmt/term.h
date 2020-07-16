#ifndef __TERM__
#define __TERM__
#include "type.h"
#include<memory>

class Term {
public:
	Term(int _ty): ty(_ty) {}
	int type() const { return ty; }
	virtual bool is_svar() const { return ty == SVAR; }
	bool is_var() const { return ty == VAR; }
	bool is_const() const { return ty == CONST; }
	bool is_comb() const { return ty == COMB; }
	bool is_abs() const { return ty == ABS; }
	bool is_bound() const { return ty == BOUND; }
	virtual int size() const = 0;
protected:
	const int SVAR = 0;
	const int VAR = 1;
	const int CONST = 2;
	const int COMB = 3;
	const int ABS = 4;
	const int BOUND = 5;
	friend bool operator==(const Term&, const Term&);
	virtual bool isEqual(const Term& A) const { return ty == A.type(); }
private:
	int ty;
};

bool operator==(const Term& A, const Term& B) {
	return typeid(A) == typeid(B) && A.isEqual(B);
}

bool operator!=(const Term& A, const Term& B) {
	return !(A == B);
}

class SVar : public Term {
public:
	SVar(const std::string& _na, const Type& _t): Term(0), na(_na), t(_t) {}
	std::string name() const { return na; }
	Type T() const { return t; }
	virtual int size() const override { return 1; }
protected:
	virtual bool isEqual(const Term& obj) const override{
		auto v = dynamic_cast<const SVar&>(obj);
		return Term::isEqual(obj) && na == v.name() &&v.T() == t;
	}
private:
	std::string na;
	Type t;
};

class Var : public Term {
public:
	Var(const std::string& _na, const Type& _t) : Term(1), na(_na), t(_t) {}
	std::string name() const { return na; }
	Type T() const { return t; }
	virtual int size() const override { return 1; }
protected:
	virtual bool isEqual(const Term& obj) const override {
		auto v = dynamic_cast<const Var&>(obj);
		return Term::isEqual(obj) && na == v.name() && v.T() == t;
	}
private:
	std::string na;
	Type t;
};

class Const : public Term {
public:
	Const(const std::string& _na, const Type& _t) : Term(2), na(_na), t(_t) {}
	std::string name() const { return na; }
	Type T() const { return t; }
	virtual int size() const override { return 1; }
protected:
	virtual bool isEqual(const Term& obj) const override {
		auto v = dynamic_cast<const Const&>(obj);
		return Term::isEqual(obj) && na == v.name() && v.T() == t;
	}
private:
	std::string na;
	Type t;
};

class Comb : public Term {
public:
	Comb(std::shared_ptr<Term> _fun, std::shared_ptr<Term> _arg): Term(3), f(_fun), arg(_arg) {}
	std::shared_ptr<Term> fun() const { return f; }
	std::shared_ptr<Term> get_arg() const { return arg; }
	virtual int size() const override { return 1 + f->size() + arg->size(); }
protected:
	virtual bool isEqual(const Term& obj) const override {
		auto v = dynamic_cast<const Comb&>(obj);
		return Term::isEqual(obj) && *f == *(v.fun()) && *arg == *(v.get_arg());
	}
private:
	std::shared_ptr<Term> f;
	std::shared_ptr<Term> arg;
};

class Abs : public Term {
public:
	Abs(const std::string& _var_na, Type _T, std::shared_ptr<Term> _body): Term(4), var_na(_var_na), 
		t(_T), body(_body) {}
	std::string var_name() const { return var_na; }
	Type T() const { return t; }
	std::shared_ptr<Term> get_body() const { return body; }
	virtual int size() const override { return 1 + body->size(); }
protected:
	virtual bool isEqual(const Term& obj) const override {
		auto v = dynamic_cast<const Abs&>(obj);
		return Term::isEqual(obj) && t == v.T() && *body == *(v.get_body());
	}
private:
	std::string var_na;
	Type t;
	std::shared_ptr<Term> body;
};

class Bound : public Term {
public:
	Bound(int _n): Term(5), n(_n) {}
	int get_n() const { return n; }
	virtual int size() const override { return 1; }
protected:
	virtual bool isEqual(const Term& obj) const override {
		auto v = dynamic_cast<const Bound&>(obj);
		return Term::isEqual(obj) && n == v.get_n();
	}
private:
	int n;
};

#endif // !__TERM__
