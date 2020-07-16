#include "term.h"
#include<iostream>

std::string helper(std::shared_ptr<Term> t, std::vector<std::string>& bd_vars) {
	if (t->is_svar()) {
		std::shared_ptr<SVar> svar = std::dynamic_pointer_cast<SVar>(t);
		return "?" + svar->name();
	}
	else if (t->is_var()) {
	 	std::shared_ptr<Var> var = std::dynamic_pointer_cast<Var>(t);
	  	return var->name();
	}
	else if (t->is_const()) {
		std::shared_ptr<Const> c = std::dynamic_pointer_cast<Const>(t);
		return c->name();
	}
	else if (t->is_comb()) {
		std::shared_ptr<Comb> comb = std::dynamic_pointer_cast<Comb>(t);
		std::string str_fun;
		std::string str_arg;
		if (comb->fun()->is_abs()) {
			 str_fun = "(" + helper(comb->fun(), bd_vars) + ")";
		}
		else{
			str_fun = helper(comb->fun(), bd_vars);
		}
		if (comb->get_arg()->is_comb()) {
			std::shared_ptr<Comb> comb_arg = std::dynamic_pointer_cast<Comb>(comb_arg->get_arg());
			str_arg = helper(comb_arg->get_arg(), bd_vars);
		}
		else if (comb->get_arg()->is_abs()) {
			std::shared_ptr<Abs> abs_arg = std::dynamic_pointer_cast<Abs>(comb->get_arg());
			str_arg = helper(abs_arg->get_body(), bd_vars);
		}
		else {
			str_arg = helper(comb->get_arg(), bd_vars);
		}
		return str_fun + " " + str_arg;
	}
	else if (t->is_abs()) {
		std::shared_ptr<Abs> abs = std::dynamic_pointer_cast<Abs>(t);
		bd_vars.push_back(abs->var_name());
		std::string body_str = helper(abs->get_body(), bd_vars);
		return "%" + abs->var_name() + ". " + body_str;
	}
	else if (t->is_bound()) {
		std::shared_ptr<Bound> bound = std::dynamic_pointer_cast<Bound>(t);
		if (bound->get_n() >= bd_vars.size()) {
			return ":B" + std::to_string(bound->get_n());
		}
		else {
			return bd_vars[bound->get_n()];
		}
	}
	else {
		throw std::runtime_error("Bad term.");
	}
}
std::ostream& operator <<(std::ostream& os, SVar& t){
	std::vector<std::string> bd_vars;
	
		auto pt_t = std::make_shared<SVar>(t);
		std::string s = helper(pt_t, bd_vars);
		return os << s;
}

std::ostream& operator <<(std::ostream& os, Var& t) {
	std::vector<std::string> bd_vars;

	auto pt_t = std::make_shared<Var>(t);
	std::string s = helper(pt_t, bd_vars);
	return os << s;
}

std::ostream& operator <<(std::ostream& os, Const& t) {
	std::vector<std::string> bd_vars;

	auto pt_t = std::make_shared<Const>(t);
	std::string s = helper(pt_t, bd_vars);
	return os << s;
}

std::ostream& operator <<(std::ostream& os, Comb& t) {
	std::vector<std::string> bd_vars;

	auto pt_t = std::make_shared<Comb>(t);
	std::string s = helper(pt_t, bd_vars);
	return os << s;
}

std::ostream& operator <<(std::ostream& os, Abs& t) {
	std::vector<std::string> bd_vars;

	auto pt_t = std::make_shared<Abs>(t);
	std::string s = helper(pt_t, bd_vars);
	return os << s;
}
