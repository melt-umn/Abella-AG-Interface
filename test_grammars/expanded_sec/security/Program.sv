grammar expanded_sec:security;

aspect production fun
top::Function ::= funName::String retTy::Type retName::String
                  params::Params body::C
{

}


abstract production secfun
top::Function ::= funName::String startSec::SecurityLevel
                  retTy::Type retSec::SecurityLevel retName::String
                  params::Params body::C
{
  top.funName = funName;
  top.retTy = retTy;
  top.retName = retName;
  top.params = params;
  top.body = body;
  --
  body.tyCtx = (retName, retTy)::params.tyCtx_out;
  body.funTyCtx = top.funTyCtx;
  --
  top.wellTyped = body.wellTyped;
  --
  forwards to fun(funName, retTy, retName, params, body);
}




aspect production endParams
top::Params ::=
{

}


aspect production addParams
top::Params ::= name::String type::Type rest::Params
{

}


abstract production secureParams
top::Params ::= name::String type::Type sec::SecurityLevel rest::Params
{
  top.tyCtx_out = (name, type)::rest.tyCtx_out;
  top.names = name::rest.names;
  top.tys = type::rest.tys;
  --
  forwards to addParams(name, type, rest);
}




aspect production endProgram
top::Program ::=
{

}


aspect production addProgram
top::Program ::= f::Function rest::Program
{

}





aspect production root
top::Root ::= p::Program
{

}
