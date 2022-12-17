grammar expanded_sec:security;


attribute funSecCtx, isSecure, levels occurs on Function;

synthesized attribute startSec::SecurityLevel occurs on Function;
synthesized attribute retSec::SecurityLevel occurs on Function;

aspect production fun
top::Function ::= funName::String retTy::Type retName::String
                  params::Params body::C
{
  top.startSec = public();
  top.retSec = public();
  top.levels = params.levels;

  body.secCtx = params.secCtx_out;
  body.funSecCtx = top.funSecCtx;
  body.pc = public();

  top.isSecure = body.isSecure;
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

  top.wellTyped = body.wellTyped;
  --
  top.startSec = startSec;
  top.retSec = retSec;
  top.levels = params.levels;

  body.secCtx = params.secCtx_out;
  body.funSecCtx = top.funSecCtx;
  body.pc = startSec;

  top.isSecure = body.isSecure;
  --
  forwards to fun(funName, retTy, retName, params, body);
}




attribute secCtx_out, levels occurs on Params;

aspect production endParams
top::Params ::=
{
  top.secCtx_out = [];
  top.levels = [];
}


aspect production addParams
top::Params ::= name::String type::Type rest::Params
{
  top.secCtx_out = (name, public())::rest.secCtx_out;
  top.levels = public()::rest.levels;
}


abstract production secureParams
top::Params ::= name::String type::Type sec::SecurityLevel rest::Params
{
  top.tyCtx_out = (name, type)::rest.tyCtx_out;
  top.names = name::rest.names;
  top.tys = type::rest.tys;
  --
  top.secCtx_out = (name, sec)::rest.secCtx_out;
  top.levels = sec::rest.levels;
  --
  forwards to addParams(name, type, rest);
}




attribute funSecCtx, funSecCtx_out, isSecure occurs on Program;

aspect production endProgram
top::Program ::=
{
  top.funSecCtx_out = [];
  top.isSecure = true;
}


aspect production addProgram
top::Program ::= f::Function rest::Program
{
  f.funSecCtx = top.funSecCtx;
  rest.funSecCtx = top.funSecCtx;

  top.funSecCtx_out =
      (f.funName, f.startSec, f.retSec, f.levels)::rest.funSecCtx_out;
  top.isSecure = f.isSecure && rest.isSecure;
}





--I think we might want funSecCtx_out for proofs to get the security
--information for the main function
attribute isSecure, funSecCtx_out occurs on Root;

aspect production root
top::Root ::= p::Program
{
  p.funSecCtx = p.funSecCtx_out;
  top.funSecCtx_out = p.funSecCtx_out;
  top.isSecure = p.isSecure;
}
