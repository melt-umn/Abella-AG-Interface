grammar expanded_sec:host;


nonterminal Function with
   funName, retTy, retName, params, body,
   funTyCtx, wellTyped;

synthesized attribute funName::String;
synthesized attribute retTy::Type;
synthesized attribute retName::String;
synthesized attribute params::Params;
synthesized attribute body::C;

abstract production fun
top::Function ::= funName::String retTy::Type retName::String
                  params::Params body::C
{
  top.funName = funName;
  top.retTy = retTy;
  top.retName = retName;
  top.params = params;
  top.body = body;

  body.tyCtx = (retName, retTy)::params.tyCtx_out;
  body.funTyCtx = top.funTyCtx;

  top.wellTyped = body.wellTyped;
}




nonterminal Params with names, tys, tyCtx_out;

synthesized attribute names::[String];

abstract production endParams
top::Params ::=
{
  top.tyCtx_out = [];

  top.names = [];

  top.tys = [];
}


abstract production addParams
top::Params ::= name::String type::Type rest::Params
{
  top.tyCtx_out = (name, type)::rest.tyCtx_out;

  top.names = name::rest.names;

  top.tys = type::rest.tys;
}




nonterminal Program with
   wellTyped, funTyCtx_out, funTyCtx,
   funEvalCtx, mainArgs, printedOutput;

abstract production endProgram
top::Program ::=
{
  --check that the main function exists
  local mainTy::Type = lookupFunTy("main", top.funTyCtx).1;
  top.wellTyped = mainTy.isIntTy || !mainTy.isIntTy;

  top.funTyCtx_out = [];

  local mainFound::(String, [String], C) =
        lookupFunEval("main", top.funEvalCtx);
  local body::C = mainFound.3;
  body.funEvalCtx = top.funEvalCtx;
  body.evalCtx = buildEvalCtx(mainFound.2, top.mainArgs);

  top.printedOutput = body.printedOutput;
}


abstract production addProgram
top::Program ::= f::Function rest::Program
{
  top.wellTyped = f.wellTyped && rest.wellTyped;

  top.funTyCtx_out =
      (f.funName, f.retTy, f.params)::rest.funTyCtx_out;

  f.funTyCtx = top.funTyCtx;
  rest.funTyCtx = top.funTyCtx;

  rest.mainArgs = top.mainArgs;

  local p::Params = f.params;
  rest.funEvalCtx =
       (f.funName, f.retName, p.names, f.body)::top.funEvalCtx;

  top.printedOutput = rest.printedOutput;
}





nonterminal Root with wellTyped, printedOutput, mainArgs;

abstract production root
top::Root ::= p::Program
{
  p.funTyCtx = p.funTyCtx_out;
  top.wellTyped = p.wellTyped;

  p.funEvalCtx = [];
  p.mainArgs = top.mainArgs;
  top.printedOutput = p.printedOutput;
}
