grammar expanded_sec:list;

imports expanded_sec:host;

abstract production nilExpr
top::Expr ::= ty::Type --we don't have type inference, so needs a type
{
  top.vars = [];
  --
  top.ty = listTy(ty);
  --
  top.value = nilVal();
  --
  forwards to recBuild(addRecFieldExprs("null", etrue(),
                                        endRecFieldExprs()));
}


abstract production consExpr
top::Expr ::= hd::Expr tl::Expr
{
  top.vars = hd.vars ++ tl.vars;
  --
  local tlTy::Type = tl.ty;
  top.ty = if tysEq(hd.ty, tlTy.listContents)
           then tlTy
           else error("Must be a list");
  --
  top.value = consVal(hd.value, tl.value);
  --
  forwards to recBuild(addRecFieldExprs("null", efalse(),
                       addRecFieldExprs("head", hd,
                       addRecFieldExprs("tail", tl,
                       endRecFieldExprs()))));
}


abstract production nullExpr
top::Expr ::= e::Expr
{
  top.vars = e.vars;
  --
  local ety::Type = e.ty;
  top.ty = if ety.isListTy then boolTy() else error("Must be a list");
  --
  local ev::Value = e.value;
  top.value = if ev.isNullList then trueVal() else falseVal();
  --
  forwards to e;
}


abstract production headExpr
top::Expr ::= e::Expr
{
  top.vars = e.vars;
  --
  local ety::Type = e.ty;
  top.ty = ety.listContents;
  --
  local ev::Value = e.value;
  top.value = ev.listHead;
  --
  forwards to e;
}


abstract production tailExpr
top::Expr ::= e::Expr
{
  top.vars = e.vars;
  --
  local ety::Type = e.ty;
  top.ty = if ety.isListTy then ety else error("Must be a list");
  --
  local ev::Value = e.value;
  top.value = ev.listTail;
  --
  forwards to e;
}


abstract production indexExpr
top::Expr ::= lst::Expr idx::Expr
{
  top.vars = lst.vars ++ idx.vars;
  --
  local lstTy::Type = lst.ty;
  local idxTy::Type = idx.ty;
  top.ty = if idxTy.isIntTy
           then lstTy.listContents
           else error("Must be an int");
  --
  local iv::Value = idx.value;
  local lv::Value = lst.value;
  lv.idx = iv.intValNum;
  top.value = lv.listIndex;
  --
  forwards to plus(lengthExpr(lst), idx);
}


abstract production lengthExpr
top::Expr ::= e::Expr
{
  top.vars = e.vars;
  --
  local ety::Type = e.ty;
  top.ty = if ety.isListTy then intTy() else error("Must be a list");
  --
  local ev::Value = e.value;
  top.value = intVal(ev.listLen);
  --
  forwards to e;
}





synthesized attribute isNullList::Boolean occurs on Value;
synthesized attribute listHead::Value occurs on Value;
synthesized attribute listTail::Value occurs on Value;
--special operations on lists
synthesized attribute listLen::Integer occurs on Value;
inherited attribute idx::Integer occurs on Value;
synthesized attribute listIndex::Value occurs on Value;

abstract production nilVal
top::Value ::=
{
  top.intValNum = error("Not an integer value");
  top.isTrueVal = error("Not a Boolean value");
  top.isFalseVal = error("Not a Boolean value");
  top.recValFields = error("Not a record value");
  --
  top.isNullList = true;
  top.listHead = error("Null list");
  top.listTail = error("Null list");
  top.listLen = 0;
  top.listIndex = error("Reached null list");
  --
  forwards to recVal([("null", trueVal())]);
}


abstract production consVal
top::Value ::= hd::Value tl::Value
{
  top.intValNum = error("Not an integer value");
  top.isTrueVal = error("Not a Boolean value");
  top.isFalseVal = error("Not a Boolean value");
  top.recValFields = error("Not a record value");
  --
  top.isNullList = false;
  top.listHead = hd;
  top.listTail = tl;
  top.listLen = 1 + tl.listLen;
  tl.idx = top.idx - 1;
  top.listIndex = if top.idx == 0 then hd else tl.listIndex;
  --
  forwards to
     recVal([("head", hd), ("tail", tl), ("null", falseVal())]);
}


aspect production intVal
top::Value ::= i::Integer
{
  top.isNullList = error("Not a list value");
  top.listHead = error("Not a list value");
  top.listTail = error("Not a list value");
  top.listLen = error("Not a list value");
  top.listIndex = error("Not a list value");
}


aspect production trueVal
top::Value ::=
{
  top.isNullList = error("Not a list value");
  top.listHead = error("Not a list value");
  top.listTail = error("Not a list value");
  top.listLen = error("Not a list value");
  top.listIndex = error("Not a list value");
}


aspect production falseVal
top::Value ::=
{
  top.isNullList = error("Not a list value");
  top.listHead = error("Not a list value");
  top.listTail = error("Not a list value");
  top.listLen = error("Not a list value");
  top.listIndex = error("Not a list value");
}


aspect production recVal
top::Value ::= contents::[(String, Value)]
{
  top.isNullList = error("Not a list value");
  top.listHead = error("Not a list value");
  top.listTail = error("Not a list value");
  top.listLen = error("Not a list value");
  top.listIndex = error("Not a list value");
}





synthesized attribute isListTy::Boolean occurs on Type;
synthesized attribute listContents::Type occurs on Type;

abstract production listTy
top::Type ::= ty::Type
{
  top.isIntTy = false;
  top.isBoolTy = false;
  top.isRecTy = false;
  top.recTyFields = error("Not a record type");
  --
  top.isListTy = true;
  top.listContents = ty;
  --
  local comp::Type = top.compareTy;
  ty.compareTy = comp.listContents;
  top.isTyEqual = comp.isListTy && ty.isTyEqual;
  --
  forwards to recTy([("null", boolTy())]);
}


aspect production intTy
top::Type ::=
{
  top.isListTy = false;
  top.listContents = error("Not a list type");
}


aspect production boolTy
top::Type ::=
{
  top.isListTy = false;
  top.listContents = error("Not a list type");
}


aspect production recTy
top::Type ::= contents::[(String, Type)]
{
  top.isListTy = false;
  top.listContents = error("Not a list type");
}
