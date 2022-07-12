import cpp

from Variable v
where v.getName() = "is_same_v"
select v,
  concat(int index, string res | res = v.getTemplateArgument(index).toString() + "[" + index + "]" | res, ","  order by index),
  count(v.getInitializer().getExpr())
