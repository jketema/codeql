// generated by codegen/codegen.py, do not edit
import codeql.swift.elements
import TestUtils

from ThenStmt x, Expr getResult
where
  toBeTested(x) and
  not x.isUnknown() and
  getResult = x.getResult()
select x, "getResult:", getResult
