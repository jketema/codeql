private import codeql.swift.generated.stmt.YieldStmt

module Impl {
  class YieldStmt extends Generated::YieldStmt {
    override string toStringImpl() { result = "yield ..." }
  }
}
