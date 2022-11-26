import semmle.code.cpp.commons.File
import semmle.code.cpp.ir.dataflow.DataFlow

/** Holds if there exists a call to a function that might close the file specified by `e`. */
predicate closed(Expr e) {
  fcloseCall(_, e) or
  exists(ExprCall c |
    // cautiously assume that any ExprCall could be a call to fclose.
    c.getAnArgument() = e
  )
}

private class FopenCallMayBeClosedConfiguration extends DataFlow::Configuration {
  FopenCallMayBeClosedConfiguration() { this = "FopenCallMayBeClosedConfiguration" }

  override predicate isSource(DataFlow::Node node) { fopenCall(node.asConvertedExpr()) }

  override predicate isSink(DataFlow::Node node) { closed(node.asConvertedExpr()) }
}

/**
 * Holds if `fc` is a call to a function that opens a file that might be closed. For example:
 * ```
 * FILE* f = fopen("file.txt", "r");
 * ...
 * fclose(f);
 * ```
 */
predicate fopenCallMayBeClosed(FunctionCall fc) {
  exists(FopenCallMayBeClosedConfiguration cfg, DataFlow::Node source, DataFlow::Node sink |
    cfg.hasFlow(source, sink) and
    source.asExpr() = fc
  )
}
