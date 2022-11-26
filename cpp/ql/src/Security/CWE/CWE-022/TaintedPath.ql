/**
 * @name Uncontrolled data used in path expression
 * @description Accessing paths influenced by users can allow an
 *              attacker to access unexpected resources.
 * @kind path-problem
 * @problem.severity warning
 * @security-severity 7.5
 * @precision medium
 * @id cpp/path-injection
 * @tags security
 *       external/cwe/cwe-022
 *       external/cwe/cwe-023
 *       external/cwe/cwe-036
 *       external/cwe/cwe-073
 */

import cpp
import semmle.code.cpp.security.FunctionWithWrappers
import semmle.code.cpp.security.Security
import semmle.code.cpp.ir.IR
import semmle.code.cpp.ir.dataflow.TaintTracking
import DataFlow::PathGraph

/**
 * A function for opening a file.
 */
class FileFunction extends FunctionWithWrappers {
  FileFunction() {
    exists(string nme | this.hasGlobalName(nme) |
      nme = ["fopen", "_fopen", "_wfopen", "open", "_open", "_wopen"]
      or
      // create file function on windows
      nme.matches("CreateFile%")
    )
    or
    this.hasQualifiedName("std", "fopen")
    or
    // on any of the fstream classes, or filebuf
    exists(string nme | this.getDeclaringType().hasQualifiedName("std", nme) |
      nme = ["basic_fstream", "basic_ifstream", "basic_ofstream", "basic_filebuf"]
    ) and
    // we look for either the open method or the constructor
    (this.getName() = "open" or this instanceof Constructor)
  }

  // conveniently, all of these functions take the path as the first parameter!
  override predicate interestingArg(int arg) { arg = 0 }
}

Expr asSourceExpr(DataFlow::Node node, int x) {
  result = node.asConvertedExpr() and
  x = 1
  or
  result = node.asDefiningArgument() and
  x = 2
}

Expr asSinkExpr(DataFlow::Node node, int x) {
  result = node.asConvertedExpr() and
  x = 1
  or
  result =
    node.asOperand()
        .(SideEffectOperand)
        .getUse()
        .(ReadSideEffectInstruction)
        .getArgumentDef()
        .getUnconvertedResultExpression() and
  x = 2
}

class TaintedPathConfiguration extends TaintTracking::Configuration {
  TaintedPathConfiguration() { this = "TaintedPathConfiguration" }

  override predicate isSource(DataFlow::Node node) {
    exists(int x |
      isUserInput(asSourceExpr(node, x), _) //and
      // (
      //   x = 1
      //   or
      //   x = 2 and
      //   not exists(DataFlow::Node n2, Expr e | e = asSourceExpr(n2, 1) |
      //     isUserInput(e, _) and e = asSourceExpr(node, 2)
      //   )
      // )
    )
  }

  override predicate isSink(DataFlow::Node node) {
    exists(FileFunction fileFunction |
      exists(int x |
        fileFunction.outermostWrapperFunctionCall(asSinkExpr(node, x), _)// and
        // (
        //   x = 1
        //   or
        //   x = 2 and
        //   not exists(DataFlow::Node n2, Expr e | e = asSinkExpr(n2, 1) |
        //     fileFunction.outermostWrapperFunctionCall(e, _) and e = asSinkExpr(node, 2)
        //   )
        // )
      )
    )
  }
}

predicate simp(TaintedPathConfiguration cfg,
  DataFlow::PathNode sourceNode, DataFlow::PathNode sinkNode) {
exists(DataFlow::PathNode sourceNode2, DataFlow::PathNode sinkNode2, int x, int y, int z, int w|
  cfg.hasFlowPath(sourceNode2, sinkNode2) and
  asSinkExpr(sinkNode.getNode(), x) = asSinkExpr(sinkNode2.getNode(), y) and
  asSourceExpr(sourceNode.getNode(), z) = asSourceExpr(sourceNode2.getNode(), w) and
  (x = 2 and y = 1 or z = 2 and w = 1)
  )
}

from
  FileFunction fileFunction, Expr taintedArg, Expr taintSource, TaintedPathConfiguration cfg,
  DataFlow::PathNode sourceNode, DataFlow::PathNode sinkNode, string taintCause, string callChain
where
  taintedArg = asSinkExpr(sinkNode.getNode(), _) and
  fileFunction.outermostWrapperFunctionCall(taintedArg, callChain) and
  cfg.hasFlowPath(sourceNode, sinkNode) and
  taintSource = asSourceExpr(sourceNode.getNode(), _) and
  isUserInput(taintSource, taintCause) and
  not simp(cfg, sourceNode, sinkNode)
select taintedArg, sourceNode, sinkNode,
  "This argument to a file access function is derived from $@ and then passed to " + callChain + ".",
  taintSource, "user input (" + taintCause + ")"
