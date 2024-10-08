/**
 * Provides classes for working with concepts relating to the Macaron web framework
 */

import go

private module Macaron {
  private class Context extends Http::ResponseWriter::Range {
    SsaWithFields v;

    Context() {
      this = v.getBaseVariable().getSourceVariable() and
      exists(Method m | m.hasQualifiedName("gopkg.in/macaron.v1", "Context", "Redirect") |
        v.getType().getMethod("Redirect") = m
      )
    }

    override DataFlow::Node getANode() { result = v.similar().getAUse().getASuccessor*() }
  }
}
