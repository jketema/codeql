---
category: minorAnalysis
---
* The JavaScript extractor will on longer report syntax errors related to "strict mode".
  Files containing such errors are now being fully analyzed along with other sources files.
  This improves our support for source files that technically break the "strict mode" rules,
  but where a build steps transforms the code such that it ends up working at runtime.
