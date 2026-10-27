import RequestProject.Dasein15VM.PathObservable.Basic
import RequestProject.Dasein15VM.PathObservable.Observables
import RequestProject.Dasein15VM.PathObservable.Graph
import RequestProject.Dasein15VM.PathObservable.Dasein

/-!
# RFC-0004 revised: path observables and path classes

* `PathObservable.Basic`: certified traces are determined by their endpoints
  (`VMCorrect.unique`); the proposed `stutter`/`swap` rewrites never apply; reversal is never
  certified; shape steps are undone only by routes with 2-cycles.
* `PathObservable.Observables`: `traceLength`, `traceSupport`, `totalVariation`, `traceWinding`,
  `traceEntropy`, with `totalVariation = 2 * (length - 1)` on certified traces.
* `PathObservable.Graph`: the path graph (`Extend`, `Reachable`, `PathGraph`), reachability =
  certified-prefix order, path classes = start states, and which observables descend.
* `PathObservable.Dasein`: the Dasein15 walk as a path, with kernel-computed observables.
-/
