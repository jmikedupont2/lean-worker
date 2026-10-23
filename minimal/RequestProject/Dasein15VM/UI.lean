import RequestProject.Dasein15VM.UI.Mask
import RequestProject.Dasein15VM.UI.VMObject
import RequestProject.Dasein15VM.UI.Guidance
import RequestProject.Dasein15VM.UI.Proof
import RequestProject.Dasein15VM.UI.Wire
import RequestProject.Dasein15VM.UI.Dasein

/-!
# RFC-0002: Dasein15 VM user interface — proofs and VMs as objects

* `UI.Mask`: observables, the semantic order set `specOrders`, `observedMask` and
  `observedMask_sound` / `observedMask_holds`.
* `UI.VMObject`: `checkVMTrace_complete`, `TraceEntry`, `Badge` (`Badge.sound`, S1), `VMObject`,
  `mkVMObject`, `declareVMObject`.
* `UI.Guidance`: `Verdict`, `compare_verdict`, `compare_notContained_witness`,
  `compare_unknown_unresolved`, `GuidanceEdge`, `runCompare`, `GuidanceEdge.sound`,
  `derived_contained`.
* `UI.Proof`: the proof grammar `ProofTerm` with `ProofTerm.check_sound`, `Evidence.both`, and the
  proof editor `EditorState` (`stepBadge?_isSome_iff`, S2).
* `UI.Wire`: JSON values, `Wire` roundtrip instances, trace/object/edge encoders and decoders
  with roundtrip theorems.
* `UI.Dasein`: the Dasein15 reference objects, `dasein_spectrum`, the kernel-checked
  `contained` / `notContained` edges, and `dasein_roundtrip`.
-/
