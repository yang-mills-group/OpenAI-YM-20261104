import YM.Integration.WilsonOriginalNullRelocation
import YM.Integration.WilsonOriginalNamedRoughRide
import YM.MergeProof.Cashew

/-! Translation covariance of the actual engineering-weighted conditional
Wilson operator, at a coarse site and its genuine fine embedding. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullMovedOperator
open Function MeasureTheory Lattice RG Wilson Extra.Histories Source Labels Relay
open MergeProof MergeProof.Float Motion Trace.Physical.GermGraph
open scoped Classical BigOperators

variable {G:Gauge} {n:Side}

theorem step (o:Site n) (f:Config G n→ℂ) : stepUp (1,false) o f=f ∘ Lattice.translate o := by
  funext U
  change f (pull 1 o U)=f (Lattice.translate o U)
  rw [pull_one]

theorem undo (o:Site n) (f:Config G n→ℂ) :
    (f ∘ Lattice.translate (-o)) ∘ Lattice.translate o = f := by
  funext U
  apply congrArg f
  funext e
  rcases e with ⟨x,axis⟩
  change U ((x+-o)+o,axis)=U (x,axis)
  rw [add_assoc,neg_add_cancel,add_zero]

theorem commute (C:Family G) (d N p i:ℕ) (o:Site (C.side i p))
    (f:Config G (C.side (i+1) p)→ℂ) (hi:Integrable f (prior G _)) :
    transition (C:=C) d N p i (f ∘ Lattice.translate ((C.path.levels.clock.op i p).ratio.embed o)) =
      (transition (C:=C) d N p i f) ∘ Lattice.translate o := by
  have h:=MergeProof.unison (1,false) C.path i N p d o f hi
  rw [step,step] at h
  exact h

end YM.Integration.WilsonOriginalNullMovedOperator
