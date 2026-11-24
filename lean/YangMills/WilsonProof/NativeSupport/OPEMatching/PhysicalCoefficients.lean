import YangMills.WilsonProof.NativeSupport.CorrelationMatching.Measurements

/-! The coefficients and output fields in the continuum hierarchy's OPE. -/

set_option autoImplicit false
noncomputable section

namespace YangMills.OPEMatching

open scoped BigOperators Classical

variable {g : GaugeGroup} {C : WilsonFamily g} {T : Hierarchy C}
  {B : Maxwell.Reference g}

/-- Fuse the measured inputs at radius `r` and express their physical output
through dimension `h` in the same measured frame. Each coefficient multiplies
the field that represents its channel in the hierarchy's OPE. -/
def physicalOutput (H : CorrelationMatching.Measurement B T) {n : ℕ} (r : ℝ)
    (h : ℕ) (fields : Fin n → Matching.Label B) (center : Spacetime)
    (x : Points n) : B.sector h :=
  (H.frame r h).symm
    (∑ d : Fin (h + 1), ∑ channel : T.Channel d.val,
      T.coefficient (H.inputs r fields) d.val channel (fun i => center + r • x i) center •
        H.includeField (Nat.le_of_lt_succ d.isLt) (T.actor d.val channel))

/-- The coefficients are multilinear functions of the physical input fields.
Their channels, included from the dimensions where they first occur, form a
basis through each finite output dimension. -/
structure PhysicalCoefficients (H : CorrelationMatching.Measurement B T) : Prop where
  multilinear {I : Type} [Fintype I] (degrees : I → ℕ)
      (w : ℕ) (channel : T.Channel w) (x : I → Spacetime)
      (distinct : Function.Injective x) (center : Spacetime) :
    ∃ form : MultilinearMap ℂ (fun i => T.Field (degrees i)) ℂ,
      ∀ v, T.coefficient (fun i => ⟨degrees i, v i⟩) w channel x center = form v
  /-- A common translation, a relabeling of the slots, and a change of
  filtration degree presenting the same field preserve the coefficient. -/
  sameInputs {I J : Type} [Fintype I] [Fintype J] (slots : J ≃ I)
      (a : I → T.Tag) (b : J → T.Tag) (x : I → Spacetime)
      (distinct : Function.Injective x) (center shift : Spacetime)
      (sameField : ∀ j, T.toLabel (b j).1 (b j).2 =
        T.toLabel (a (slots j)).1 (a (slots j)).2)
      (w : ℕ) (channel : T.Channel w) :
    T.coefficient b w channel (fun j => x (slots j) + shift) (center + shift) =
      T.coefficient a w channel x center
  channelBasis (h : ℕ) :
    ∃ basis : Module.Basis (Σ d : Fin (h + 1), T.Channel d.val) ℂ (T.Field h),
      ∀ (d : Fin (h + 1)) (channel : T.Channel d.val),
        basis ⟨d, channel⟩ =
          H.includeField (Nat.le_of_lt_succ d.isLt) (T.actor d.val channel)

end YangMills.OPEMatching
