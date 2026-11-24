import YangMills.WilsonProof.NativeSupport.MatchingSpec
noncomputable section
namespace IssuedBridge.PostedExamTreeSignedFields
open Function Filter Set MeasureTheory YangMills YangMills.Matching
open scoped BigOperators Topology Distributions Classical
variable {g:GaugeGroup}{B:Maxwell.Reference g}{C:WilsonFamily g}{T:Hierarchy C}
structure Signed (M : MSbar.Coefficients B) (S : Conversion B)
    (H : Measurement B T) : Prop where
  correlation (n : ℕ) (d : Fin n → ℕ) : ∃ m : ℕ,
    ∀ (phase : Option T.Character) (v : (i : Fin n) → B.sector (d i)) (o : Spacetime),
      let a : Fin n → Label B := fun i => ⟨d i, v i⟩
      HasExpansion m H.clock (fun s x => T.correlation phase (H.inputs s a)
        (WithLp.toLp 2 fun i => o + s • x i)) (fun k x => S.correlation M k a x)
  ope (n h : ℕ) (d : Fin n → ℕ) : ∃ m : ℕ,
    ∀ (v : (i : Fin n) → B.sector (d i)) (o : Spacetime) (out : B.sector h →ₗ[ℂ] ℂ),
      let a : Fin n → Label B := fun i => ⟨d i, v i⟩
      HasExpansion m H.clock (fun s x => out (H.wilsonOPE s h a o x))
        (fun k x => out (S.ope M h k a x))

theorem original (M:MSbar.Coefficients B)(S:Conversion B)(H:Measurement B T)
    (ordinary:Hierarchy.SeparatedPowerLog T)(nested:Hierarchy.SeparatedNestedPowerLog T):
    Compares M S H ↔ Signed M S H:=by
  constructor
  · intro paid
    exact ⟨paid.correlation,paid.ope⟩
  · intro paid
    exact ⟨paid.correlation,paid.ope,ordinary,nested⟩
end IssuedBridge.PostedExamTreeSignedFields
end
