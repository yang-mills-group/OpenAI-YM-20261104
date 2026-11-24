import YangMills.WilsonProof.NativeSupport.FixedFieldExistence
import YangMills.WilsonProof.NativeSupport.WardStressSeries

set_option autoImplicit false
noncomputable section

namespace YangMills.Matching.CorrelationOnly

open Set Filter
open scoped BigOperators

variable {g : GaugeGroup} {B : Maxwell.Reference g}
variable {C : WilsonFamily g} {T : Hierarchy C}

theorem physicalConservation (H : Measurement B T) (b : Axis) :
    (∑ a : Axis, (WardStress.original H).derivative 4 a (T.stress a b)) = 0 :=
  WardStress.originalConservation H b

theorem physicalTranslation (H : Measurement B T) (phase : Option T.Character)
    {n d : ℕ} (x : Points (n+1)) (hx : x ∈ separated (n+1)) (v : T.Field d)
    (q : Fin n → T.Tag) (χ : Spacetime → ℝ) (window : Ward.Window x χ) (b : Axis) :
    T.translationFlux phase x v q χ b =
      Ward.firstDerivative b (T.correlation phase (Fin.cons ⟨d,v⟩ q)) x :=
  WardStress.originalTranslation H phase x hx v q χ window b

theorem physicalStressLeading (X : T.MaxwellScaling B) (laws : FixedFields.Laws B T X)
    (a b : Axis) :
    FixedFields.Aligned B T X 4 (FixedFields.engineering B T X 4 (T.stress a b))
      (B.stress a b) :=
  laws.stress a b

variable {M N : MSbar.Coefficients B} {S U : Conversion B}
variable (corr : ∀ {n : ℕ} (k : ℕ) (v : Fin n → Label B) (x : Points n),
  S.correlation M k v x = U.correlation N k v x)

include corr

set_option maxHeartbeats 1200000

private theorem insertedAlong (P : WardStress.Series B) {n : ℕ} (k : ℕ)
    (a b : Axis) (v : Fin n → Label B) (x : Points (n+1)) :
    WardStress.inserted M S P k a b v x = WardStress.inserted N U P k a b v x := by
  simp only [WardStress.inserted, corr]

private theorem fluxAlong (P : WardStress.Series B) {n : ℕ} (k : ℕ)
    (v : Fin (n+1) → Label B) (φ : WilsonFamily.SeparatedTest (n+1))
    (χ : Spacetime → ℝ) (a b : Axis) (z : Spacetime × Points (n+1)) :
    WardStress.fluxIntegrand M S P k v φ χ a b z =
      WardStress.fluxIntegrand N U P k v φ χ a b z := by
  simp only [WardStress.fluxIntegrand, insertedAlong corr]

theorem determinedAlongCorrelation (P : WardStress.Series B)
    (paid : WardStress.Determined M S P) : WardStress.Determined N U P := by
  refine ⟨paid.leading, paid.symmetric, paid.signedAxes, ?_, ?_, ?_⟩
  · intro k a b φ
    simpa only [← insertedAlong corr] using paid.vacuum k a b φ
  · intro n k b v φ
    simpa only [← insertedAlong corr] using paid.conservation k b v φ
  · intro n k b v φ χ window
    have flux (a : Axis) : WardStress.fluxIntegrand N U P k v φ χ a b =
        WardStress.fluxIntegrand M S P k v φ χ a b :=
      funext fun z => (fluxAlong corr P k v φ χ a b z).symm
    simpa only [flux, ← corr] using paid.translation k b v φ χ window

theorem comparesAlongCorrelation (H : Measurement B T) (paid : WardStress.Compares M S H) :
    WardStress.Compares N U H := by
  have back : ∀ {n : ℕ} (k : ℕ) (v : Fin n → Label B) (x : Points n),
      U.correlation N k v x = S.correlation M k v x :=
    fun k v x => (corr k v x).symm
  refine ⟨?_, fun P hp => paid.named P (determinedAlongCorrelation back P hp)⟩
  obtain ⟨P, hp, unique⟩ := paid.independent
  exact ⟨P, determinedAlongCorrelation corr P hp,
    fun Q hQ => unique Q (determinedAlongCorrelation back Q hQ)⟩

end YangMills.Matching.CorrelationOnly
end

