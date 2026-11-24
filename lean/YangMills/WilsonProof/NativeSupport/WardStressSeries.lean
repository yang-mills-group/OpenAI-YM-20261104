import YangMills.PerturbativeMatching.WardIdentities
import YangMills.WilsonProof.NativeSupport.MatchingSpec

/-! The named physical stress on the commissioned measurement. Its independent
coordinate is fixed by the separated conservation and translation equations
for the converted MS correlations, including the translation sign. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.Matching.WardStress
open Function Filter Set MeasureTheory
open scoped Topology BigOperators Classical

variable {g : GaugeGroup} {B : Maxwell.Reference g}
variable {C : WilsonFamily g} {T : Hierarchy C}


/-- The Ward action already aligning the measured frame acts on the original
hierarchy. Both physical identities below use its named tensor. -/
def original (H : Measurement B T) : T.StressWardLaws := H.frameAxes.choose

theorem originalConservation (H : Measurement B T) (b : Axis) :
    (∑ a : Axis, (original H).derivative 4 a (T.stress a b)) = 0 :=
  (original H).divergence b

theorem originalTranslation (H : Measurement B T) (phase : Option T.Character) {n d : ℕ}
    (x : Points (n+1)) (hx : x ∈ separated (n+1)) (v : T.Field d) (q : Fin n → T.Tag)
    (χ : Spacetime → ℝ) (window : Ward.Window x χ) (b : Axis) :
    T.translationFlux phase x v q χ b =
      Ward.firstDerivative b (T.correlation phase (Fin.cons ⟨d, v⟩ q)) x :=
  (original H).translation phase x hx v q χ window b




/-- Full coordinate of the literal scaled stress in the measured frame.
Testing every complex dual includes the vacuum component. At every fixed
grade these coordinates can be substituted in every occupied multilinear
slot. The OPE output remains in the inverse frame of Measurement.wilsonOPE
and uses the inverse conversion of Conversion.ope. -/
def Named (H : Measurement B T) (P : Series B) : Prop :=
  ∀ (a b : Axis) (N : ℕ) (out : B.sector 4 →ₗ[ℂ] ℂ),
    Tendsto (fun s : ℝ =>
      (out ((H.frame s 4).symm ((s : ℂ)^4 • T.stress a b)) -
        ∑ j : Fin (N+1), (H.clock s : ℂ)^j.val * out (P j.val a b)) /
          (H.clock s : ℂ)^N) (𝓝[>] 0) (𝓝 0)

/-- The independent Ward equations have a unique solution before any measured
values enter. The same hierarchy carries the exact physical Ward laws and
the same measurement realizes that solution in its physical coordinate. -/
structure Compares (M : MSbar.Coefficients B) (S : Conversion B) (H : Measurement B T) : Prop where
  independent : ∃! P : Series B, Determined M S P
  named : ∀ P : Series B, Determined M S P → Named H P

end YangMills.Matching.WardStress
end
