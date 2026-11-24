import YM.Integration.WilsonThermometerReverseWard
import YM.Push.STRESS_FLUX.Restore

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardFile
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Labels Source Push
open Extraction RG12 RG17 Climb Trace.Pilot MergeProof Next.Extract PhysicalNext.Repeat.Legato
open XSpace XSpace.Rose Cells Push.GridApprox OPE OPE.Orbits
open WilsonPositionThermometerCapStation WilsonOffsetReportingProducts WilsonOffsetEquationLaw
open WilsonAddressedEquationShelf PhysicalNext.Repeat Legato Bandage
open scoped Classical Topology BigOperators

variable {G : Gauge} {n : Side}

private theorem inside_sub {K : Set (Site n)} {f g : Config G n → ℂ}
    (hf : Interior K f) (hg : Interior K g) : Interior K (f-g) := by
  change Interior K (fun U => f U - g U)
  simpa [sub_eq_add_neg] using hf.plus (hg.scale (-1))

/-- Keep one literal counterterm on both sides of every reflected copy. -/
theorem same_counterterm (T : Tiling n) (β : ℝ) {A B C : Config G n → ℂ}
    (ha : Interior (T.chamber 0) A) (hb : Interior (T.chamber 0) B)
    (hc : Interior (T.chamber 0) C)
    (ward : ∀ X : Config G n → ℂ, Interior (T.chamber 0)ᶜ X →
      moment β (fun U => A U * X U) = moment β (fun U => B U * X U)) :
    T.rootTest β (A-C) = T.rootTest β (B-C) := by
  apply StressFlux.restore_root T β (inside_sub ha hc) (inside_sub hb hc)
  intro X hX
  have fun_eq : (fun U => ((A-C) U-(B-C) U)*X U) =
      (fun U => A U * X U) - (fun U => B U * X U) := by
    funext U
    simp only [Pi.sub_apply]
    ring
  rw [fun_eq]
  change ∫ U, (A U * X U - B U * X U) ∂law G n β = 0
  have xa := (ha.enlarges (subset_univ _)).times (hX.enlarges (subset_univ _))
  have xb := (hb.enlarges (subset_univ _)).times (hX.enlarges (subset_univ _))
  rw [integral_sub (xa.integrable β) (xb.integrable β)]
  exact sub_eq_zero.mpr (ward X hX)

variable (R : Run G)
variable (V : ∀ d, SectionData (R.family.labels.level d)) (W : Mark.Weave G)
  (P : ∀ d, (ℕ×ℕ) → (R.family.label d ≃ₗ[ℂ] R.family.label d)) (b : Presentation R.family)
  (portfolio : ∀ d, Mark.Portfolio R.family.params (V d) (W d))
  (issued : Hearthside R.family V W P b (Bandage.fly R.alloy.B.a))

include W portfolio issued in
/-- The cutoff threshold is chosen at the child arity before the period and number of cells. -/
theorem original : ∃ radius : ℕ → ℕ,
    ∀ (I : Type) [Fintype I] (d : I → ℕ), ∀ᶠ N : ℕ in atTop,
    ∀ (p : ℕ) (T : Tiling (R.family.side N p)) (x : (i : I) → R.family.label (d i))
    (o : I → Site (R.family.side N p)) (C : Config G (R.family.side N p) → ℂ),
    Avoids V radius d o →
    (∀ i, (T.chamber 0)ᶜ ⊆ Mark.Outer (radius (d i)) (o i)) →
    (∀ i (z : R.family.label (d i)), Interior (T.chamber 0) (R.family.O N p z (o i))) →
    (∀ i, (↑((V (d i)).footprint (o i)) : Set _) ⊆ T.chamber 0) →
    Interior (T.chamber 0) C →
    T.rootTest (R.family.beta N p) ((fun U =>
      ∏ i, R.family.O N p (b.step (d i) (N,p) (x i)) (o i) U) - C) =
    T.rootTest (R.family.beta N p) ((fun U => ∏ i, (R.family.O N p (x i) (o i) U -
      residual R.family (V (d i)) N p (P (d i) (N,p))
         (x i-b.step (d i) (N,p) (x i)) (o i) U)) - C) := by
  obtain ⟨rad,erase⟩ := WilsonThermometerReverseWard.projected R V W P b portfolio issued
  refine ⟨rad, fun I _ d => ?_⟩
  filter_upwards [erase I d] with N atN
  intro p T x o C apart guarded raw footprint counter
  refine same_counterterm T (R.family.beta N p) ?_ ?_ counter ?_
  · exact Interior.combines _ univ (fun i _ => raw i _)
  · apply Interior.combines _ univ
    intro i _
    let z := x i-b.step (d i) (N,p) (x i)
    have h := incoming_continuous (V (d i)) N p (P (d i) (N,p)) z (o i)
    have placed : Interior (T.chamber 0) (incoming R.family (V (d i)) N p (P (d i) (N,p)) z (o i)) := by
      refine ⟨?_, h.measurable, ?_, (Mark.cont_envelope h).cost⟩
      · intro k U
        simp only [incoming, initial, Pi.smul_apply]
        rw [(V (d i)).placed_invariant (portfolio (d i)).valid _ _ k U]
      · intro U U' agreed
        exact incoming_local _ _ _ _ _ _ U U' (agrees_mono agreed (footprint i))
    exact inside_sub (raw i _) (inside_sub (raw i z) placed)
  · intro X ext
    exact atN p x o X apart (fun i U Z agreed => ext.localSites U Z
      (agrees_mono agreed (guarded i))) ⟨ext.borel, ext.cost⟩

end YM.Integration.WilsonCapturedPrimaryWardFile
