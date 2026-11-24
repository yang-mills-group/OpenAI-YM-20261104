import YM.Integration.WilsonMatrixOriginalSignedPanel
import YM.Integration.WilsonInvariantActionDoubleAdmission

/-! Transport the signed two-field covariance through the original varying reporting coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalFiledCovariance
open Filter Function Set MeasureTheory Table Spec Climb Lattice RG Wilson RG17 Marker
open Next.UVStress PhysicalNext.Repeat.Legato Extraction Extraction.Order Push.GridApprox
open OPE OPE.Orbits OPE.Therm WilsonInvariantActionIntegratedPair WilsonInvariantActionPairMarginals
open WilsonMatrixOriginalRealFields WilsonMatrixOriginalSignedReading
open private tags recorded from YM.Integration.WilsonInvariantActionIntegratedPair
open private pair from YM.Integration.WilsonInvariantActionAdmittedPair
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) {U : Filter (ℕ × ℕ)} [U.NeBot] (covered : U ≤ f.fuse)

include F covered in
private theorem one (A : ℕ × ℕ → R.family.label 4) (a : R.family.label 4)
    (ha : Tendsto A U (𝓝 a)) :
    Tendsto (fun z : ℕ × ℕ => WilsonInvariantActionPairMarginals.single R (A z)
      (0 : Site (R.family.side z.1 z.2))) U (𝓝 (expectation S 4 (S.project 4 a))) := by
  let E : Fin 1 → Type := fun _ => R.family.label 4
  let M (z : ℕ × ℕ) := R.family.ensemble (N:=z.1) (p:=z.2) (fun _ : Fin 1 => 4) (fun _ => 0)
  let v (x : ∀ i,E i) := expectation S 4 (S.project 4 (x 0))
  have fixed (x : ∀ i,E i) : Tendsto (fun z => M z x) U (𝓝 (v x)) := by
    have h := (along (WilsonMatrixOriginalPolarReadout.single_read F (x 0))).mono_left covered
    have same : (fun _ : Fin 1 => x 0) = x := funext fun i => congrArg x (Subsingleton.elim _ _)
    change Tendsto (fun z : ℕ × ℕ => M z (fun _ => x 0)) U (𝓝 (v x)) at h
    rwa [same] at h
  exact tendsto_multi (ι:=Fin 1) E M v fixed (fun _ => a) (fun z _ => A z) (fun _ => ha)

include F covered in
private theorem two (A B : ℕ × ℕ → R.family.label 4) (a b : R.family.label 4)
    (ha : Tendsto A U (𝓝 a)) (hb : Tendsto B U (𝓝 b)) (t : Test 2) :
    Tendsto (fun z : ℕ × ℕ => smears R.family z.1 z.2 (tags R (A z) (B z)) t) U
      (𝓝 (S.integralOn (fun _ : Fin 2 => 4) (pair a b) t)) := by
  have each (i : Fin 2) : Tendsto (fun z => pair (A z) (B z) i) U (𝓝 (pair a b i)) := by
    fin_cases i
    · exact ha
    · exact hb
  exact calibrated_smear (v:=fun z => pair (A z) (B z)) (x:=pair a b) F.room.ordered U covered t each

include F covered in
private theorem reading (cut : (N p : ℕ) → Fin (N+1)) (t : Test 2)
    (A B : ℕ × ℕ → R.family.label 4) (a b : R.family.label 4)
    (ha : Tendsto A U (𝓝 a)) (hb : Tendsto B U (𝓝 b)) :
    Tendsto (fun z : ℕ × ℕ => profile R cut (A z) (B z) t z.1 z.2) U
      (𝓝 (S.integralOn (fun _ : Fin 2 => 4) (pair a b) t -
        expectation S 4 (S.project 4 a) *
          S.integralOn (fun _ : Fin 2 => 4) (pair (R.family.refUnit 4) b) t)) := by
  have mass := two F covered A B a b ha hb t
  have unit := two F covered (fun _ => R.family.refUnit 4) B _ b tendsto_const_nhds hb t
  apply (mass.sub ((one F covered A a ha).mul unit)).congr'
  filter_upwards [((Cards.largeMesh f).eventually_ge_atTop (R.family.ref 4)).filter_mono covered] with z hz
  exact (recorded R cut _ _ t hz).symm

include F covered in
theorem moving (cut : (N p : ℕ) → Fin (N+1)) (t : Test 2)
    (A B : ℕ × ℕ → R.family.label 4) (a b : R.family.label 4)
    (ha : Tendsto A U (𝓝 a)) (hb : Tendsto B U (𝓝 b)) :
    Tendsto (fun z : ℕ × ℕ =>
      profile R cut (A z) (B z) t z.1 z.2 - profile R cut a b t z.1 z.2) U (𝓝 0) := by
  have entries := reading F covered cut t A B a b ha hb
  have fixed := reading F covered cut t (fun _ => a) (fun _ => b) a b tendsto_const_nhds tendsto_const_nhds
  simpa only [sub_self] using! entries.sub fixed

variable (L : Layout F) (chosen : U ≤ L.lens)
include F chosen in
theorem filed (cut : (N p : ℕ) → Fin (N+1)) (φ : Test 2) {r : ℝ} (hr : 0 < r)
    (real_test : ∀ x, dilate hr φ x = (((dilate hr φ x).re : ℝ) : ℂ))
    (live : R.family.ref 4 ≤ L.level r) (a b : R.family.label 4) (χ : ℂ →L[ℝ] ℝ)
    (real_action : centering S 4 (S.project 4 (realLabel (R:=R)
      (S.representative 4 (master L 4 r a)))) = centering S 4 (master L 4 r a)) :
    Tendsto (fun z : ℕ × ℕ => signed R (atRef L 4 r z a) (atRef L 4 r z b) χ
      (dilate hr φ) z.1 z.2) U (𝓝 (χ (WilsonInvariantActionPairCovariance.tested
        (master L 4 r a) (master L 4 r b) r φ))) := by
  let A := fun z => realLabel (R:=R) (atRef L 4 r z a)
  let B := fun z => atRef L 4 r z b
  let a₀ := realLabel (R:=R) (locatedRef L 4 r a)
  let b₀ := locatedRef L 4 r b
  have real_cont : Continuous (fun w : R.family.label 4 => realLabel (R:=R) w) := by
    unfold realLabel
    fun_prop
  have ha : Tendsto A U (𝓝 a₀) := (real_cont.tendsto _).comp
    (tendsRef (L:=L) (D:=4) (r:=r) chosen tendsto_const_nhds live)
  have hb : Tendsto B U (𝓝 b₀) := tendsRef (L:=L) (D:=4) (r:=r) chosen tendsto_const_nhds live
  have base := (along (WilsonMatrixOriginalPolarReadout.ordered F cut φ hr a₀ b₀)).mono_left
    (chosen.trans L.certified)
  have same : centering S 4 (S.project 4 a₀) = centering S 4 (master L 4 r a) := by
    dsimp only [a₀]
    rw [WilsonMatrixOriginalActionReality.projected F,payRef]
    rw [WilsonMatrixOriginalActionReality.projected F,S.rep] at real_action
    exact real_action
  have change := moving F (chosen.trans L.certified) cut (dilate hr φ) A B a₀ b₀ ha hb
  have all := change.add base
  simp only [sub_add_cancel,zero_add] at all
  have equality : WilsonInvariantActionPairCovariance.tested (S.project 4 a₀) (S.project 4 b₀) r φ =
      WilsonInvariantActionPairCovariance.tested (master L 4 r a) (master L 4 r b) r φ := by
    unfold WilsonInvariantActionPairCovariance.tested WilsonInvariantActionPairCovariance.covariance
    simp only [same,b₀,payRef]
  rw [equality] at all
  apply ((χ.continuous.tendsto _).comp all).congr'
  filter_upwards [((Cards.largeMesh f).eventually_ge_atTop (R.family.ref 4)).filter_mono
    (chosen.trans L.certified)] with z hz
  exact measured R cut _ _ χ _ real_test hz

end YM.Integration.WilsonMatrixOriginalFiledCovariance
