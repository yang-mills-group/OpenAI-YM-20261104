import YM.Integration.WilsonGraphCenteredFarHeaterRate
import YM.Integration.WilsonGraphCenteredFarHighFieldCrop
import YM.Integration.WilsonGraphCenteredFarScalarRecomposition

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedBentHeater
open Filter Real PowerSeries Growth Continuation
open Register MS MS.Book MS.Land Scale
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Enh O.Score O.Canon Dframe Jury
open MS.Native MS.Menus MS.Tide MS.Book.Program
open YangMills YM.Answer.ContinuumLimit YM.Integration
open scoped Topology BigOperators Classical

universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)
private abbrev Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev Q := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev θ := ElectedMeasurement.clock
  (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)) (Z g hg)

/-- The elected far reading is approximated by the scalar clock at the requested crop,
with the high-order chart used only to prove the error on the same radius. -/
theorem original (p : ℕ) {C B : ℝ} (hC : 0 < C) (hB : 0 < B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ a : ℕ, ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ s ≥ 0,
      exp s ≤ C*(gYM g.core r)^(-B) →
      let t := θ.{u} g hg periods strict r
      let v := θ.{u} g hg periods strict (r*exp s)
      let ψ := GroupS.ψ (Z g hg).criterion (Q.{u} g hg).MS (Teller.logNu 1) (-s)
      ‖(v:ℂ)-Appointed220.Eval.value p ψ (t:ℂ)‖ ≤ D*(gYM g.core r)^(p+1)*(1+s)^a ∧
        ‖Appointed220.Eval.value p ψ (t:ℂ)‖≤1 ∧ |t|≤1 ∧ |t|≤2*gYM g.core r ∧ 0≤gYM g.core r := by
  let N := Z g hg
  let M := (Q.{u} g hg).MS
  let law := ((Q.{u} g hg).matching.dilation (Teller.logNu 1)).check
  let simple := _root_.IssuedMaxwell.ElectedPrescription.simple g hg
  obtain ⟨k,paired,hpk⟩ := ((AppointedCenteredWindow.paid.{u} g hg periods strict 0 (p+1) hC hB).and
    (eventually_ge_atTop p)).exists
  obtain ⟨L,hL,a,clock⟩ := Appointed220.Zones.clock_log law k
  obtain ⟨K,hK⟩ := exists_nat_gt B
  have running : Tendsto (gYM g.core) (𝓝[>] (0:ℝ)) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨shrink simple,positive_g simple⟩
  have edges := running.eventually (G1.Wire.move C B hK hC)
  have heating := paid_reading simple (θ.{u} g hg periods strict)
    (AppointedPhysicalWindowAndPhase.electedClock.{u} g hg periods strict)
  have locations := running.eventually (Appointed220.Zones.Budget.location law K p (δ:=1/2) (by norm_num))
  refine ⟨1+2^(p+1)*L,by positivity,a,?_⟩
  filter_upwards [paired,heating,edges,locations,running.eventually (Ioc_mem_nhdsGT (by norm_num : (0:ℝ)<1/4))]
    with r pairedAt heatAt edgeAt locate small s hs upper
  intro t v ψ
  let x := gYM g.core r
  have hx : 0<x := small.1
  have quarter : x≤1/4 := small.2
  have cap : x≤1 := by linarith
  have nt : |t|≤2*x := heatAt.2.2.2
  have ht : |t|≤1 := by linarith
  have near : ‖(t:ℂ)‖≤2*x := by simpa only [Complex.norm_real,Real.norm_eq_abs] using nt
  have edge := edgeAt (exp s) (Real.one_le_exp_iff.mpr hs) upper
  have located := locate (exp s) edge (t:ℂ) near
  rw [Appointed220.Zones.Budget.eta,Real.log_exp] at located
  have half : ‖Appointed220.Eval.value p ψ (t:ℂ)‖≤1/2 := located
  refine ⟨?_,by linarith,ht,nt,hx.le⟩
  have high : ‖(v:ℂ)-Appointed220.Eval.value k ψ (t:ℂ)‖≤x^(p+2) :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans (pairedAt s hs upper).1
  have high1 := high.trans (pow_le_pow_of_le_one hx.le cap (show p+1≤p+2 by omega))
  have tail := AppointedHighFieldCrop.tail hpk t ψ ht
  rw [AppointedScalarRecomposition.value,AppointedScalarRecomposition.value] at tail
  have tp : |t|^(p+1)≤2^(p+1)*x^(p+1) := by simpa only [mul_pow] using pow_le_pow_left₀ (abs_nonneg t) nt (p+1)
  have qmass : AppointedScalarOverflow.mass k ψ≤L*(1+s)^a := by simpa only [AppointedScalarOverflow.mass,Appointed220.Eval.mass,abs_neg,abs_of_nonneg hs] using clock (-s)
  have remainder := tail.trans (mul_le_mul tp qmass (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (mul_nonneg (by positivity) (pow_nonneg hx.le _)))
  have one := mul_le_mul_of_nonneg_left (one_le_pow₀ (le_add_of_nonneg_right hs) (n:=a)) (pow_nonneg hx.le (p+1))
  rw [mul_one] at one
  have triangle := dist_triangle (v:ℂ) (Appointed220.Eval.value k ψ (t:ℂ)) (Appointed220.Eval.value p ψ (t:ℂ))
  simp only [dist_eq_norm] at triangle
  exact triangle.trans ((add_le_add (high1.trans one) remainder).trans_eq (by ring))

end YM.FVA2.GradedFar.AppointedBentHeater
