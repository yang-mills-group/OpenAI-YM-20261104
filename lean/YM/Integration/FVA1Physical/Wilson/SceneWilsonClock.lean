import YM.Integration.FVA1Physical.Wilson.SceneClockGerm
import YM.Integration.FVA1Physical.Wilson.VaryingAccount
import YM.Integration.FVA1Physical.Wilson.ClockComponents

/-! Relative temperatures and their formal Taylor series from the
actual selected sequence of coupling recalibrations. Only the finitely
many clock entries used by the descent enter any primitive account. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter RG Lattice YM.Wilson Precision RGComparison.Core16 RGComparison.Core16.Descent
open MSbar MSbar.Rolling MSbar.Midpoint MSbar.Bakery Comparison.RG02
open PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FVA2.CityHistory FVA2.CityHistory.Legacy
open PowerSeries
open scoped Classical Topology ContDiff
variable {G : Gauge} {L : Levels G} {H : Horizon L} {Z : ChartRatio G}
    {K : Kin H Z} {N p r k : ℕ} {e : G.Color} (S : Scene L p r)

def relativeSceneClock (m i : ℕ) (g : ℝ) := (resetProduct S i m g)^2
def formalSceneClock (N m i : ℕ) : PowerSeries ℝ :=
  if m+i ≤ N then mk (fun j => jet (relativeSceneClock S m i) j 1) else 1

theorem clock_measures (m : ℕ) (g : ℝ) (i : ℕ) :
    sceneTemperatures S m g i = relativeSceneClock S m i g / g^2 := by
  unfold sceneTemperatures Integral.temperature
  rw [scene_coupling_product,div_pow,inv_div]
  rfl

theorem scene_clock_hot (hS : Realized K N p k r e S) (m i : ℕ) (lo : k ≤ m) (hi : m+i ≤ N) :
    ContDiffAt ℝ ω (relativeSceneClock S m i) 0 := by
  suffices H : ContDiffAt ℝ ω (resetProduct S i m) 0 by exact H.pow 2
  induction i generalizing m with
  | zero => exact contDiffAt_const
  | succ i ih =>
    obtain ⟨_,_,head,_,_⟩ := hS.step m (by omega) lo
    have birth : taste r (S.action m) 0 = 1 := by simpa [taste,Finset.sum_range_succ'] using head
    have hot : ContDiff ℝ ω (taste r (S.action m)) := by unfold taste; fun_prop
    have ht : tiltMap (S.action m) r 0 = 0 := zero_div _
    have smooth : ContDiffAt ℝ ω (tiltMap (S.action m) r) 0 :=
      contDiffAt_id.div hot.contDiffAt (birth.trans_ne one_ne_zero)
    change ContDiffAt ℝ ω (fun g => taste r (S.action m) g *
      resetProduct S i (m+1) (tiltMap (S.action m) r g)) 0
    exact hot.contDiffAt.mul ((ht.symm ▸ ih (m+1) (by omega) (by omega)).comp 0 smooth)

theorem formalScene_sound (hS : Realized K N p k r e S) (m : ℕ) (lo : k ≤ m) :
    SoundZ (formalSceneClock S N m) := by
  intro i
  by_cases hi : m+i ≤ N
  · rw [formalSceneClock,if_pos hi,← coeff_zero_eq_constantCoeff_apply,coeff_mk,jet_zero,
      relativeSceneClock,(scene_product_germ S hS i m lo hi).1,one_pow]
  rw [formalSceneClock,if_neg hi,map_one]

theorem formalScene_rates (hS : Realized K N p k r e S) (m i : ℕ) (lo : k ≤ m) (hi : m+i ≤ N) :
    Aspiration (relativeSceneClock S m i) (term (formalSceneClock S N m i)) := by
  have H := directions ((scene_clock_hot S hS m i lo hi).of_le le_top) (1:ℝ)
  rw [formalSceneClock,if_pos hi]
  convert H using 1
  · funext g; simp
  funext j
  exact coeff_mk ..

theorem scene_account_program (hS : Realized K N p k r e S) (T : Slices L p) {m : ℕ}
    (hm : m ≤ N) (lo : k ≤ m) (h : (traversal T hm).OK G) (t : (traversal T hm).Tags)
    (v : SpaceF G (traversal T hm)) :
    Aspiration (fun g : ℝ => consume (traversal T hm) t (fun i => relativeSceneClock S m i g) (g • v))
      (term (read v (moneyX (traversal T hm) t (formalSceneClock S N m)))) := by
  apply actual_account_coefficients
  · exact h
  intro i hi
  rw [traversal_depth] at hi
  exact formalScene_rates S hS m i lo (by omega)

end YM.Integration.FVA1Physical.Wilson
