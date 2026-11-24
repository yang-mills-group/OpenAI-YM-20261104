import YM.Integration.FVA1Physical.Wilson.SceneHistory

/-! The actual truncated coupling resets of a selected RG scene have unit
relative inverse-temperature at the bare endpoint. The individual higher
orders of its recalibrations are unrestricted. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter Function RG Lattice YM.Wilson Precision RGComparison.Core16
open MSbar MSbar.Rolling MSbar.Midpoint MSbar.Bakery Comparison.RG02
open scoped Classical Topology
variable {G : Gauge} {L : Levels G} {H : Horizon L} {Z : ChartRatio G}
    {K : Kin H Z} {N p k r : ℕ} {e : G.Color} (S : Scene L p r)

def resetProduct : ℕ → ℕ → ℝ → ℝ
  | 0,_,_ => 1
  | i+1,m,g => taste r (S.action m) g * resetProduct i (m+1) (tiltMap (S.action m) r g)

theorem scene_coupling_product (i m : ℕ) (g : ℝ) :
    sceneCoupling S i m g = g / resetProduct S i m g := by
  induction i generalizing m g with
  | zero => simp [sceneCoupling,resetProduct]
  | succ i ih => rw [sceneCoupling,ih,resetProduct,tiltMap,div_div]

private theorem taste_at_zero (s : PowerSeries ℝ) : taste r s 0 = PowerSeries.coeff 0 s := by
  simp [taste,Finset.sum_range_succ']

theorem scene_product_germ (hS : Realized K N p k r e S) (i m : ℕ)
    (lo : k ≤ m) (hi : m+i ≤ N) :
    resetProduct S i m 0 = 1 ∧ ContinuousAt (resetProduct S i m) 0 := by
  induction i generalizing m with
  | zero => exact ⟨rfl,continuousAt_const⟩
  | succ i ih =>
    obtain ⟨_,_,head,_,_⟩ := hS.step m (by omega) lo
    have birth : taste r (S.action m) 0 = 1 := (taste_at_zero _).trans head
    have cont : Continuous (taste r (S.action m)) := by unfold taste; fun_prop
    have ht : tiltMap (S.action m) r 0 = 0 := zero_div _
    have smooth : ContinuousAt (tiltMap (S.action m) r) 0 :=
      continuousAt_id.div cont.continuousAt (birth.trans_ne one_ne_zero)
    obtain ⟨prior,good⟩ := ih (m+1) (by omega) (by omega)
    refine ⟨by rw [resetProduct,birth,ht,prior,one_mul],?_⟩
    change ContinuousAt (fun g => taste r (S.action m) g *
      resetProduct S i (m+1) (tiltMap (S.action m) r g)) 0
    exact cont.continuousAt.mul ((ht.symm ▸ good).comp smooth)

theorem scene_temperature_leading (hS : Realized K N p k r e S) (i m : ℕ)
    (lo : k ≤ m) (hi : m+i ≤ N) :
    Tendsto (fun g : ℝ => g^2 * sceneTemperatures S m g i) PertExtension.Series.Tested.germ (𝓝 1) := by
  obtain ⟨birth,cont⟩ := scene_product_germ S hS i m lo hi
  have H := (cont.pow 2).tendsto.mono_left
    (show PertExtension.Series.Tested.germ ≤ 𝓝 (0:ℝ) from nhdsWithin_le_nhds)
  change Tendsto (fun g : ℝ => (resetProduct S i m g)^2) _ (𝓝 ((resetProduct S i m 0)^2)) at H
  rw [birth,one_pow] at H
  apply H.congr'
  filter_upwards [PertExtension.Series.Tested.eventually_pos] with g hg
  unfold sceneTemperatures Integral.temperature
  rw [scene_coupling_product,div_pow,inv_div]
  field_simp [hg.ne']

end YM.Integration.FVA1Physical.Wilson
