import YM.PertExtension.MeshIntegral

/-! Changing-origin uniformly weighted averages from arbitrary center choices. -/
set_option autoImplicit false
set_option maxHeartbeats 560000
noncomputable section
namespace YM.PertExtension.LatticePT.Grid
open MeasureTheory Filter Set Finset Function Metric Lattice
open scoped NNReal Topology Classical BigOperators
variable {q:ℕ+}{V:ℕ→Type*}{s : ∀ m,Finset (V m)}{f:∀ m,V m→ℝ}{x:ℝ}
local notation "reg"=> (Filter.atTop:Filter ℕ)
lemma average_paths (hn:∀m,(s m).Nonempty)
 (H:∀ (u : (m:ℕ) → V m), (∀ m,u m∈s m) → Tendsto (fun m=>f m (u m)) reg (𝓝 x)) : Tendsto (fun m=>((s m).card:ℝ)⁻¹* ∑ i∈s m,f m i) reg (𝓝 x):=by
  let d(m):ℝ:=(s m).card
  have hp m : 0<d m :=Nat.cast_pos.mpr (card_pos.mpr (hn _))
  choose u hu hS using fun m=> (s m).exists_mem_eq_sup (α:=ℝ≥0) (hn m) (fun i=> ‖f m i-x‖₊)
  have h:= (H u hu).sub_const x |>.norm;rw [sub_self,norm_zero] at h
  let z(m):= (d m)⁻¹*∑ i∈s m,f m i
  have hz(m): ‖z m-x‖ ≤ ‖f m (u m)-x‖ := by
     unfold z; rw [show _*_-x = (d m)⁻¹ * ∑ i∈s m,(f m i-x) from ?_]
     · rw [norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr (hp m).le)]
       exact le_trans (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (fun i hi => show ‖f m i-x‖≤‖f m (u m)-x‖ from NNReal.coe_le_coe.mpr ((le_sup (s:=s m) (f:=fun i=> ‖f m i-x‖₊) hi).trans_eq (hS m)))) ) (inv_nonneg.mpr (hp m).le)) (by
           rw [sum_const,nsmul_eq_mul]; unfold d;field_simp; exact le_rfl)
     rw [sum_sub_distrib,sum_const,nsmul_eq_mul, mul_sub,show (d m)⁻¹ * ((s m).card*x)=x by rw [← mul_assoc,show (d m)⁻¹*(s m).card=1 from inv_mul_cancel₀ (hp m).ne',one_mul]]
  rw [tendsto_iff_dist_tendsto_zero];exact squeeze_zero (fun _=>dist_nonneg) (by simpa [dist_eq_norm,z,d] using hz) h
end YM.PertExtension.LatticePT.Grid
