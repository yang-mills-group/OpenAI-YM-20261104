import YM.Integration.WilsonThermometerUnitFilingWeakRoom
import YM.Pert.Bulk.Crossing

/-! Coarsening at the actual source root, with all current-cell offsets and every repeated line. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingWeakRibbon
open Function Finset Lattice Laurent Bloch Metric Exterior Precision RG Next.Free Work.F08 Stationary FormalBulk08 Flat
open WilsonThermometerUnitFilingWeakKernel
open scoped Classical BigOperators
variable {I J:Type*} [Fintype J]

theorem moved (L:Side)(x z:Cover):
    (size (rent L z-rent L x):ℝ)≤8+(size (z-x):ℝ)/(L.val:ℝ):=by
  have close (v:Cover):Pert.Bulk.delta L v (rent L v)≤4:=by
    simpa only [Pert.Bulk.sep_self,zero_add] using Pert.Bulk.mixed_sep (L:=L) v (rent L v)
  have h:=Pert.Bulk.inv_scaled L z (rent L z) x (rent L x)
  unfold Pert.Bulk.sep at h
  exact h.trans (by linarith only [close x,close z])

theorem length (L:Side) {s w:ℝ}(sp:0≤s)(shrink:s/(L.val:ℝ)≤w)(x z d:Cover):
    s*(size (rent L z+d-rent L x):ℝ) ≤ 8*s+w*(size (z-x):ℝ)+s*(size d:ℝ):=by
  have trans: (size (rent L z+d-rent L x):ℝ)≤(size (rent L z-rent L x):ℝ)+(size d:ℝ):=by
    rw [show rent L z+d-rent L x=(rent L z-rent L x)+d by abel]
    exact_mod_cast size_add (rent L z-rent L x) d
  have below:=mul_le_mul_of_nonneg_left (moved L x z) sp
  have body:=mul_le_mul_of_nonneg_right shrink (show 0≤(size (z-x):ℝ) by positivity)
  calc _≤s*((size (rent L z-rent L x):ℝ)+(size d:ℝ)):=mul_le_mul_of_nonneg_left trans sp
       _≤_:=by rw [mul_add] at below ⊢; ring_nf at below body ⊢;linarith

def old (w:ℝ)(r:ℕ)(x:Cover)(place:Fin r→Cover):ℝ:=∏a:Fin r,Real.exp (w*size (place a-x))

def shifted (L:Side) (s:ℝ)(A:Bloch.Row I J)(z x:Cover)(key:I)(b:Cover×J):ℝ:=
  Real.exp (s*size (rent L z+b.1-rent L x))*‖A key b.2 b.1‖

def after (L:Side)(s:ℝ)(A:Bloch.Row I J){r:ℕ}(x:Cover)(place:Fin r→Cover)
    (key:Fin r→I)(box:Fin r→Finset Cover):ℝ:=
  ∑d∈Fintype.piFinset (fun a=>(box a) ×ˢ (univ:Finset J)),∏a:Fin r,shifted L s A (place a) x (key a) (d a)

theorem original (L:Side) {s w b:ℝ}(sp:0≤s)(shrink:s/(L.val:ℝ)≤w)(A:Bloch.Row I J)
    (h:A.strip s b)(floor:Real.exp (8*s)*cash A b≤1) {r:ℕ}(x:Cover)(place:Fin r→Cover)
    (key:Fin r→I)(box:Fin r→Finset Cover):after L s A x place key box≤old w r x place:=by
  rw [after,←prod_univ_sum,old]
  apply prod_le_prod
  · exact fun a _=>sum_nonneg fun ξ _=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  intro a _
  let K:=Real.exp (w*size (place a-x))
  have test (d:Cover×J):shifted L s A (place a) x (key a) d≤K*Real.exp (8*s)*parcel A s (key a) d:=by
    have h₁:=Real.exp_le_exp.mpr (length L sp shrink x (place a) d.1)
    rw [Real.exp_add,Real.exp_add] at h₁
    unfold shifted parcel
    dsimp only [K]
    exact (mul_le_mul_of_nonneg_right h₁ (norm_nonneg _)).trans_eq (by ring)
  calc _ ≤ ∑d∈(box a) ×ˢ (univ:Finset J),K*Real.exp (8*s)*parcel A s (key a) d:=sum_le_sum fun d _=>test d
       _ = K*Real.exp (8*s)*(∑d∈(box a) ×ˢ (univ:Finset J), parcel A s (key a) d):=by rw [mul_sum]
       _ ≤ K*Real.exp (8*s)*cash A b:=mul_le_mul_of_nonneg_left (bond A h (key a) (box a)) (by dsimp [K];positivity)
       _ ≤ K*1:=by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left floor (Real.exp_pos _).le
       _ = _:=mul_one _

end YM.Integration.WilsonThermometerUnitFilingWeakRibbon
