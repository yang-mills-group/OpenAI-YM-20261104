import YM.Contacts.Lintel.Plata
namespace YM.Contacts.Lintel
set_option linter.unusedSectionVars false
set_option quotPrecheck false
open Function Set Finset Filter Metric RG Wilson Lattice Precision Exterior MeasureTheory
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F05
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open PertExtension.Chart Radial
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{c f m: Side}{α:ℕ→Type}{n k:ℕ}
namespace Plata
open Crag Steam Lumen Resetter Ion Angle Convoy
namespace Shelf
-- uniform thermal bound at all densities without costing n exponential log penalty
variable (G:Gauge){Y:House (Lines G m 1)}{i j k n:ℕ}
local notation "B" => Lines G m 1
local notation "S" => Site m
private abbrev tailwind (x:B)(p:S) (a: TypeFace 1)(z:G.ColorIndex): ℂ:= if x.2=(a,z) then (cell x.1 p)⁻¹ else 0
private lemma cell_norm (x p:S) : ‖cell x p‖=1:= by
    unfold cell; exact mode_real _ _ (real_frequency _)
private lemma tailwind_bound (x:B)(p:S) (a z): ‖tailwind G x p a z‖≤1:= by unfold tailwind; split; simp [cell_norm]; simp
private def torque (x:B)(p:S):Link G m:= (arm G m 1).symm (Precision.wave p (tailwind G x p))
private lemma torque_read (x:B)(p:S)(t:B): torque G x p t= if x.2=t.2 then ((cell t.1 p)*(cell x.1 p)⁻¹).re else 0:= by
    rcases t with ⟨i,a,b⟩; rw [← arm_apply G m 1 (torque G x p) i a b,torque,ContinuousLinearEquiv.apply_symm_apply]; change (cell p i*tailwind G x p a b).re=_; unfold tailwind; split <;> simp [cell_duality p, *] -- wrong conj
private def unit (x:B):Link G m := (Pi.basisFun ℝ B) x
private lemma connects (x:B): ∑ p:S,torque G x p=(Fintype.card (Site m):ℝ) • unit G x:= by
   ext t; rw [Finset.sum_apply]; by_cases ht:t.2=x.2; · simp_rw [torque_read, if_pos (show _ = _ from ht.symm)]; rw [←Complex.re_sum, orthogonal]; unfold unit; by_cases hv:t.1=x.1 <;> simp [hv, Pi.single_apply,Prod.ext_iff,ht]; exact (congr_arg Complex.re (show (m.val:ℂ)^4=(( (m.val:ℝ)^4:ℝ):ℂ) by push_cast; rfl))
   simp_rw [torque_read, if_neg (Ne.symm ht),sum_const_zero]; rw [unit,Pi.basisFun_apply]; simp [Pi.single_eq_of_ne (show t≠x from fun e=> ht (congr_arg Prod.snd e))]
private lemma triceps {C:ℝ} (T:Link G m →ₗ[ℝ] Link G m→ₗ[ℝ]ℝ)(h:∀ x y p q, |T (torque G x p) (torque G y q)| ≤ C)(x y:B): ‖T (unit G x) (unit G y)‖≤ C:= by
   let a:ℝ:=Fintype.card (Site m); have hp:0 < a:= by unfold a; positivity
   have he: a*(a*T (unit G x) (unit G y))=∑ p:S,∑ q:S,T (torque G x p) (torque G y q):= by calc
    _= T (a • unit G x) (a • unit G y):= by simp
    _= _:= by rw [show a •_= _ from (connects G x).symm,show a •_= _ from (connects G y).symm]; simp only [map_sum,LinearMap.sum_apply]; rw [sum_comm]
   apply le_of_mul_le_mul_left (a:=a^2) ?_ (sq_pos_of_pos hp); calc
      _ = ‖(a*(a*T (unit G x) (unit G y)))‖:= by rw [norm_mul,norm_mul,Real.norm_of_nonneg hp.le,pow_two,mul_assoc]
      _ ≤ _:= by rw [he]; exact (norm_sum_le ..).trans ((sum_le_sum fun p _=> (norm_sum_le ..).trans (sum_le_sum fun q _=> h ..)).trans_eq (by simp only [sum_const,card_univ,nsmul_eq_mul,a]; ring))
-- let sec
lemma triton (g f:fieldDir G m 1→ℝ) {C d:ℝ}(hc:0≤C)(hd:0≤ d) (hg:AnalyticAt ℝ g 0)(hf:AnalyticAt ℝ f 0)(h:∀ p q X Y, (∀ i j,‖X i j‖ ≤ 1) → (∀ i j, ‖Y i j‖ ≤ 1) → |iteratedFDeriv ℝ 2 g 0 ![Precision.wave p X,Precision.wave q Y] - iteratedFDeriv ℝ 2 f 0 ![Precision.wave p X, Precision.wave q Y]| ≤ C)(x:Link G m)(hp:∀ i,‖x i‖≤ d): ‖jet (g∘arm G m 1) 2 x-jet (f∘ arm G m 1) 2 x‖≤ ((Fintype.card B)*d)^2*C:= by
    let L:= arm G m 1; let K:= Work.F05.bend g 0- Work.F05.bend f 0; let T:= LinearMap.compl₁₂ K L.toLinearMap L.toLinearMap; have he (u v:B): ‖T (unit G u) (unit G v)‖≤ C:= by
      refine triceps G T ?_ u v; intro a b p q; change ‖bend g 0 (L _) (L _) - bend f 0 (L _) (L _)‖≤ _; unfold torque L; rw [ContinuousLinearEquiv.apply_symm_apply,ContinuousLinearEquiv.apply_symm_apply,bend_apply,bend_apply]; exact h _ _ _ _ (tailwind_bound G _ _) (tailwind_bound G _ _)
    let k p:= x p • unit G p; have hk : ∑ i,k i=x:= (Pi.basisFun ℝ B).sum_repr x; rw [show jet (g∘ _) _ _- jet (f∘_) _ _=T x x /2 from ?_]; swap; · erw [woven hg (arm G m 1).toContinuousLinearMap x, woven hf (arm G m 1).toContinuousLinearMap x]; change Radial.jet g 2 (L x)-Radial.jet f 2 (L x)=(bend g 0 (L x) (L x)-bend f 0 (L x) (L x))/2; rw [bend_apply,bend_apply]; unfold Radial.jet; rw [show ![L x,L x]=(fun _:Fin 2=> L x) from funext fun p=>by fin_cases p<;>rfl]; norm_num; ring
    rw [norm_div,Real.norm_of_nonneg zero_le_two]; apply le_trans (div_le_self (norm_nonneg _) one_le_two); rw (occs:=.pos [1,2]) [←hk]; simp only [map_sum,LinearMap.sum_apply]; refine (norm_sum_le ..).trans ((sum_le_sum fun j _=> (norm_sum_le ..).trans (sum_le_sum (g:=fun _:Lines G m 1=>d*(d*C)) fun i _=> ?_ )).trans_eq ?_) -- stuck metavars
    · exact le_trans (b:=‖x i‖*(‖x j‖*‖T (unit G i) (unit G j)‖)) (le_of_eq (by simp [k]; ring)) (mul_le_mul (hp i) (mul_le_mul (hp j) (he i j) (norm_nonneg _) hd) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hd)
    simp only [sum_const,card_univ,nsmul_eq_mul]; ring
end Shelf
end Plata
end
end YM.Contacts.Lintel
