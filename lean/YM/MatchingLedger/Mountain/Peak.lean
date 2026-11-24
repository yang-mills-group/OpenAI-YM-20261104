import YM.Planned.STATIONARY_JET_PORT.Enclosures
import YM.Analysis.Homogeneous
import YM.MatchingLedger.Compass.Tick

/-!
 # Mountain: principal activity entry budgets from all-support stencil lengths.
 Common Taylor (!) all mixed operator norms. Symmetric Tensor conventions. Multioutput
 stencil widths arrive separately. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.MatchingLedger.Mountain
open Set Function Filter Precision RG MeasureTheory Lattice Wilson Metric Tensor Push.Uniform
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius Classical

section Taylor
variable {E F Y : Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
    (f:E→ F) (h:ContDiffAt ℝ ω f 0)

abbrev cap (j:ℕ) := Tensor.diagonal (Tensor.coeff f j 0)
def summit (j:ℕ) : E→F:= ∑ i∈ Finset.range (j+1), cap f i
lemma summit_smooth (j:ℕ) : ContDiff ℝ ω (summit f j):= by unfold summit; rw [Finset.sum_fn]; exact ContDiff.sum (fun i _=> (diag_smooth (Tensor.coeff f i 0) _) ) -- syntax defeq?
lemma runes (j:ℕ)(x:E) : summit f j x= ∑ i∈Finset.range (j+1), (i.factorial:ℝ)⁻¹ • (iteratedFDeriv ℝ i f 0 (fun _=>x)):= by unfold summit cap Tensor.diagonal Tensor.coeff; rw [Finset.sum_apply]; rfl
lemma stays (j:ℕ) : summit f j 0=f 0:=by
   rw [runes,Finset.sum_eq_single (0:ℕ)]; simp
   intro i hi ht; rw [(iteratedFDeriv ℝ i f 0).map_coord_zero (⟨0,Nat.pos_of_ne_zero ht⟩:Fin i) rfl,smul_zero]
   simp
lemma constant : summit f 0=fun _=> f 0:=by funext x; rw [runes,Finset.sum_range_one];simp


open Analysis
include h
lemma drops (v:E)(k:ℕ) : D v (summit f (k+1))= summit (D v f) k:=by
   ext1 x; unfold summit D; rw [fderiv_sum (fun i _=> (diag_smooth _ ω).differentiable (by simp) _),Finset.sum_apply,(show _= _ from (sum_apply _ _ _)),Finset.sum_range_succ' (n:=k+1)] -- edit
   have hx:cap f 0=fun _=>f 0:=by ext1 x; unfold cap Tensor.diagonal Tensor.coeff; rw [_root_.smul_apply]; simp
   rw [show Tensor.diagonal (Tensor.coeff f 0 0)=_ from hx,show fderiv ℝ (fun _ : E=> f 0) x=0 from (by simp)]; simp_rw [_root_.zero_apply,add_zero]; apply Finset.sum_congr rfl
   intro i _; exact Tensor.slot_lower (h.of_le le_top) ..

lemma complete {j i:ℕ}(he:i≤j) : iteratedFDeriv ℝ i (summit f j) 0=iteratedFDeriv ℝ i f 0:=by
   induction i generalizing f j with
   | zero=> ext1 v; simp [stays]
   | succ i ih=>
      cases j with
      | zero => omega
      | succ j=>
         ext1 v; rw [← Fin.cons_self_tail v]
         rw [Analysis.cons_inner (summit_smooth f _|>.contDiffAt.of_le le_top),Analysis.cons_inner (h.of_le le_top), drops f h, ih (Analysis.D _ f) (dSmooth h _ le_top) (by omega)] -- edit
lemma finished {i k:ℕ} (hV:i<k)(x:E): iteratedFDeriv ℝ k (summit f i) x=0:=by
   induction i generalizing k f with
   | zero=> rw [constant,iteratedFDeriv_const_of_ne hV.ne']; rfl -- theorem typo
   | succ i ih=>
      cases k with
      | zero=> omega
      | succ k=>
         ext1 v; rw [← Fin.cons_self_tail v, Analysis.cons_inner (summit_smooth f _|>.contDiffAt.of_le le_top),drops f h,ih (Analysis.D _ f) (dSmooth h _ le_top) (by omega) ]; rfl

omit h
lemma changes (s:ℝ)(x:E){k:ℕ}(hv: ContDiffAt ℝ k f (s • x)) :
    iteratedFDeriv ℝ k (fun v=>f (s • v)) x= s^k • iteratedFDeriv ℝ k f (s • x) := by
   let T: E →L[ℝ] E := s • ContinuousLinearMap.id ℝ E
   change iteratedFDeriv ℝ k (f ∘ T) x=_
   ext1 v; rw [Push.Uniform.iter_lin_at (L:=T) (show ContDiffAt ℝ k f (T x) from hv)]
   simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply, T,_root_.smul_apply,ContinuousLinearMap.id_apply,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using! (iteratedFDeriv ℝ k f (s • x)).map_smul_univ (fun _=>s) v

def bit (k:ℕ) (s:ℝ) (x:E) := f (s • x)- summit f k (s • x)
lemma rarity {k i:ℕ}{M r s:ℝ} (hs:1≤r)(hr:0<s)(he : s*r<1)(h:∀ x∈ball (0:E) 1, Allows (k+1) f x M)(x:E)(hx:‖x‖ ≤ r)(hi:i≤k+1):
    Allows i (bit f k s) x (M*r^(k+1)*s^(k+1)):=by
   let y:= s • x; let w:= f - summit f k; let T:E→L[ℝ] E:= s • ContinuousLinearMap.id ℝ E
   have hh:‖y‖≤ s*r:= (norm_smul_of_nonneg hr.le x).le.trans (mul_le_mul_of_nonneg_left hx hr.le)
   have hY:y∈ ball (0:E) 1:= mem_ball_zero_iff.mpr (hh.trans_lt he)
   have hx':0∈ball (0:E) 1:= mem_ball_self zero_lt_one; have hM:0≤M:=(h _ hx').nonneg; have h₁ u (hp:u∈ball (0:E) 1):= (h u hp).analytic
   have hD (u) (hy:u∈ball (0:E) 1): ContDiffAt ℝ ω w u:= (h₁ u hy).sub (summit_smooth f k|>.contDiffAt)
   change Allows i (w ∘ T) x _
   refine ⟨(show ContDiffAt ℝ ω w (T x) from hD _ hY).comp _ T.contDiff.contDiffAt,fun j hJ=> ?_⟩
   have hx:= (h₁ _ hx'); have hp:= hJ.trans hi
   change ‖iteratedFDeriv ℝ j (fun u=>w (s • u)) x‖ ≤ _
   have ht:= Planned.JetPort.jetSmall (k:=k+1) (f:=w) (C:=M) zero_lt_one (fun x hx'=>⟨hD x hx',?_⟩) hM (fun l (hl:l<k+1)=>?_) j hp y hY
   rotate_left 1
   · unfold w; rw [iteratedFDeriv_sub_apply ((h₁ _ hx').of_le le_top) ((summit_smooth ..).contDiffAt.of_le le_top),finished f hx (by omega), sub_zero]; exact (h _ hx').norm_le _ le_rfl
   · unfold w; rw [iteratedFDeriv_sub_apply (hx.of_le le_top) ((summit_smooth ..).contDiffAt.of_le le_top),complete f hx (by omega),sub_self];
   rw [changes w s _ ((hD y hY).of_le le_top), norm_smul, Real.norm_of_nonneg (pow_nonneg hr.le j)]
   have hy' : 0≤ s^j:= pow_nonneg hr.le _
   refine (mul_le_mul_of_nonneg_left (ht.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hh _) hM)) hy').trans ?_
   rw [mul_pow,show s^j* (M*(s^(k+1-j)*r^(k+1-j)))= M*r^(k+1-j)*s^(j+(k+1-j)) by rw [pow_add]; ring,Nat.add_sub_of_le hp]
   gcongr; omega
end Taylor
end YM.MatchingLedger.Mountain
