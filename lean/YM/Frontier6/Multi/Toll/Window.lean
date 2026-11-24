import YM.Frontier6.Multi.Toll.Way

/-! Finite financing gates at moving legs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Filter Lattice RG Wilson MergeProof Ribbons Canopies Finset Push Stock GridApprox
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage
open scoped Topology BigOperators Classical
section
variable {G:Gauge}(A:Levels G) (C:Family G)(hG:G.Simple)
variable {r:ℕ→ℕ}{D:∀ N p i,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (hV:Velour C (renal C.path.levels) r D)
lemma region_index (i:ℕ): (i:ℝ)*Real.log 3 ≤ A.S.scale i:=by
    induction i with
    | zero=>simp
    | succ i ih=> rw [A.S.scale_succ,Nat.cast_succ,add_mul,one_mul]; exact add_le_add ih (Real.log_le_log (by norm_num) (by exact_mod_cast A.S.block_large i))
lemma region_cost : Note A.S (fun i=>(A.clock.J i:ℝ)+5) 0:=by
    have hp(i): (A.clock.J i:ℝ) ≤ (A.clock.J 0:ℝ)+i:=by
       induction i with
       | zero=> simp
       | succ i ih=> rw [Nat.cast_succ,← add_assoc]; exact le_trans (show _≤ (A.clock.J i:ℝ)+1 by exact_mod_cast A.fits.stepSlow i) (add_le_add ih (le_refl _)) -- right?
    have hL : 0 < Real.log 3:= Real.log_pos (by norm_num)
    let f i:= (A.clock.J 0:ℝ)+i/Real.log 3+5
    have hv : ∀ᶠ i:ℕ in atTop, 1 ≤ (A.clock.J i:ℝ)+5 ∧ (A.clock.J i:ℝ)+5 ≤ (f (A.S.scale i)):= by
       filter_upwards with i; have ht: (i:ℝ) ≤ A.S.scale i/Real.log 3:= (le_div_iff₀ hL).mpr (region_index A i); exact ⟨by linarith [Nat.cast_nonneg (α:=ℝ) (A.clock.J i)], add_le_add (le_trans (hp i) (by linarith)) le_rfl⟩
    refine ⟨fun i=>by positivity, squeeze_zero' (g:=fun i=> Real.log (f (A.S.scale i))/A.S.scale i) ?_ ?_ ?_⟩
    -- compare with log(Zscale)/Zscale
    · filter_upwards [hv,A.S.divergent.eventually_gt_atTop 0] with i hi hp; exact div_nonneg (Real.log_nonneg hi.1) hp.le
    · filter_upwards [hv,A.S.divergent.eventually_gt_atTop 0] with i hi hp; exact div_le_div_of_nonneg_right (Real.log_le_log (zero_lt_one.trans_le hi.1) hi.2) hp.le
    let b:= A.clock.J 0+5; let a:= Real.log 3; have he:Tendsto (fun i:ℕ=> f (A.S.scale i)) atTop atTop:= by apply tendsto_atTop_add_const_right atTop 5; exact tendsto_atTop_add_const_left _ _ (A.S.divergent.atTop_div_const hL)
    let g (x:ℝ):= x/(1/a) - (b:ℝ)*a
    have hh := (Real.tendsto_pow_log_div_mul_add_atTop a (-(b:ℝ)*a) 1 (show a≠0 from hL.ne')).comp he; refine hh.congr' ?_
    filter_upwards with i; dsimp only [comp_apply]; unfold f b; push_cast; rw [pow_one]; congr 1; congr 1; unfold a; field_simp; ring -- fix

include hG hV in
lemma restoreN : Note C.S (restoreRate C.path.levels (renal C.path.levels)) 0:=by
    let A:=C.path.levels
    let q(i:ℕ):= ((A.budget i).supportExponent+1/2)*inscribed A i
    have hp(i) : 0 ≤ q i:=mul_nonneg (add_nonneg (A.budget i|>.exponent_pos.le) (by norm_num)) (Nat.cast_nonneg _)
    have hs:Note A.S (fun i=> Real.exp (q i)) 0:=by
       refine ⟨fun _=>Real.exp_pos _,?_⟩; simp_rw [Real.log_exp]; apply squeeze_zero' (Eventually.of_forall fun i=> div_nonneg (hp i) (Shoot.scale_nn _ _)) _ (whack C hG hV); filter_upwards with i
       apply div_le_div_of_nonneg_right _ (Shoot.scale_nn _ _); 
       have he:inscribed A i ≤ peepers A i:=by
          let T:ℕ:= (A.budget i).B; change 4*T^2+1 ≤ (2*(1024*T)+1)^4; have he:1 ≤ 2*(1024*T)+1:=by omega
          exact le_trans (b:=(2*(1024*T)+1)^2) (by nlinarith) (pow_le_pow_right₀ he (by norm_num))
       exact mul_le_mul_of_nonneg_left (by exact_mod_cast he) (by linarith only [ (A.budget i).exponent_pos])
    exact (((mintN C hG).1.powerN 2).splits ((Note.notes A.S 8 (by norm_num)).mills hs)).swapP (by norm_num)

open Fareway
variable {I:Type*}{T:Fareway I}{k j m:I→ℕ}{a b c ε:ℝ}(hj:Bench C.S T j c)(hm:Bench C.S T m a)(hk:Bench C.S T k b)
include hm
lemma roomed (hf:b<a)(hk:Bench C.S T k b)(p:ℕ):∀ᶠ i in T.via, GridApprox.room C.path.levels (k i) (m i) p:=by
    let A:= C.path.levels; have hh:T.Mint (fun i=>GridApprox.tail A (m i)) (-a) := ((T.minted_c 30 (by norm_num)).mul hm.spacing|>.mul (hm.notes (region_cost A))).eq (by ring)
    have hv:= (T.minted_c 2 two_pos).mul ((hm.spacing.mul (T.minted_c (p+1) (by positivity))|>.eq (add_zero _)).common hh)|>.eq (zero_add _)
    filter_upwards [hv.cheaper hk.spacing (by linarith)] with i hi; exact lt_of_le_of_lt (a:=2 * (A.S.a (m i) * p + GridApprox.tail A (m i))) (by gcongr <;> try (first| exact (C.S.a_pos _).le|linarith)) hi

include hG hV
lemma travelers (he:0<ε)(hv:0<c)(hj:Bench C.S T j c): ∀ᶠ i in T.via, ∀ b:ℕ,m i ≤ b→ b ≤ j i→ Real.exp (T.scale i*(-ε)) ≤ restoreRate C.path.levels (renal C.path.levels) b:=by
   let x:= ε/(2*c); have hx:0<x:=by unfold x; positivity
   have hh:= Note.bell_exp C.S (-x)|>.outweigh (restoreN C hG hV) (by linarith); obtain ⟨b,hb⟩:= eventually_atTop.mp hh
   filter_upwards [hm.infinite.eventually_ge_atTop b,hj.speed.eventually (gt_mem_nhds (show c< 2*c by linarith)),T.ahead] with i hi hG hi' b' he' hb'
   have hk:= hb b' (le_trans hi he'); apply le_trans (Real.exp_monotone (le_trans ?_ (mul_le_mul_of_nonpos_left ((bob C.S).monotone hb') (neg_nonpos.mpr hx.le)))) hk -- direction
   have h : C.S.scale (j i) ≤ (2*c)*T.scale i:=((div_lt_iff₀ hi').mp hG).le; exact le_trans (le_of_eq (by unfold x; field_simp  : T.scale i*(-ε)=-x*(2*c*T.scale i))) (mul_le_mul_of_nonpos_left h (by linarith))
end
end YM.Frontier6.Road
