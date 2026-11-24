import YM.FVA2.Wick.Fmla

/-!
# Fermion determinant in the MS power-series algebra

`trace_bar` and `pair_read` see the same covariance and **odd** sign. The proof uses the Euler
identity on the series, so no explicit permutation expansion, and retains all uncontracted
boson legs in the result. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Wick.Fermion
open Function Set Finset Filter
open MS MS.Koszul MS.Plane MS.Orbit MS.Orbit.Cog MS.Swirl MS.Book Convolve MS.Cylinder Taylor
open MS.Puff MS.Puff.Mom MS.Puff.Engine MS.Puff.Actors Gem
open Formal (overlay)
open scoped BigOperators Topology ContDiff Matrix Matrix.Norms.Frobenius
variable {A J E : Type} [FA:Fintype A] [DA:DecidableEq A] [FJ:Fintype J] [DJ:DecidableEq J]
local notation "L" => Index A J
local notation "p" => sector (A:=A) (J:=J)
local infixl:70 " ⋆ " => product p
local infixl:70 " ★ " => overlay p
local notation "R" => Formal.Table L
local notation "Λ" => promote (Wg A J)
local notation "G" => odd A J
local notation "β" => allIndex (Alone p) ℕ
local notation "ι" => Formal.tab
local notation "Φ" => Formal.tab (A:=L) (coin 1)

variable (e : A→E) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M:E→Matrix J J ℝ}
variable (i j:J)
local notation "T" => Gem.letter (eased (J:=J) e)
local notation "k" => (fun i:J=> Formal.tab (atLetter (ghost (A:=A) i) («R»:=ℂ)))
local notation "f" => (fun i:J=> Formal.tab (atLetter (bar (A:=A) i) («R»:=ℂ)))
local notation "∂" => Formal.der (ghost (A:=A) i)
local notation "MK" => exponent e M
local notation "Z" => exp0 p MK
local notation "U" => Λ Z
local notation "θ" => Swirl.clock useN (Raw L ℂ)
variable (h0:M 0=1) (h: germ M)
include h0 h
local notation "τ" => (fun i j:J=> Λ (f i ★ k j ★ Z))

omit FA DA FJ [NormedAddCommGroup E] [NormedSpace ℝ E] h0 h in
lemma eq_diag (t : R)(i j:J) : (if i=j then Φ else 0) ★ t = if i=j then t else 0 := by
  split; exact (PermV p).identityK _; simp

lemma fp_equation : (∑ u:J, T (atM M u i) ★ τ u j) = if i=j then U else 0 := by
  let x u := f (u:J); let y u:= k (u:J); let θ' := MK; let V:= Z
  let F:=τ; let m (u v:J) := T (minus M u v); have he := exp_first e M h0; have hz : Z∈funded p := Formal.exponent_ok (valid e M (select_s h))
  have hs u : y j ★ ((x u ★ m u i) ★ Z) = - (m u i ★ (x u ★ y j ★ Z)) := by
    rw [commute_left _ (m u i) (minus_alone u i e M) |>.symm, Formal.assoc]
    rw [← Formal.assoc p, commute_left _ (m u i) (minus_alone u i e M) |>.symm]
    rw [Formal.assoc, ← Formal.assoc p _ (x u) Z, bar_comm j u,map_neg,LinearMap.neg_apply, map_neg] -- orientation
  have hx : F i j = (if j=i then U else 0) - ∑ u:J, m u i ★ F u j := by
     unfold F; rw [Formal.assoc, trace_bar i ( (k j) ★ Z ) (Formal.overlay_ok (ghost_funded _) hz), Formal.der_product (ghost_graded j), d_ghost, Formal.der_exp MK (even e M) he, exp_input_D ];
     have hV : y j ★ ((-∑ j, x j ★ m j i) ★ Z) = ∑ u:J,m u i ★ (x u ★ y j ★ Z) := by
        simp_rw [map_neg,map_sum,LinearMap.neg_apply,LinearMap.sum_apply,map_neg,map_sum,hs, Finset.sum_neg_distrib,neg_neg]
     rw [hV]; simp_rw [ show cross (p (ghost i)) true= (-1:ℂ) from rfl, neg_one_smul, map_add,map_neg,map_sum,
       show ∀ u:J,Λ (m u i ★ (x u ★ y j ★ Z))= _ from fun u=> frame_time _ _ (minus_alone u i e M) (Ti u i e M (select_s h)) (Formal.overlay_ok (Formal.overlay_ok (bar_funded u) (ghost_funded j)) hz) ]; by_cases hQ:i=j
     · rw [if_pos hQ,if_pos hQ.symm,Formal.tab_left]; exact (sub_eq_add_neg ..).symm
     rw [if_neg hQ,if_neg (Ne.symm hQ),map_zero,LinearMap.zero_apply,map_zero]; exact (sub_eq_add_neg ..).symm
  have hk (u:J) : T (atM M u i)=m u i+(if u=i then Φ else 0):= by unfold m; rw [minus_eq e M (select_s h), sub_add_cancel]
  change (∑ u:J,T (atM M u i) ★ F u j)=_
  simp_rw [hk,map_add,LinearMap.add_apply, Finset.sum_add_distrib, eq_diag]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), hx, add_sub_cancel]; by_cases hq:i=j <;> simp [hq, eq_comm]

lemma pair_read : τ i j = T (atV M j i) ★ U := by
  have hp : IsUnit (M 0).det:= by rw [h0]; simp
  have hi (x:J) : ∑ v:J, T (atV M v i) ★ T (atM M x v) = if x=i then Φ else 0 := by
    simp_rw [Formal.central (Gem.even _ (eased_p e) (atV M _ _)) ]; exact inverse_ink _ (eased_p e) h hp x i
  calc
    _ = ∑ x:J,(∑ u:J,T (atV M u i) ★ T (atM M x u)) ★ τ x j := by simp_rw [hi,eq_diag]; simp
    _ = ∑ u:J, T (atV M u i) ★ (∑ x:J,T (atM M x u) ★ τ x j) := by simp_rw [map_sum,LinearMap.sum_apply,Formal.assoc]; exact Finset.sum_comm
    _ = _ := by simp_rw [fp_equation e _ j h0 h]; simp [apply_ite (overlay p _)]

theorem unbill : Λ (exp0 p MK)= T (germ_det M) := by
  let V := exp0 p MK; let ψ (i j:J) := θ (T (atM M i j)) ★ T (atV M j i); let F:R := ∑ i:J,∑ j:J, ψ i j
  have hF (i j : J) : ψ i j 0=0:= by unfold ψ; rw [Formal.coeff_zero, Formal.time_weight]; simp
  have hp : IsUnit (M 0).det:= by rw [h0]; simp
  apply tick_agree useN (actor p) (u:=F) _ _ _ (Euler_ink _ (eased_p e) h hp)
  · unfold Happy; change F 0=0; simp [F,hF]
  · change Λ V 0=_; rw [promised, show V 0=coin 1 from Formal.exp_zero p (exp_first e _ h0), Wg_coin ]; change _ = T (germ_det M) 0; rw [Gem.first]; simp [germ_det,h0]
  let tm (i j : J) := θ ( T (minus M i j))
  let b (i j:J) : R:=ι (xy i j)
  have hθ (i j:J) : θ (b i j)=0:= clock_U _
  have ht (i j:J) : tm i j= θ (T (atM M i j)) := by unfold tm; rw [minus_eq e M (select_s h), map_sub]; split; rw [show θ Φ=0 from clock_U _,sub_zero]; rw [map_zero,sub_zero]
  have hZ : Z∈funded p:= Formal.exponent_ok (valid e M (select_s h)); have hw i j : tm i j∈β:= fun y _=> (Alone p).smul_mem (y:ℂ) (minus_alone i j e M y (Set.mem_univ _));
  have hY i j : Λ ((θ ((b i j) ★ T (minus M i j))) ★ Z)= ψ i j ★ Λ Z:= by
    have hh : b i j = f i ★ k j := Eq.symm (Formal.tabs p _ _)
    rw [Formal.clock_prod,hθ i j,map_zero,LinearMap.zero_apply,zero_add]
    rw [hh]; change Λ (((f i ★ k j) ★ tm i j) ★ Z)=_
    rw [← commute_left _ _ (hw i j), Formal.assoc p (tm i j), frame_time _ _ (hw i j) (Formal.clock_ok (Ti i j e M (select_s h))) (Formal.overlay_ok (Formal.overlay_ok (bar_funded _) (ghost_funded _)) hZ), show Λ (f i ★ k j ★ Z) = _ from pair_read e i j h0 h, ht i j]; exact (Formal.assoc ..)|>.symm
  change θ (Λ Z)= F ★ Λ Z
  rw [← Formal.time_comm, Formal.time_exp (even e M) (exp_first e M h0)];
  change Λ (θ (∑ i:J,∑ j:J,b i j ★ T (minus M i j)) ★ Z) = _
  unfold F; simp_rw [map_sum, LinearMap.sum_apply, map_sum,hY]
end YM.FVA2.Wick.Fermion
