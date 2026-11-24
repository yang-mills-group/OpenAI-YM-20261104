import YM.OPE.Compatible.Kyoto.Yank
/-!
# Travel bills. Triang bank. Inverse does not assume long μ.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lake
open Function Filter MeasureTheory Spec Lattice RG Word Cov Allot ContinuousLinearMap
open scoped Topology Classical BigOperators
variable {d:ℕ} {E: Fin (d+1)→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℂ (E i)]
variable {p:Train E}{F:Dock E≃L[ℂ] Dock E}
local notation "I!"=> Fin (d+1)
structure Flyer (p:Train E)(S η:ℝ):Prop where
      grow : team p
      hi (i:I!): ‖route p i i‖≤ S^(d-i.val)*η
      lo (i:I!)(x:E i): ‖x‖≤ ((S^(d-i.val))⁻¹ * η)* ‖route p i i x‖
namespace Flyer
variable {S η:ℝ} (A:Flyer p S η)
include A
lemma peeled (v:Dock E)(m:ℕ)(ht:∀ (i:I!),i.val < m → p v i=0)(i:I!)(hi:i.val < m): v i=0:=by
       suffices h:∀ k:ℕ,∀ (i:I!), i.val=k→ k < m → v i=0 from h _ i rfl hi
       intro k; induction k using Nat.strong_induction_on with
       | _ k h=>
          intro i hi hk; have he: route p i i (v i)=0:=by
               rw [← ht i (hi ▸ hk),routed,Finset.sum_eq_single i]; intro j _ hj; by_cases hh:j < i; rw[h j.val (hi ▸ hh) j rfl (by rw[← hi] at hk;exact Nat.lt_trans hh hk), _root_.map_zero]; rw[A.grow _ _ (lt_of_le_of_ne (le_of_not_gt hh) hj.symm)]; simp; simp
          apply norm_le_zero_iff.mp; exact (A.lo i _).trans_eq (by rw [he,norm_zero,mul_zero])
lemma existsB [∀ i,FiniteDimensional ℂ (E i)] : ∃ U:Dock E≃L[ℂ] Dock E,U.toContinuousLinearMap=p:=by
       have hv:Injective p.toLinearMap:= LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.2 (fun x hx=> funext fun i=>peeled A x (d+1) (fun i _=>congr_fun hx i) i i.isLt)); let F:=LinearEquiv.ofBijective p.toLinearMap ⟨hv,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hv⟩; exact ⟨F.toContinuousLinearEquiv,ContinuousLinearMap.ext fun _=>rfl⟩
variable (h:F.toContinuousLinearMap=p)
include h
lemma opposes : team F.symm.toContinuousLinearMap:=by
       intro i j he; ext1 v; exact peeled A (F.symm (Pi.single j v)) j.val (fun k hk=>by rw [← h]; change F (F.symm _) k=0; rw [F.apply_symm_apply]; exact Pi.single_eq_of_ne (M:=E) (ne_of_lt (show k<j from hk)) v) _ he
lemma revD (hv:1 ≤ S)(he:1 ≤η)(i:I!) : ‖route F.symm.toContinuousLinearMap i i‖≤ (S^(d-i.val))⁻¹ * η:=by
       let T:=route F.symm.toContinuousLinearMap i i; refine opNorm_le_bound T (by positivity) (fun x=> (A.lo i (T x)).trans_eq ?_); rw[show route p i i (T x)=x from _]; exact DFunLike.congr_fun (teamTracks F p F.symm.toContinuousLinearMap h.symm rfl A.grow (A.opposes h) i) x
end Flyer
end YM.OPE.Lake
