import YM.OPE.Compatible.Kyoto.Tree
/-!
# control all of inverse σμ under Φ fixed stage, no common across stages.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lake
open Function Filter MeasureTheory Spec Lattice RG Word Cov Allot ContinuousLinearMap
open scoped Topology Classical BigOperators
variable {I:Type}{d:ℕ} {E: Fin (d+1)→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℂ (E i)]
variable {p:I→Train E}{F:I→ Dock E≃L[ℂ] Dock E}
local notation "I!"=> Fin (d+1)
variable {L:Filter I}{V η:I→ℝ}{B:ℝ}
variable (hq :∀ᶠ i in L,(F i).toContinuousLinearMap=p i ∧ Flyer (p i) B (η i)) (ht:Tendsto V L atTop) (hp: RateLE L V p 0)(hS:1 ≤ B)(h:∀ᶠ i in L,1 ≤ η i)(hη:RateLE L V η 0)
set_option quotPrecheck false
local notation "Λ"=>fun i=> (F i).symm.toContinuousLinearMap
local notation "z"=>RateLE L V
include hq ht hp hS h hη
lemma ascentW (i j:I!) : z (fun k=> route ((F k).symm.toContinuousLinearMap) i j) 0:=by
       let T':=Λ; suffices he:∀ k:ℕ,∀ i:I!,i.val=k → z (fun k=>route (T' k) i j) 0 from he _ i rfl
       intro k; induction k using Nat.strong_induction_on with
       | _ k H=>
           intro i hi; let b:=(B^(d-i.val))⁻¹; let g(n)(u v:I!):= route (T' n) u v; let f(n)(u v:I!):= route (p n) u v;
           have hv: z (fun k=> b*η k) 0:= (by simpa only [zero_add] using (RateLE.const b ht).mul hη)
           by_cases hz : i=j
           · subst j; exact RateLE.of_norm_le hv (hq.and h|>.mono fun n hh=>hh.1.2.revD hh.1.1 hS hh.2 i)
           let I₀ := Finset.univ.filter (fun v:I!=>v < i); let q(n)(u:I!):=(f n i u).comp (g n u j); let Q(n:I):= - ∑ u∈I₀,q n u
           have hQ: z Q 0 := (RateLE.sum (f:=fun i n=>q n i) (S:=I₀) ht (fun l hl=>by
                   have he:= H l.val (hi ▸ (show l.val < i.val from Finset.mem_filter.mp hl|>.2)) l rfl; have hL:z (fun j=> f j i l) 0:= hp.transfer (Eventually.of_forall fun _=>tolls ..); exact (RateLE.bil hL he (Eventually.of_forall fun _=> opNorm_comp_le ..)).mono (by simp))).neg
           apply RateLE.of_norm_le ((hv.mul hQ.norm).mono (by simp)); filter_upwards [hq,h] with n hh ha; let U:= F n; let V':= Q n; have he: q n i= V':=by
                 apply eq_neg_of_add_eq_zero_left; have he: p n ∘L (T' n)= ContinuousLinearMap.id ..:=by rw[←hh.1]; ext1 x; exact U.apply_symm_apply x
                 have hx := routes (p n) (T' n) i j; rw[he, ←Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hx; change q n i+ _=_; apply Eq.trans (congr_arg (fun v=>q n i+v) (Finset.sum_subset ?_ ?_)) (hx.symm.trans ?_)
                 · intro k h; exact Finset.mem_erase.mpr ⟨ne_of_lt (Finset.mem_filter.mp h|>.2),Finset.mem_univ _⟩
                 · intro k hk he; have hl:i<k:=lt_of_le_of_ne (le_of_not_gt (fun h=> he (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))) (Finset.ne_of_mem_erase hk).symm; rw[hh.2.grow _ _ hl];simp
                 ext1 v; exact Pi.single_eq_of_ne (M:=E) hz _
           refine (g n i j).opNorm_le_bound (mul_nonneg (mul_nonneg (inv_nonneg.mpr (by positivity)) (zero_le_one.trans ha)) (norm_nonneg _)) (fun x=>?_); refine (hh.2.lo i _).trans ?_; rw [show route (p n) i i (g n i j x)=Q n x from DFunLike.congr_fun he x] -- unfold f?
           exact (mul_le_mul_of_nonneg_left ((Q n).le_opNorm x) (mul_nonneg (inv_nonneg.mpr (by positivity)) (zero_le_one.trans ha))).trans_eq (mul_assoc ..|>.symm)
lemma μTravel : z (fun i=> (F i).symm.toContinuousLinearMap) 0:=by
       let f:= Λ; let p(n:I)(i j:I!):= ‖route (f n) i j‖; have hz(n): ‖f n‖≤ ∑ i,∑ j,p n i j:= by refine (f n).opNorm_le_bound (Finset.sum_nonneg fun _ _=> Finset.sum_nonneg fun _ _=>norm_nonneg _) (fun i=>?_); apply le_trans (board (f n i)); unfold berth; rw [Finset.sum_mul]; refine Finset.sum_le_sum fun j _=>?_ ; rw [routed]; refine (norm_sum_le ..).trans ?_; rw[Finset.sum_mul]; exact Finset.sum_le_sum fun k _=> ((route (f n) j k).le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm i k) (norm_nonneg _))
       have hv(i j): z (fun n:I=> p n i j) 0:=(ascentW hq ht hp hS h hη i j).norm; exact RateLE.of_norm_le (RateLE.sum (f:=fun i n=>∑ j,p n i j) (S:=Finset.univ) ht (fun i _=> RateLE.sum (f:=fun j n=>p n i j) (S:=Finset.univ) ht (fun _ _=> hv i _))) (Eventually.of_forall hz)
end YM.OPE.Lake
