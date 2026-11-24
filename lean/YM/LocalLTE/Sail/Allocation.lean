import YM.LocalLTE.Sail.Front
import YM.MergeProof.Wicket
/-!
# startup costs for a local layer on the actual family
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Sail
open Filter Function Finset Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open GridApprox.Nil Extra.Trajectories Progress.DirectedRecipe MergeProof Accent Push.AbsoluteSums
open GridApprox.Nil Local Extra.Multi Source Overlay Planned.GuardedAtom Guard
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V : Type} [DecidableEq V] [Fintype V]
variable (B:Census V) {G:Gauge}{n:Side} (P:Rep G n) (χ:V→ MergeProof.Response G n)
variable (X: V→ Support n) (t:ℝ)
    (h:∀ i k,χ i k≠0→ k=X i) (hh:∀ i U,‖χ i (X i) U‖ ≤ t)
    {k:ℕ} (hx:Fintype.card V≤k) (w:V→ℝ) (hw:∀ i,0<w i)(hq:∀ i,w i ≤1)
    {s a:ℝ}(hp:P.activities.Valid P.p a s)
    {m:ℕ} (hm:∀ i,(X i).card ≤ m)
open XPhase
/-- Coarse payment uses trivial support-card estimate for each localized pane.
  (For the real probes this cost is polynomial in SHIFTED beta after stage/order.) -/
noncomputable def birthFee (s t e:ℝ)(k m:ℕ):= (Real.exp (((k:ℝ)*m+1)*s)-1) * (1+Real.exp (e*m)*t)^k
include hm hp hx h hh hw hq
lemma alpine (he:0≤t)(hV:∀ i,coverNumber P.p.B (X i)≤ m) : Towed w Prod.fst (captain B P χ) P.p.B P.p.supportExponent (birthFee s t P.p.supportExponent k m) :=by
    let J:= P.activities; have hv:= vacant J P.p B hp w hw
    let φ:= conviction χ B; let b:(V→V×Support n):= fun i=>(i,X i); let W:=Finset.univ.image b
    let d (i:V×Support n):ℝ:= if i.2=X i.1 then w i.1*t else 0
    have hs(i):Loci w (φ i) (d i):=by
       unfold d;split
       next he'=> exact (show Poly.toll w (B.fire i.1)= w i.1 from Poly.solo_toll _) ▸ satin (χ i.1 i.2) (w:=w) (B.fire i.1) t he (fun U=> he'.symm ▸ hh i.1 U)
       next hx=> rw [show φ i=0 from ?_]; exact ⟨0,le_rfl,fun x y=>by simp,by simp [wordsPrice]⟩
                 funext j; unfold φ conviction; rw [not_not.mp (mt (h i.1 i.2) hx)]; simp -- check
    have hW(i):d i ≠0 → i∈ W:=by
       intro hi; unfold d at hi; split at hi
       next he=> exact Finset.mem_image.mpr ⟨i.1,Finset.mem_univ _, Prod.ext rfl he.symm⟩
       next=> contradiction
    apply Towed.shrink (Towed.sift (branch_localized (Accent.exclaim J B) φ Prod.snd W d w P.p hv hw hs hW)) le_rfl ?_ hw
    have hu : (W.biUnion Prod.snd).card ≤ k*m:=by
       have hM:(W.biUnion Prod.snd).card ≤ ∑ i∈W,i.2.card:= Finset.card_biUnion_le ..
       apply hM.trans (?_); refine le_trans (Finset.sum_le_sum (g:=fun _=>m) (fun i hi=>?_)) ?_
       · obtain ⟨i,hi,rfl⟩:= mem_image.mp hi; exact hm i
       rw [sum_const,nsmul_eq_mul]; exact Nat.mul_le_mul_right m ((Finset.card_image_le.trans_eq Finset.card_univ).trans hx) -- order
    let u (i:V×Support n):= 1+P.p.mass i.2 (d i)
    let c:= Real.exp (P.p.supportExponent*m)*t
    have hz(i):0 ≤ u i:= add_nonneg zero_le_one (mul_nonneg (Real.exp_nonneg _) ((hs i).fares hw|>.1))
    have hS:0≤ s:= ((tsum_nonneg ((show P.activities.KBound _ _ from hp.boundK).choose_spec.2 (0:Site n)).1).trans ((hp.boundK.choose_spec.2 (0:Site n)).2.2)) -- possible
    have hK:1 ≤ (1+c):= le_add_of_nonneg_right (mul_nonneg (Real.exp_nonneg _) he)
    have hT(i:V):(∏ j:Support n,u (i,j))≤ 1+c :=by
       rw [Finset.prod_eq_single (X i)]
       · refine add_le_add_right (mul_le_mul (?_) (?_) ((hs _).fares hw).1 (Real.exp_nonneg _)) _
         · refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr ?_) (P.p.exponent_pos.le)); exact hV i -- lemma search
         rw [show d (i,X i)=w i*t from if_pos rfl]; exact mul_le_of_le_one_left he (hq i)
       · intro j _ hj; unfold u; rw [show d (i,j)=0 from if_neg (show j≠X i from hj),BudgetPoint.mass,mul_zero,add_zero]
       simp
    refine mul_le_mul (sub_le_sub_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (add_le_add_left (by exact_mod_cast hu) _) hS)) _) ?_ (Finset.prod_nonneg fun i _=> hz i) (sub_nonneg.mpr (Real.one_le_exp (by positivity)))
    change (∏ i,u i)≤(1+c)^k; rw [Fintype.prod_prod_type]
    refine le_trans (Finset.prod_le_prod (g:=fun _=> 1+c) (fun i _=> prod_nonneg fun j _=> hz _) fun i _=>hT i) ?_
    rw [prod_const, Finset.card_univ]; exact pow_le_pow_right₀ hK hx
end YM.LocalLTE.Sail
