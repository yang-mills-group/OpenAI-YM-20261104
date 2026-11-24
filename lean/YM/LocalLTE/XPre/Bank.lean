import YM.LocalLTE.XPre.Heap
/-! # Bucket under collision packing. Entire T alphabet.Measure.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.XPre
open Function Finset Filter MeasureTheory Lattice Wilson RG
open Extra.Histories Push Local Motion Extra.Multi
open LocalLTE.Fan LocalLTE.River LocalLTE.Vinca Ticket
open PhysicalNext.Repeat Lotus Blush Progress.DirectedRecipe
open YM.MergeProof Menu Marker Accent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{c f:Side}{S:StepData c f} {R : Rep G f} {C: Rep G c}
variable {J I N T:Type}[DecidableEq J][Fintype J][Fintype I][Fintype N][Fintype T]
variable {B:Marker.Census J}{d p m l K:ℕ} {κ V:ℝ}
variable (A:T→Hat B R) (h:T→Prop)
variable (g:ℝ) (w:J→ℝ)
noncomputable def uses (i:T):= R.p.mass (A i).M.crest (Menu.fare (A i) w)
noncomputable def banks := ∑ i:T,(if h i then 1 else g)* R.p.mass (A i).M.crest (Menu.fare (A i) w)
include g
variable (hw:∀ i,0<w i)(hg:1≤g){u:ℝ}
include h hw hg
local notation "Fq"=> banks A h g w
local notation "p'"=> (R.p.supportExponent)
local notation "f'"=> (fun i:T=> uses A w i)
local notation "rp"=> alphaH A h
omit [Fintype J] in
lemma e_init (z:ℕ) (p: Rock A (.logKey z)) :
    (if (∀ i∈ p.val.val,h i) then 1 else g)*R.p.mass (rise A (.logKey z) p.val).M.crest (Menu.fare (rise A (.logKey z) p.val) w) ≤ ∏ i∈ p.val.val,((if h i then 1 else g)*R.p.mass (A i).M.crest (Menu.fare (A i) w)):=by
    let k:= Wing.logKey z; let a:= p.val; let r:=p.val.val; let V:=rise A k p.val; let f i:=Menu.fare (A i) w; let g' i:=(if h i then (1:ℝ) else g); let u:=if ∀ i∈ a.val,h i then (1:ℝ) else g
    have hg' i: 1 ≤ g' i:= by unfold g';split; rfl; exact hg; -- tactic.
    have hg(i):0≤ g' i:= zero_le_one.trans (hg' i); have hf(i):0≤ f i:= Menu.Crew _ hw
    have hb i (hi:i∈ a.val): (A i).M.turn=k:=(mem_filter.mp (a.property.2.1 hi)).2
    have hp₁ i (hi:i∈ a.val):(A i).M.crest=V.M.crest:= congr_arg (fun z:Wing=> z.support R) (hb _ hi)
    have hX(i)(hi:i∈ a.val):f i ≤R.p.mass V.M.crest (f i):= R.p.loMass _ _ (hf i)
    let T0:= a.val; change u* R.p.mass V.M.crest (Menu.fare (rise ..) w) ≤ _
    rw [Menu.tolls,Finset.prod_mul_distrib]
    apply mul_le_mul
    · by_cases h':∀ i∈a.val,h i
      · unfold u;rw [if_pos h']; exact one_le_prod (fun i _=> hg' i)
      push Not at h';obtain ⟨i,hi,H⟩:=h'
      have hG:g' i=u:=by unfold g' u; rw [if_neg H,if_neg (fun h=>H (h i hi))]
      rw [← hG,← Finset.mul_prod_erase _ _ hi]; exact le_mul_of_one_le_right (hg i) (one_le_prod fun i _=> hg' i)
    · unfold BudgetPoint.mass
      let y :ℝ:= Real.exp (R.p.supportExponent*coverNumber R.p.B V.M.crest); have hy:1 ≤ y:= Real.one_le_exp (mul_nonneg R.p.exponent_pos.le (Nat.cast_nonneg _))
      rw [Finset.prod_congr (s₂:= T0) rfl (f:=fun x=> Real.exp (R.p.supportExponent* (coverNumber R.p.B (A x).M.crest :ℝ))*Menu.fare (A x) w) (g:=fun i:T => y*f i) (fun i hi=> by rw [hp₁ i hi]) , Finset.prod_mul_distrib,Finset.prod_const]
      apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun i _=> hf i)); apply le_self_pow₀ hy ; exact Finset.card_pos.mpr a.property.1|>.ne' -- syntax
    · unfold BudgetPoint.mass; exact mul_nonneg (Real.exp_nonneg _) (prod_nonneg fun i _=> hf i)
    exact prod_nonneg fun i _=> hg i
set_option quotPrecheck false
local notation "Yτ"=> Σ i:logDeck A, Rock A (.logKey i.val)
omit g h hg hw [Fintype J] in
noncomputable def outerF (i:Yτ):Finset T:= i.snd.val.val
omit g h hg hw [Fintype J] in
lemma riv : Injective (outerF A):=by
    intro p q hp; let T:=p.snd.val.val; obtain ⟨x,hx⟩:=p.snd.val.property.1; have ht:(A x).M.turn=.logKey p.fst.val:=(mem_filter.mp (p.snd.val.property.2.1 hx)).2; have hq : (A x).M.turn=.logKey q.fst.val:= (mem_filter.mp (q.snd.val.property.2.1 ((show p.snd.val.val=q.snd.val.val from hp) ▸ hx))).2
    obtain ⟨i,p⟩:=p; obtain ⟨j,q⟩:=q; obtain rfl : i=j:= Subtype.ext (Wing.logKey.inj (ht.symm.trans hq)); exact congr_arg _ (Subtype.ext (Subtype.ext hp) : p=q)
omit [Fintype J] in
lemma fas (he: Fq ≤ u): banks (heap A) (alphaH A h) g w ≤ u + (Real.exp u-1):= by
    unfold banks Mound; rw [Fintype.sum_sum_type]; apply add_le_add he
    let f i:= (if h i then 1 else g)* R.p.mass (A i).M.crest (Menu.fare (A i) w)
    have hp i:0≤f i:=by unfold f; apply mul_nonneg; split; exact zero_le_one; exact zero_le_one.trans hg;exact mul_nonneg (Real.exp_nonneg _) (Menu.Crew _ hw)
    let F (s:Finset T):=∏ i∈s,f i
    have hQ : ∑ i:Yτ, F (outerF A i) ≤ Real.exp u -1:=by
        rw [← Finset.sum_image (riv A|>.injOn)]
        let s:= (Finset.univ (α:=T)).powerset; let S:=s.erase ∅; let X:=Finset.univ.image (outerF A)
        have hx:X⊆ S:=by
           intro i hi; obtain ⟨i,_,rfl⟩:= mem_image.mp hi; have h: (outerF A i).Nonempty:= i.snd.val.property.1; exact mem_erase.mpr ⟨h.ne_empty, mem_powerset.mpr (subset_univ _)⟩
        apply le_trans (sum_le_sum_of_subset_of_nonneg (f:=F) hx (fun i _ _=> prod_nonneg fun i _=> hp i))
        apply le_sub_iff_add_le.mpr; rw [show (1:ℝ) = F ∅ from (prod_empty).symm, sum_erase_add s F (show ∅∈s from empty_mem_powerset _)]
        refine le_trans ?_ (Real.exp_le_exp.mpr he); change (∑ v∈Finset.univ.powerset,∏ i∈v,f i) ≤ Real.exp (∑ i,f i);rw [← Finset.prod_one_add,Real.exp_sum]; exact Finset.prod_le_prod (fun i _=> add_nonneg zero_le_one (hp i)) fun i _=>(add_comm ..).trans_le (Real.add_one_le_exp (f i))
    refine le_trans (Finset.sum_le_sum (fun i hi=>?_)) hQ
    have hx:= XPre.e_init A h g w hw hg _ i.2
    by_cases h':(∀ j∈ i.2.val.val,h j); rw [if_pos h'] at hx; simp only [if_pos (show rp (Sum.inr i) from h')]; exact hx
    rw [if_neg h'] at hx; simp only [if_neg (show ¬ rp (Sum.inr i) from h')]; exact hx

end YM.LocalLTE.XPre
