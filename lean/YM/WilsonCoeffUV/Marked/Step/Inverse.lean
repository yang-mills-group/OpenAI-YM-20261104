import YM.WilsonCoeffUV.Marked.Step.Exponential
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Mark
open Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix
open scoped Topology BigOperators
variable {n:Side}{ι U:Type}{J K S T:Finset ι}{D k:ι→ℕ}{i j e r h N m l:ℕ}{G:Gauge}
variable [DecidableEq ι]
lemma stairK (k:ι→ℕ)(h:J⊆ S): mass k S= mass k J+mass k (S\J):= by rw [add_comm]; exact (Finset.sum_sdiff h).symm
lemma sh_k (h:J⊆ S)(z:J≠∅): S\J⊂ S:=lt_of_le_of_ne Finset.sdiff_subset (fun p=> z (Eq.symm (Eq.trans (Finset.sdiff_self _).symm ((congr_arg (S\·) p).symm.trans (twin_l h)))))

-- sum comprehension easier direct over s.powerset with proof q
noncomputable def levelsO (M:family G D) (S:Finset ι): Era G (Pen D S):=
 if h:S=∅ then h.symm ▸ puff D G
 else (S.card:ℝ)⁻¹ • ∑ j∈S.powerset, if w:j⊆S∧j≠∅ then (j.card:ℝ) • waxV w.1 (M j) (levelsO M (S\j)) else 0
termination_by S.card
decreasing_by apply Finset.card_lt_card; exact sh_k w.1 w.2

noncomputable def reverseO (M:family G D) (S:Finset ι): Era G (Pen D S):=
 if _h:S=∅ then 0 else M S - (S.card:ℝ)⁻¹ • ∑ j∈ S.powerset, if w:j⊆S∧j≠S then (j.card:ℝ) • waxV w.1 (reverseO M j) (M (S\j)) else 0
termination_by S.card
decreasing_by exact Finset.card_lt_card (lt_of_le_of_ne w.1 w.2)

lemma empty_level (M:family G D): levelsO M ∅=puff D G:=by rw [levelsO,dif_pos rfl]
lemma empty_reverse (M:family G D): reverseO M ∅=0:=by rw [reverseO,dif_pos rfl]
lemma wind_height (M:family G D)(L:family G D){S:Finset ι}(p:Eu k M)(h:∀ J⊂S,Auth (mass k J) (L J))(J:Finset ι): Auth (mass k S) (if w:J⊆ S∧J≠∅ then (J.card:ℝ) • waxV w.1 (M J) (L (S\J)) else 0):=by
   split
   next w=> rw [stairK k w.1]; exact (paidW w.1 _ _ (p J) (h _ (sh_k w.1 w.2))).μ _
   exact unstamped
lemma rev_height (M L:family G D){S:Finset ι}(p:Eu k M)(h:∀ J⊂S,Auth (mass k J) (L J))(J:Finset ι): Auth (mass k S) (if w:J⊆ S∧J≠S then (J.card:ℝ) • waxV w.1 (L J) (M (S\J)) else 0):=by
   split
   next w=> rw [stairK k w.1]; exact (paidW w.1 _ _ (h _ (lt_of_le_of_ne w.1 w.2)) (p _)).μ _
   exact unstamped
lemma placedO (M:family G D)(h:Eu k M): Eu k (levelsO M):=by
   intro S; induction S using Finset.strongInduction with
   | H S ih=>
       rw [levelsO]; split
       next e=> subst S; exact paidO _
       next e=> exact (Auth.sum (fun j _=>wind_height M (levelsO M) h ih j)).μ _
lemma counted (M:family G D)(h:Eu k M): Eu k (reverseO M):=by
   intro S; induction S using Finset.strongInduction with
   | H S ih=>
       rw [reverseO]; split
       next z=> exact unstamped
       exact (h S).sub ((Auth.sum (fun j _=> rev_height M (reverseO M) h ih j)).μ _)

abbrev feeble (P:family G D)(A:Case D)(n:Side)(S:Finset ι):= readO A (P S) n
lemma levels_exp (P:family G D)(p:Eu k P)(h:P ∅=0)(A:Case D)(n:Side) : Equation (feeble (levelsO P) A n) (feeble P A n):=by
    unfold feeble; refine ⟨by simp only [empty_level,readingO],by simp only [h,read_emp],?_⟩; let V:= levelsO P; funext S; by_cases z:S=∅; · subst S; rw [shells_emp]; simp [dial]
    have hf J:= wind_height P V p (S:=S) (fun i _=> placedO P p i) J
    have he:(S.card:ℝ)≠0:=by exact_mod_cast (show S.card≠0 from by simp [z])
    rw [dial,levelsO,dif_neg z,read_rho A n _ (Auth.sum (fun i _=>hf i)),read_Sum A n (fun i _=> hf i), ← Nat.cast_smul_eq_nsmul ℝ S.card _, smul_smul,mul_inv_cancel₀ he, one_smul]; apply Finset.sum_congr rfl; intro i hp
    split
    next H=> have ho:=paidW H.1 _ _ (p i) (placedO P p _); rw [read_rho _ _ _ ho, read_wax _ _ _ _ _ (p _) (placedO P p _),←smul_mul_assoc]; exact congr_arg (fun v=> v*_) (Nat.cast_smul_eq_nsmul ℝ i.card _)
    next u=> obtain rfl:= not_ne_iff.mp (fun H=> u ⟨Finset.mem_powerset.mp hp,H⟩); rw [read_emp]; simp only [dial,Finset.card_empty,zero_smul,zero_mul]

lemma levels_log (P:family G D)(p:Eu k P)(h:P ∅=puff D G)(A:Case D)(n:Side): Equation (feeble P A n) (feeble (reverseO P) A n):=by
    unfold feeble; refine ⟨by simp only [h,readingO],by simp only [empty_reverse,read_emp],?_⟩; let V:= reverseO P; funext S; by_cases z:S=∅; · subst S; rw [shells_emp]; simp only [dial,Finset.card_empty,zero_smul,zero_mul]
    have hf J:= rev_height P V p (S:=S) (fun i _=> counted P p i) J
    have he:(S.card:ℝ)≠0:=by exact_mod_cast (show S.card≠0 from by simp [z])
    rw [shells,← Finset.sum_erase_add _ _ (show S∈ S.powerset by simp), dial,Finset.sdiff_self,h,readingO,mul_one];
    rw [dial,reverseO,dif_neg z,read_lot _ _ _ _ (p _) ((Auth.sum (fun i _=> hf i)).μ _), read_rho _ _ _ (Auth.sum (fun i _=>hf i)), smul_sub,read_Sum _ _ (fun i _=> hf i)]
    rw [← Nat.cast_smul_eq_nsmul ℝ S.card ((S.card:ℝ)⁻¹ • _),smul_smul,mul_inv_cancel₀ he,one_smul,←Finset.sum_erase_add _ (f:=fun i=>readO A (if w:i⊆S∧i≠S then _ else _) n) (show S∈ S.powerset by simp),dif_neg (show ¬(S ⊆ S∧S≠S) by simp), read_emp,add_zero,add_comm _ (_-_)]
    refine (Eq.symm (sub_add_cancel (S.card • readO A (P S) n) _)).trans (congr_arg₂ (·+·) rfl ?_); apply Finset.sum_congr rfl; intro j hj; have h:j⊆S∧j≠ S:=by simpa only [Finset.mem_erase, Finset.mem_powerset, and_comm] using hj
    rw [dif_pos h, read_rho _ _ _ (paidW h.1 _ _ (counted _ p _) (p _)),read_wax _ _ _ _ _ (counted _ p _) (p _), ←smul_mul_assoc,dial, Nat.cast_smul_eq_nsmul]

theorem rectify (L:family G D)(h:Eu k L)(u:L ∅=0) : reverseO (levelsO L)=L:=by
    funext S; let M:=levelsO L; let K:=reverseO M; have hp: Eu k M:=placedO L h; apply read_ext _ _ (counted _ hp _) (h _); intro A n; exact congr_fun ((levels_log M hp (empty_level _) A n).unique _ _ _ (levels_exp L h u A n)) S

theorem wreathed (M:family G D)(h:Eu k M)(u:M ∅=puff D G) : levelsO (reverseO M)=M:=by
    funext S; let L:=reverseO M; let K:= levelsO L; have hp:= counted M h; apply read_ext _ _ (placedO _ hp S) (h S); intro A n; exact congr_fun (Equation.prod_u (feeble K A n) (feeble L A n) _ (levels_exp L hp (empty_reverse _) A n) (levels_log _ h u A n)) S
end YM.WilsonCoeffUV.Wheel.Mark
