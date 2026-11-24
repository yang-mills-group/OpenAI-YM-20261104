import YM.FormalBulk08.Palm.Sister

/-!
# Matrices with slot and total weight (Pence coefficients)
Rows outputs. Leading only can lower slots; within slots raises weight by
exactly strict steps off the diagonal. Higher coefficients have bounded
slot valence.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Roof
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {I : Type*} [Fintype I][DecidableEq I]
abbrev Pennants (I:Type*) := Matrix I I Pence
variable {s w:I→ℕ}{T W : Matrix I I Pence}{b : I → ℝ}
structure Colfax (s w:I→ℕ)(T: Matrix I I Pence)(b:I→ℝ): Prop where
   bound : ∀ i j e, s j+e<s i → coeff e (T i j)=0
   paid : ∀ i, 0 < b i
   diagonal : ∀ i j,s i=s j → w i ≤ w j → coeff 0 (T i j)= if i=j then b j else 0
omit [Fintype I] in
lemma Colfax.peers (h:Colfax s w T b)(i j:I)(hP: coeff 0 (T i j)≠0)(hz:i≠j): s i<s j ∨ s i=s j∧ w j<w i:= by
   have he: s i≤s j:=le_of_not_gt fun p=>hP (h.bound i j 0 p)
   by_cases hw : s i=s j
   · exact Or.inr ⟨hw, lt_of_not_ge fun P=>hP ((h.diagonal _ _ hw P).trans (if_neg hz))⟩
   exact Or.inl (by omega)
omit [Fintype I] in
lemma Colfax.due (h:Colfax s w T b)(i:I) : coeff 0 (T i i)=b i:= by rw [h.diagonal i i rfl le_rfl,if_pos rfl]
omit [DecidableEq I] in
lemma summed (σ:Equiv.Perm I)(s:I→ℕ)(h:∀ i,s (σ i)≤ s i) : ∀ i,s (σ i)=s i:= by
    intro i; by_contra he; have h': ∑ i,s (σ i)<∑ i,s i:= Finset.sum_lt_sum (fun i _=>h i) ⟨i,Finset.mem_univ _,lt_of_le_of_ne (h i) he⟩; rw [Equiv.sum_comp] at h'; exact lt_irrefl _ h'
lemma pall (h:Colfax s w T b): constantCoeff T.det=∏ i,b i:= by
   let Q:=constantCoeff (R:=ℝ); let A:=Q.mapMatrix T; have he i j : A i j=coeff 0 (T i j):= (coeff_zero_eq_constantCoeff_apply _).symm
   rw [RingHom.map_det]; change A.det= _; rw [Matrix.det_apply, Finset.sum_eq_single 1]; swap
   · intro σ _ hv
     by_cases hp: ∃ i,A (σ i) i=0
     · obtain ⟨i,hi⟩:= hp; rw [Finset.prod_eq_zero (f:=fun i=> A (σ i) i) (Finset.mem_univ _) hi,smul_zero]
     push Not at hp
     have hh i : s (σ i)=s i := summed σ s (fun i=> le_of_not_gt fun h'=>hp i ((he _ _).trans (h.bound _ i 0 h'))) _
     have hx i : w i ≤ w (σ i):= by by_cases p:σ i=i; rw [p]; exact (((h.peers _ i (by rw [←he]; exact hp i) p).resolve_left (not_lt.mpr (hh i).ge)).2).le -- `rw`?;
     have hg i : w (σ i)=w i:=by
         have hv k:w (σ.symm k)≤ w k:=by simpa only [σ.apply_symm_apply] using hx (σ.symm k)
         simpa only [σ.symm_apply_apply] using (summed σ.symm w hv (σ i)).symm
     exact False.elim (hv (Equiv.ext fun i=> by by_contra hz; exact lt_irrefl _ (((h.peers _ i (by rw [←he]; exact hp i) hz).resolve_left (not_lt.mpr (hh i).ge)).2.trans_le (hg i).le)))
   swap; · simp
   simp_rw [map_one,one_smul, Equiv.Perm.one_apply,he,h.due]
lemma Colfax.det (h:Colfax s w T b): IsUnit T.det:= isUnit_iff_constantCoeff.mpr ((pall h).symm ▸ isUnit_iff_ne_zero.mpr (ne_of_gt (Finset.prod_pos (fun i _=> h.paid i))))

-- Combined well-order for leading personnel induction. Smaller slots,
-- then bigger weight. Enumerate ties independently.
def priority (s w : I→ℕ)(i:I) := (Finset.univ.filter (fun j=> s j < s i ∨ s j = s i ∧ w i < w j)).card
omit [DecidableEq I] in
lemma promotes {i j:I}(h:s i< s j ∨ s i=s j ∧ w j<w i): priority s w i < priority s w j:= by
    let V(k:I) := Finset.univ.filter (fun q:I=> s q < s k ∨ s q=s k∧ w k<w q)
    apply Finset.card_lt_card (show V i ⊂ V j from ?_); rw [Finset.ssubset_iff_subset_ne]; refine ⟨fun k hk=>Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,fun H=>?_⟩
    · have hp := (show s k<s i ∨ _ from (Finset.mem_filter.mp hk).2); omega
    have he : i∈ V i:= H.symm ▸ (show i∈ V j from Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    have hp := (show s i<s i ∨ _ from (Finset.mem_filter.mp he).2); omega
end YM.FormalBulk08.Roof
