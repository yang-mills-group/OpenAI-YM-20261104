import YM.Frontier6.Bouquet.Geometry.Tandem

/-! Forests of macro projections. Dimensions for a split and for two nested refinements. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Submodule
open scoped Topology BigOperators Classical InnerProductSpace lp
open scoped YM.Frontier6.Bouquet
variable {P Q R:Place}
def Loft (P Q:Place):Place:=Qᗮ ⊓ P
instance (P Q:Place) [FiniteDimensional ℝ P]: FiniteDimensional ℝ (Loft P Q):= Submodule.finiteDimensional_of_le (S₁:=Loft P Q) (inf_le_right : _≤P)
instance (P Q:Place)[FiniteDimensional ℝ P]: ProperSpace (Loft P Q):= FiniteDimensional.proper ℝ _
instance (P Q:Place)[FiniteDimensional ℝ P]: CompleteSpace (Loft P Q):= FiniteDimensional.complete ℝ _
lemma loft_orth : Loft P Q ≤ Qᗮ:= inf_le_left
lemma loft_le : Loft P Q ≤ P:= inf_le_right
lemma attendance [FiniteDimensional ℝ Q](h:P≤Q) : Tandem P (Loft Q P) Q:= by
    letI := Submodule.finiteDimensional_of_le h; exact ⟨loft_orth, Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection h⟩
lemma tandem_from [FiniteDimensional ℝ R][FiniteDimensional ℝ P][FiniteDimensional ℝ Q](he:P≤R)(hv:Q≤R)(h:Q≤Pᗮ)(hp:dim P+dim Q=dim R) : Tandem P Q R:=by
    have hr:= sup_le he hv; exact ⟨h,eq_of_le_of_finrank_eq hr ((Tandem.dim_eq (show Tandem P Q (P⊔Q) from ⟨h,rfl⟩)).symm.trans hp)⟩
section
variable [FiniteDimensional ℝ P][FiniteDimensional ℝ Q][FiniteDimensional ℝ R] (h:P≤Q)(he:Q≤R)
include h he
lemma bridges : Tandem (Loft R Q) (Loft Q P) (Loft R P) :=by
    apply tandem_from
    · exact le_inf (loft_orth.trans (orthogonal_le h)) loft_le
    · exact le_inf loft_orth (loft_le.trans he)
    · intro x hx y hy; exact inner_left_of_mem_orthogonal (loft_le hx) (loft_orth hy)
    have hv:= Tandem.dim_eq (attendance h); have hp:= Tandem.dim_eq (attendance he); have ht:= Tandem.dim_eq (attendance (h.trans he)); omega
end
section
variable {A B A' B': Ensemble} (he:Free A B)
lemma merged_left : fiber A ≤ fiber (merge he):=by
    intro x hx; obtain ⟨hx,h⟩:= fiber_iff _ x|>.mp hx; rw [fiber_iff]; refine ⟨entire_le (show _ ⊆ Along (merge he) by rw [along_merge]; exact subset_union_left) hx,fun p hp=>?_⟩; rcases Finset.mem_union.mp hp with hP|hP; exacts [h p hP,mass_disjoint hx (Disjoint.mono_right (listed _ _ hP) he)]
lemma merge_commutes : merge he= merge he.symm:= Ensemble.ext (union_comm ..)
lemma merged : Tandem (fiber A) (fiber B) (fiber (merge he)):=by
   apply tandem_from (merged_left he) (by rw [merge_commutes he]; exact merged_left he.symm) (frame_orth he.symm); have h1:= fiber_dim A; have h2:=fiber_dim B; have h:=fiber_dim (merge he); rw [rank_merge,along_merge,Finset.card_union_of_disjoint he] at h; omega
lemma adds_macro {K:Free A' B'}(hN:A' ≤ A)(hM:B' ≤ B) : Tandem (Loft (fiber A) (fiber A')) (Loft (fiber B) (fiber B')) (Loft (fiber (merge he)) (fiber (merge K))):=by
    let X:=fiber (merge he); let Y:= fiber (merge K); let P:=fiber A; let Q:=fiber B; let U:=fiber A'; let V:=fiber B'
    have hx := merged he; have hy := merged K; have hU:=plan_sub hN; have hV:=plan_sub hM
    have ht : Y≤ X:=plan_sub (merge_le he hN hM)
    have hP : (fiber (merge K))ᗮ=Uᗮ⊓Vᗮ:=by rw [← hy.full,← Submodule.inf_orthogonal]
    refine tandem_from (le_inf ?_ (loft_le.trans hx.lft)) (le_inf ?_ (loft_le.trans hx.rgt)) (loft_le.trans (hx.orth.trans (orthogonal_le loft_le))) ?_
    · rw [hP]; exact le_inf loft_orth (loft_le.trans (hx.symm.orth.trans (orthogonal_le hV)))
    · rw [hP]; exact le_inf (loft_le.trans (hx.orth.trans (orthogonal_le hU))) loft_orth
    have h1:= (attendance hU).dim_eq; have h2:= (attendance hV).dim_eq; have h3:= hx.dim_eq; have h4:= hy.dim_eq; have h5:= attendance (show fiber (merge K)≤ fiber (merge he) from ht) |>.dim_eq; omega
abbrev Margin (A B:Ensemble):= Loft (fiber A) (fiber B)
lemma margin_rank (h:A ≤ B): dim (Margin B A) + 4*B.choose.card=4*A.choose.card:=by
   have he:= fiber_dim A; have hv:= fiber_dim B; have hP:= attendance (plan_sub h)|>.dim_eq; unfold Margin; rw [ref_slots h] at he; omega
end
end YM.Frontier6.Bouquet
