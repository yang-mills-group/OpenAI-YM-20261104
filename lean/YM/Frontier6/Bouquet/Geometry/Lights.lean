import YM.Frontier6.Bouquet.Geometry.Jacobi
import YM.Frontier6.Bouquet.Ensemble.Disjoint
/-! Coordinate identities and orthogonal frames through refinements -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble
open scoped Topology BigOperators Classical InnerProductSpace lp
variable {P Q: Ensemble}{p q:Pod}{x y: Room}
lemma normal_rank (p:Pod): dim (normal p)= 4*(p.card-1):=by
    have hs:= fiber_dim (only p); rw [along_only,show #(only p).choose=1 from card_singleton _] at hs; change 4*_+dim (normal p)=4*p.card at hs; have:=p.card_pos; omega
lemma mass_disjoint {A B:Finset Slot}(h:x∈ entire A)(he:Disjoint A B) : mass B x=0:=by rw [mass_eq]; exact sum_eq_zero fun i hi=> h i (fun hh=> Finset.disjoint_left.mp he hh hi)
lemma normal_sub (h:p ≤ q): normal p ≤ normal q:=by intro x hx; rw [normal_iff] at *; refine ⟨entire_le h hx.1,?_⟩; rw [mass_eq]; exact (Finset.sum_subset h (fun i hi he=> hx.1 i he)).symm.trans ((mass_eq _ _).symm.trans hx.2)
lemma normal_off (h:x∈ normal p)(i:Slot)(he:i∉p.val): x i=0:= ((normal_iff _ _).mp h).1 i he
lemma home_sub (h:p∈P.choose): normal p ≤ fiber P:=by
   intro x hx; obtain ⟨hx,hp⟩:= (normal_iff _ _).mp hx; rw [fiber_iff]; refine ⟨entire_le (listed _ _ h) hx, fun q hq=> ?_⟩; by_cases he:p=q; exact he ▸ hp; exact mass_disjoint hx (P.pairwise h hq he)
lemma plan_sub (he:P ≤ Q): fiber P ≤ fiber Q:=by
   intro x hx; obtain ⟨h,hx⟩:= (fiber_iff _ _).mp hx; rw [fiber_iff]; refine ⟨ref_slots he ▸ h,fun q hq=> ?_⟩; let F:= P.choose.filter fun p=> p ≤ q
   have hh:F.biUnion (fun p=>p.val) = q.val:=by
       ext i; rw [Finset.mem_biUnion]; constructor
       · rintro ⟨p,hp,hh⟩; exact (Finset.mem_filter.mp hp).2 hh
       intro hi; obtain ⟨p,hp,H⟩:= (mem_along P i).mp ((ref_slots he) ▸ (listed _ _ hq hi)); exact ⟨p, Finset.mem_filter.mpr ⟨hp,not_cross he hp hq H hi⟩,H⟩
   rw [mass_eq,← hh,sum_biUnion]; exact sum_eq_zero fun p hp=> (mass_eq ..).symm.trans (hx p (mem_of_mem_filter p hp)); -- implicit ? exact
   intro i hi j hj he; exact P.pairwise (mem_of_mem_filter _ hi) (mem_of_mem_filter _ hj) he
lemma tie_eq {i j:Slot}(h:y∈ (normal p)ᗮ)(hi:i∈ p.val)(hj:j∈ p.val): y i=y j:=by
   let a:= y i-y j; let z:= occupant i a-occupant j a
   have he:z∈ normal p:= (normal_iff _ _).mpr ⟨Submodule.sub_mem _ (entire_solo hi _) (entire_solo hj _), by unfold z; rw [map_sub,mass_in hi,mass_in hj,sub_self]⟩
   have hv:= Submodule.inner_right_of_mem_orthogonal he h; unfold z at hv; rw [inner_sub_left,occupant_inner,occupant_inner,← inner_sub_right] at hv; exact sub_eq_zero.mp ((inner_self_eq_zero.mp (show ⟪a,a⟫_ℝ=0 from hv)))
lemma tie_up (y:Room)(h:∀ i∈p.val,y i=y p.here): y∈ (normal p)ᗮ:=by
   intro v hv; obtain ⟨hp,hv'⟩:=(normal_iff _ _).mp hv
   rw [written v hp, sum_inner]; rw [sum_congr rfl (g:=fun i=>⟪v i, y p.here⟫_ℝ) (fun i hi=>by rw [occupant_inner,h i hi]), ← sum_inner,← mass_eq p.val v, hv',inner_zero_left]
lemma pod_centroid (hi:y ∈ (normal p)ᗮ) (i:Slot)(h:i∈p.val): centroid p y=y i:=by
   unfold centroid; rw [ContinuousLinearMap.smul_apply, mass_eq, sum_congr rfl (g:=fun j=>y i) (fun j hj=> tie_eq hi hj h), sum_const]; change (p.card:ℝ)⁻¹ • (p.card • y i)=_; have hp:(p.card:ℝ) ≠ 0:= by exact_mod_cast p.card_pos.ne'
   rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul,inv_mul_cancel₀ hp,one_smul] -- name
lemma whole_free {A B:Finset Slot}(h:Disjoint A B) : entire A ≤ (entire B)ᗮ:=by
   intro x hx y hy; rw [written y hy,sum_inner]; refine sum_eq_zero fun i hi=>?_ ; rw [occupant_inner,hx i (fun hh=> Finset.disjoint_left.mp h hh hi),inner_zero_right] -- implicit At anno
lemma normal_orth (h:Disjoint p.val q.val) : normal p ≤ (normal q)ᗮ:= by
    exact le_trans (fun x hx=> ((normal_iff _ x).mp hx).1) ((whole_free h).trans (Submodule.orthogonal_le (fun x hx=> ((normal_iff _ _).mp hx).1)))
lemma frame_orth (h: Free P Q): fiber P ≤ (fiber Q)ᗮ:= le_trans (fiber_entire P) ((whole_free h).trans (Submodule.orthogonal_le (fiber_entire _)))
end YM.Frontier6.Bouquet
