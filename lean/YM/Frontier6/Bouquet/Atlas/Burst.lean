import YM.Frontier6.Bouquet.Atlas.Gem

/-!
# Split at one frontier point only. Keep others' planes exactly,
 not moving the other transaction centers for different-scale tails.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter Metric Submodule
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff
open scoped YM.Frontier6.Bouquet
variable {P Q : Ensemble}{i:P}
structure Burst (i:P)(Q:Ensemble): Prop where
   le : Q ≤ P
   broken : i.val∉ Q.choose
   holds : ∀ j:P,j≠i→ j.val∈ Q.choose
namespace Burst
variable (h:Burst i Q)
include h
lemma strict : Q<P:= lt_of_le_of_ne h.le (fun he=> h.broken (he ▸ i.property))
def remembers (j:P)(he:j≠i): Q:= ⟨j.val,h.holds j he⟩
lemma remembered {j:P}(he:j≠i): assign h.le (h.remembers j he)=j:= assigned _ _ _ (le_refl j.val)
lemma same_pod {j:P}{u:Q}(hh:assign h.le u=j)(he:j≠i): u=h.remembers j he:= serial Q u.val.here_mem (hh ▸ inside h.le u u.val.here_mem) -- cast?
lemma bedrooms {j:P}(he:j≠i): dialogues h.le j={h.remembers j he}:=by
    ext1 p; simp only [members,Finset.mem_singleton]; exact ⟨fun hp=> h.same_pod hp he,fun eq=>eq ▸ h.remembered he⟩
lemma closer {p:Q}(he: assign h.le p=i): p.val < i.val:= lt_of_le_of_ne (he ▸ inside h.le p) (fun H=>h.broken (H ▸ p.property))
lemma move_suppressed (x:Seats P)(z:Margin P Q)(j:P)(he:j≠i): transit h.le x z (h.remembers j he)=x j:=by
    -- orth near margin gives equal position offsets, their weighted centroid sum zero
    unfold transit; rw [h.remembered he]; exact (congr_arg (·+x j) (centroid_empty j ((insideCL loft_le z):fiber P))).trans (zero_add _)
lemma margin_local : Margin P Q ≤ normal i.val:=by
    intro x hx; let y:fiber P:=⟨_,loft_le hx⟩; refine (normal_iff _ _).mpr ⟨?_,mass_missing i y⟩; intro z hz;
    by_cases hk:z∈ Along P; swap; exact fiber_entire _ y.property z hk;
    obtain ⟨p,hp,H⟩:=mem_along _ z|>.mp hk; let j:P:=⟨p,hp⟩; have hp:j≠i:=fun he=>hz (he ▸ H); -- h shadows h!
    let v:Q:= Burst.remembers h j hp; have hv:x∈ (normal v.val)ᗮ:= orthogonal_le (home_sub v.property) (loft_orth hx); exact (pod_centroid hv _ H).symm.trans (centroid_empty j y)
lemma margin_rune (u:fiber P)(v:fiber Q)(y: Margin P Q)(hy:u=forward (plan_sub h.le) (insideCL loft_le y) v): ‖y‖≤ ‖rune i u‖:=by
    have hh:ontoSpace (Margin P Q) (rune i u).val=y:=by
       rw [show ontoSpace (Margin P Q) (rune i u).val=ontoSpace (Margin P Q) u.val from (on_lower h.margin_local u.val).symm,hy, forward_cast, map_add];
       have ht:v.val∈ (Margin P Q)ᗮ:= (attendance (plan_sub h.le)).symm.orth v.property; rw [on_blank ht,add_zero]; exact on_home y
    exact hh ▸ on_budget (P:=Margin P Q)
lemma refined_size (u:fiber P)(v:fiber Q)(y: Margin P Q)(hy:u=forward (plan_sub h.le) (insideCL loft_le y) v) (q:Q): ‖rune q v‖ ≤ ‖rune (assign h.le q) u‖:= by
    let a := assign h.le q; have hx: ontoSpace (normal q.val) (rune a u).val = rune q v:=by
        rw [show ontoSpace (normal q.val) (rune a u).val=ontoSpace (normal q.val) u.val from (on_lower (normal_sub (inside h.le q)) u.val).symm,hy,forward_cast,map_add]; have ht:y.val∈ (normal q.val)ᗮ:= orthogonal_le (home_sub q.property) (loft_orth y.property); change ontoSpace _ y.val + _= _; rw [on_blank ht,zero_add];rfl
    rw [← hx]; exact on_budget (P:=normal q.val)
end Burst
end YM.Frontier6.Bouquet
