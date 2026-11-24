import YM.OPE.Compatible.Dale.Slot
/-!
# Block forest gauging. Imported uniformly into fin-reg Stand notation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade
open Function Filter Set Lattice Laurent Tree Woody Weir MeasureTheory
open scoped Topology BigOperators ComplexConjugate Classical
variable {n c f:Side} (g:Ratio c f) (hp:Even c.val)(he:Odd g.count.val)
local notation "μ" => even_both g hp
local notation "X" => forest g he
abbrev Reed := (Pond μ).Stand (Roots g hp)
lemma footed (p: ↥((Roots g hp)ᶜ)): leaf g p.val.val := (root_bud g hp _).mp (by rw [show crumb μ p.val.val=p.val from See.king_here ..]; exact p.property)
lemma hit_at (x:Site f): (forest g he).height (crumb μ x).val = (forest g he).height x := by
     obtain ⟨i,h⟩:= (sitesK μ).joint x; let p := crumb μ x; change decks i p.val=x at h
     change size (lift (g.residue p.val)) = _; nth_rw 1 [← h]
     rw [show (forest g he).height _=size (lift (g.residue (decks i p.val))) from rfl,(step_parent g hp he ..).2,Ratio.lift_signed_of_odd he]; -- size signed
     unfold size; apply Finset.sum_congr rfl; intro j _; nth_rw 2 [← axis_pin i j]; rw [Signed.act_at]; split <;>simp
def vforest (he : Odd g.count.val): Reed g hp where
    point i := forward μ ((forest g he).up i.val.val) i.val.val
    flick i:= (forest g he).height i.val
    root i:= (stairs μ _ _).1.trans (See.king_here ..)
    bump i:=by rw [(stairs μ _ _).2,hit_at g hp he]; exact (forest g he).rise i.val.val (footed g hp i)
lemma rooted_branch {p:Limb μ} (hx:(vforest g hp he).Branch p) : p.val ∈ (forest g he).trunks:=by
      obtain ⟨i,hi⟩:=hx
      let x:=i.val.val; let q:= ((forest g he).up x).used x; change pathX μ q=p at hi; have hy:q∈ (forest g he).trunks:= ((forest g he).trunk_mem_iff ..).mpr ⟨x,footed g hp i,rfl⟩; let k:= (edgesK μ).tick q; have hh : ferry k p.val=q:=by rw [←hi]; exact (resettle μ q).symm
      have hr:= staff_at g hp he k q hy; rw [←hh] at hr -- q occurs?
      rw [← ferry_plus μ,twinned,ferry_0] at hr; exact hr
lemma branch_alike (x:Site f)(h:leaf g x): (vforest g hp he).Branch (pathX μ (((forest g he).up x).used x)):=by
      let i := crumb μ x; have hi:i∈ (Roots g hp)ᶜ:= (root_bud g hp _).mpr h; let u: ↥((Roots g hp)ᶜ):=⟨i,hi⟩; refine ⟨u,?_⟩; let k:= (sitesK μ).tick x; have heX: x= decks k i.val:= ((sitesK μ).ticket _).symm; have ha:=footed g hp u
      change pathX μ (((forest g he).up i.val).used i.val) =_; rw [heX, (winch g hp he k i.val ha).2,← ferry_read,path_ferry]
lemma branch_rep {p:Limb μ} : (vforest g hp he).Branch p ↔ p.val∈ (forest g he).trunks:=by
      refine ⟨rooted_branch g hp he,?_⟩; rw [(forest g he).trunk_mem_iff]; rintro ⟨i,hi,hx⟩; have hv:= branch_alike g hp he i hi; rw [hx,path_id] at hv; exact hv
lemma hike_same (p: ↥((Roots g hp)ᶜ)) : FollowV g hp ((Pond μ).lastV ((vforest g hp he).point p))=FollowV g hp p.val:=by
      dsimp only [vforest]; rw [(show _ = _ from (stairs μ ((forest g he).up p.val.val) p.val.val).2),parent_node g hp he,(forest g he).stays p.val.val (footed g hp p)]
end YM.OPE.Cascade
