import YM.FVA2.Edges

/-! Actual quotient tree rank (for the concrete canonical slice). -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Inversion
open Finset Matrix Set Function Filter Lattice MS.Koszul MS.Native
open PertExtension PertExtension.Orb
open Ends ArrayMap
open scoped Topology ContDiff Classical

variable {E : Type*} {n: Side} {G:Gauge}

def treeAssign (v: Vert n) : Trees n:=⟨picked v.val,v.val,v.property.2,rfl⟩

/-- An oriented tree edge is read from its deeper endpoint orbit. -/
def farther (e:Edge (Site n)) : Site n:=
  if depth (e.1+step e.2) ≤ depth e.1 then vertex e.1 else vertex (e.1+step e.2)
lemma farther_reflect (e:Edge (Site n)) (h : depth e.1≠depth (e.1+step e.2)) :
    farther (reflect e)=farther e := by
  unfold farther reflect; dsimp only; rw [sub_add_cancel,
    show -e.1-step e.2= -(e.1+step e.2) from (by abel),depth_neg,depth_neg,vertex_neg,vertex_neg]
  split_ifs <;> first| rfl| omega
lemma precedes {x:Site n} {d: Step} (h : Falls x d) :
    farther (Orb.index (d.used x)).val=vertex x := by
  let e:=d.used x
  have hh : farther e=vertex x ∧ depth e.1 ≠ depth (e.1+step e.2) := by
    change farther (d.used x)=_∧ _
    unfold e at *
    unfold Falls at h
    rcases d with ⟨i,hx|hx⟩
    · change (if depth (x+step i) ≤ depth x then _ else _)=_ ∧
        depth x≠ depth (x+step i)
      rw [if_pos (show depth (x+step i) ≤ depth x from h.le)]
      exact ⟨rfl, (Nat.ne_of_lt h).symm⟩
    change depth (x + -step i) < depth x at h
    rw [← sub_eq_add_neg] at h
    unfold farther; simp only [Step.used, ↓reduceIte];
    rw [sub_add_cancel, if_neg (by omega)]; exact ⟨rfl, Nat.ne_of_lt h⟩
  change farther (eR e)=_
  rcases eR_spec e with H|H
  · rw [H]; exact hh.1
  rw [H,farther_reflect _ hh.2]; exact hh.1

lemma assigns : Bijective (treeAssign (n:=n)) := by
  constructor
  · intro x y h
    apply Subtype.ext; obtain he:=congr_arg (fun z:Trees n=>farther z.val.val) h
    have hu (x: Vert n) : farther (treeAssign x).val.val=x.val:= (precedes (move_falls x.property.2)).trans x.property.1
    exact (hu x).symm.trans (he.trans (hu y))
  · intro e
    obtain ⟨x,hx,h⟩:=e.property
    exact ⟨⟨vertex x,vertex_vertex x,(fun h=>hx (vertex_eq_iff.mp h))⟩,
      Subtype.ext ((picked_rep x).symm.trans h)⟩

abbrev assign (n:Side) := Equiv.ofBijective (treeAssign (n:=n)) assigns

def pick {A:Type} (B:A→Prop) : Ends.Links G A →ₗ[ℝ] Ends.Links G {x : A // B x} :=
  LinearMap.pi fun i=> LinearMap.proj i.val

lemma tree_injective (he : Even n.val) :
    Injective ((pick Orb.Branch) ∘ₗ ((root n).flow (0:RootX G n))) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  obtain h:= LinearMap.mem_ker.mp hx
  let v := pin G n x
  let T := (root n).flow 0 x
  have hi (a: Site n)(ha:a≠0) :
      v a=v (a+(move a).vec) := by
    let e:=(move a).used a
    have ht : T (index e)=0:= congr_fun h (⟨index e,a,ha,rfl⟩ : Trees n)
    have hv : incl G n T e=0:=by unfold incl; simp only [LinearMap.coe_mk, AddHom.coe_mk, ht,neg_zero, ite_self]
    rw [show incl G n T= _ from root_gradient he x,fullEnd0] at hv
    have hp : v (e.1+step e.2)=v e.1:= sub_eq_zero.mp hv
    unfold e at hp
    rcases H:move a with ⟨i,b|b⟩ <;> rw [H] at hp
    · exact hp.symm
    simp only [Step.used, ↓reduceIte,sub_add_cancel] at hp
    change _=v (a + -step i)
    rwa [← sub_eq_add_neg]
  have hz (a: Site n) : v a=0 := by
    induction k: depth a using Nat.strong_induction_on generalizing a with
    | h j IH =>
      by_cases ha:a=0
      · rw [ha]; exact pin_zero _
      obtain ht:= move_falls ha; rw [hi a ha]; exact IH _ (k ▸ ht) _ rfl
  exact (Submodule.mem_bot ..).mpr (funext fun i=> by rw [← pin_at x i]; exact hz _)

def treeIso (G:Gauge) (he:Even n.val): RootY G n ≃ₗ[ℝ] Ends.Links G (Trees n):=
  let U:= chartBasis G (Vert n)
  let V:= chartBasis G (Trees n)
  let W:RootY G n≃ₗ[ℝ] Ends.Links G (Trees n) := U.trans ((LinearEquiv.piCongrLeft' ℝ (fun _ : Z G (Vert n)=>ℝ) (Equiv.prodCongr (assign n) (Equiv.refl _))).trans V.symm)
  let T:=pick Orb.Branch ∘ₗ ((root n).flow (0:RootX G n))
  have hT : Injective T:= tree_injective he
  LinearEquiv.ofBijective T ⟨hT,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank W.finrank_eq).mp hT⟩

lemma invert_tree (G:Gauge) (he:Even n.val) : (treeIso G he).toLinearMap=pick Orb.Branch ∘ₗ ((root n).flow (0:RootX G n)) := rfl
end YM.FVA2.Inversion
