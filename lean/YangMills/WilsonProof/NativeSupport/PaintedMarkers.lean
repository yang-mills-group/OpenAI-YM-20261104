import YangMills.WilsonProof.NativeSupport.MarkerSubstitution

/-! One temporary old bit and one temporary tangent bit per original
primitive. The target is its original marker times at most one common
tangent. All nonlinear prices use the same finite colored census. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Painted
open Finset Marker Extra.Trajectories Packet MarkerSubstitution
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Ink (V : Type*) := V × Bool × Bool
def support (p : Ink V) : Finset (Option V) :=
  insert (some p.1) (if p.2.2 then {none} else ∅)
def gen (p : Ink V) : Poly (Stock.census (Option V)) := Poly.send (tag (support p)) 1

theorem nil (p : Ink V) : gen p*gen p=0 := by
  by_contra ne
  obtain ⟨_,di,_⟩ := merges_of_tagged_mul ne
  exact disjoint_left.mp di (mem_insert_self (some p.1) _) (mem_insert_self (some p.1) _)

def forget := hom (gen (V:=V)) nil

def paint (y : V) (old tangent : Bool) : V ↪ Ink V :=
  ⟨fun v => (v,if v=y then (old,tangent) else (false,false)),
    fun _ _ h => congrArg Prod.fst h⟩

omit [Fintype V] in
private lemma ordinary (i : V) (p : Ink V) : some i∈support p ↔ i=p.1 := by
  unfold support; cases p.2.2 <;> simp

omit [Fintype V] in
private lemma differentiated (p : Ink V) : none∈support p ↔ p.2.2=true := by
  unfold support; cases p.2.2 <;> simp

theorem restores (S : Finset V) (y : V) (hy : y∈S) (old tangent : Bool) (c : ℂ) :
    forget (Poly.send (tag (S.map (paint y old tangent))) c) =
      Poly.send (tag ((S.image some) ∪ if tangent then {none} else ∅)) c := by
  let e := paint y old tangent
  let z (x : V) := tag (support (e x))
  have output (x : V) : (e x).1=x := rfl
  have tangent_iff (x : V) : (e x).2.2=true ↔ x=y ∧ tangent=true := by
    unfold e paint; by_cases h : x=y <;> simp [h]
  have compatible : Fits z S := by
    refine ⟨?_,mem_univ _⟩
    intro i _ j _ ne
    apply disjoint_left.mpr
    intro k h₁ h₂
    cases k with
    | none =>
      exact ne (((tangent_iff i).mp ((differentiated _).mp h₁)).1.trans
        ((tangent_iff j).mp ((differentiated _).mp h₂)).1.symm)
    | some k =>
      exact ne (((ordinary _ _).mp h₁).symm.trans ((ordinary _ _).mp h₂))
  have id : unionTag z S compatible=tag ((S.image some) ∪ if tangent then {none} else ∅) := by
    apply Subtype.ext
    change S.biUnion (fun x => support (e x))=_
    ext u
    cases u with
    | none =>
      simp only [mem_biUnion,differentiated,tangent_iff,mem_union,mem_image,Option.some_ne_none,
        and_false,exists_false,false_or]
      cases tangent <;> simp [hy]
    | some u =>
      simp only [mem_biUnion,ordinary,output,mem_union,mem_image,Option.some.injEq]
      cases tangent <;> simp
  change applyTo gen (Poly.send (tag (S.map e)) c) = _
  rw [on_send,prod_map]
  change c • (∏ i ∈ S, Poly.send (z i) 1)=_
  rw [tagged_prod z S compatible,id,Finset.prod_const_one]
  ext s; rw [Poly.part_smul,Poly.part_send,Poly.part_send]; split <;> simp

def weight (w : V→ℝ) (A B : ℝ) (born : Finset V) (p : Ink V) :=
  w p.1 * (if p.2.1 then A else 1) * (if p.1∈born then B else 1)

theorem price (S : Finset (Ink V)) (w : V→ℝ) (A B : ℝ) (born : Finset V)
    (live : (∏ p∈S, gen p)≠0) :
    (∏ p∈S,weight w A B born p) =
      (∏ x∈S.image Prod.fst,w x)*A^(S.filter (fun p => p.2.1)).card*
        B^(S.filter (fun p => p.1∈born)).card := by
  have fit := fits_of_tagged_prod (R:=Stock.census (Option V)) (fun p : Ink V=>tag (support p)) live
  have inj : Set.InjOn Prod.fst (S : Set (Ink V)) := by
    intro p hp q hq h
    by_contra ne
    exact disjoint_left.mp (fit.1 hp hq ne) (mem_insert_self (some p.1) _)
      ((ordinary _ _).mpr h)
  have count (u : Ink V→Prop) [DecidablePred u] (z : ℝ) :
      (∏ p∈S, if u p then z else 1) = z^(S.filter u).card := by
    rw [← prod_filter,prod_const]
  simp only [weight,prod_mul_distrib,count]
  rw [prod_image (fun _ h₁ _ h₂ eq=>inj h₁ h₂ eq)]

end YM.Integration.InletSusceptibility.Painted
