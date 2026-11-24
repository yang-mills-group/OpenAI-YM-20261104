import YM.RG.Activities

/-! A spatial cut of a compulsory physical roster. The two regional
admission tests cover exactly their portions of the full original flag
set. Disjointness is checked on physical supports, not just inventories. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Finset Lattice RG Wilson
open scoped Classical
variable {G:Gauge}{n:Side}

abbrev Pool (classify:ℕ→Prop):={L:Finset ℕ // ∀i∈L,classify i}

def combine (c:ℕ→Prop):Pool c × Pool (fun i=>¬c i) ≃ Finset ℕ where
  toFun r:=r.1.val∪r.2.val
  invFun S:=(⟨S.filter c,fun _ hi=>(mem_filter.mp hi).2⟩,
    ⟨S.filter (fun i=>¬c i),fun _ hi=>(mem_filter.mp hi).2⟩)
  left_inv r:=by
    apply Prod.ext <;> apply Subtype.ext
    · ext i
      change i∈(r.1.val∪r.2.val).filter c ↔ i∈r.1.val
      constructor
      · intro hi
        obtain ⟨hit,belongs⟩:=mem_filter.mp hi
        exact (mem_union.mp hit).resolve_right (fun h=>(r.2.property i h) belongs)
      · intro hi
        exact mem_filter.mpr ⟨mem_union_left _ hi,r.1.property i hi⟩
    · ext i
      change i∈(r.1.val∪r.2.val).filter (fun j=>¬c j) ↔ i∈r.2.val
      constructor
      · intro hi
        obtain ⟨hit,away⟩:=mem_filter.mp hi
        exact (mem_union.mp hit).resolve_left (fun h=>away (r.1.property i h))
      · intro hi
        exact mem_filter.mpr ⟨mem_union_right _ hi,r.2.property i hi⟩
  right_inv S:=by
    ext i
    simp only [mem_union,mem_filter]
    by_cases h:c i <;> simp [h]

theorem pools_disjoint (c:ℕ→Prop)(a:Pool c)(b:Pool (fun i=>¬c i)):
    Disjoint a.val b.val:=disjoint_left.mpr fun i ia ib=>(b.property i ib) (a.property i ia)

def Regional (B:Activities G n)(E:Support n)(S:Finset ℕ):Prop:=
  (S:Set ℕ).Pairwise (fun i j=>Disjoint (B.forced i).support (B.forced j).support) ∧
    S.biUnion (fun i=>(B.forced i).inventory)=E

private theorem divide_flags (D F X Y:Support n)(xin:X⊆D)(out:Disjoint Y D):
    X∪Y=F ↔ X=F∩D ∧ Y=F\D:=by
  constructor
  · intro equal
    rw [←equal]
    constructor
    · ext z
      constructor
      · intro hz; exact mem_inter.mpr ⟨mem_union_left _ hz,xin hz⟩
      · intro hz
        obtain ⟨belongs,within⟩:=mem_inter.mp hz
        exact (mem_union.mp belongs).resolve_right fun h=>disjoint_left.mp out h within
    · ext z
      constructor
      · intro hz; exact mem_sdiff.mpr ⟨mem_union_right _ hz,disjoint_left.mp out hz⟩
      · intro hz
        obtain ⟨belongs,away⟩:=mem_sdiff.mp hz
        exact (mem_union.mp belongs).resolve_left fun h=>away (xin h)
  rintro ⟨rfl,rfl⟩
  ext z
  by_cases h:z∈D <;> simp [h]

/-- Separate all admissible rosters on the actual original field at a
physical cut, including the entire unmarked denominator. -/
theorem true_cut_admission (B:Activities G n)(p:BudgetPoint)(U:Config G n)(D:Support n)
    (X Y:Finset ℕ)(inside:∀i∈X,(B.forced i).support⊆D)
    (outside:∀i∈Y,Disjoint (B.forced i).support D):
    B.admissible p U (X∪Y) ↔
    Regional B (flags p.threshold U∩D) X ∧ Regional B (flags p.threshold U\D) Y:=by
  let inv:=fun i=>(B.forced i).inventory
  have left:X.biUnion inv⊆D:=by
    intro z hz
    obtain ⟨i,ix,zi⟩:=mem_biUnion.mp hz
    exact inside i ix ((B.forced i).inventory_sup zi)
  have right:Disjoint (Y.biUnion inv) D:=by
    apply disjoint_left.mpr
    intro z hz
    obtain ⟨i,iy,zi⟩:=mem_biUnion.mp hz
    exact disjoint_left.mp (outside i iy) ((B.forced i).inventory_sup zi)
  have mask:=divide_flags D (flags p.threshold U) _ _ left right
  have apart (i j:ℕ)(ix:i∈X)(jy:j∈Y): Disjoint (B.forced i).support (B.forced j).support:=
    disjoint_left.mpr fun _ hi hj=>disjoint_left.mp (outside j jy) hj (inside i ix hi)
  constructor
  · rintro ⟨spatial,covered⟩
    obtain ⟨a,b⟩:=mask.mp ((Finset.union_biUnion (s₁:=X) (s₂:=Y) (t:=inv)).symm.trans covered)
    exact ⟨⟨fun _ h _ k=>spatial (mem_union_left _ h) (mem_union_left _ k),a⟩,
      ⟨fun _ h _ k=>spatial (mem_union_right _ h) (mem_union_right _ k),b⟩⟩
  rintro ⟨⟨x,xf⟩,⟨y,yf⟩⟩
  refine ⟨?_,(Finset.union_biUnion (s₁:=X) (s₂:=Y) (t:=inv)).trans (mask.mpr ⟨xf,yf⟩)⟩
  intro i hi j hj ne
  rcases mem_union.mp hi with ix|iy <;> rcases mem_union.mp hj with jx|jy
  · exact x ix jx ne
  · exact apart i j ix jy
  · exact (apart j i jx iy).symm
  exact y iy jy ne

end YM.Integration.FVA1Physical.Exchange.RoseCut
