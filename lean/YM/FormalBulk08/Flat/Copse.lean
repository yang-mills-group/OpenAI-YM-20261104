import YM.FormalBulk08.Flat.Removal

/-!
Fix one tree path convention with any period (including 1), absolutely
relative to *one* coarse root (not equality of periodic evaluations used
for cancellation). `Lodge` rules can include more than one coordinate-order
tree. The specimen uses the first nonzero coordinate, so invertible through
inversion away from the root, should later detector calculations impose it.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Flat
open Filter Set Function Lattice Laurent Bloch Exterior Precision RG Next.Free UVExtension.Free Work.F08 Stationary Tree
open scoped Topology BigOperators Matrix
variable {G : Gauge} {P : Patch} {K : KernelChoices} {c f : Side} {S : StepData c f}

structure Lodge (P : Patch) where
  aim (x : Site P.L) : Step
  lean x : x≠0 → Laurent.size (lift x+(aim x).vec) < Laurent.size (lift x)
  here x : x≠0 → lift x+(aim x).vec ∈ box (P.L.val/2)

private def direction (x : Site P.L) := Finset.univ.filter (fun i : Axis=> lift x i≠0)
private lemma exists_point {x : Site P.L} (h : x≠0) : (direction (P:=P) x).Nonempty := by
  have ht : lift x ≠ 0 := by rw [← lift_origin P.L]; exact lift_inj.ne h
  obtain ⟨k,h⟩:=Function.ne_iff.mp ht
  exact ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
def orderedAxis (P : Patch) (x : Site P.L) (h : x≠0) := (direction (P:=P) x).min' (exists_point h)
def slideTo (P : Patch) (x : Site P.L) : Step :=
  if h:x≠0 then
    let a:= orderedAxis P x h
    if lift x a < 0 then posDir a else negDir a
  else posDir 0
lemma inside (x : Site P.L) (h : x ≠ 0) :
    Laurent.size (lift x+(slideTo P x).vec) < Laurent.size (lift x) ∧ lift x+(slideTo P x).vec ∈ box (P.L.val/2) := by
  let L:=P.L
  let a:= (direction (P:=P) x).min' (exists_point h)
  let y:= lift x
  have hy : y a≠0 := (Finset.mem_filter.mp (Finset.min'_mem (direction (P:=P) x) (exists_point h))).2
  have hd : slideTo P x=(if y a < 0 then posDir a else negDir a) := by rw [slideTo,dif_pos h]; rfl
  let Y:Cover:= lift x+(slideTo P x).vec
  have he (j : Axis) (h:j≠a) : Y j=y j := by unfold Y; rw [hd]; split <;> simp [h,y]
  have hk : (Y a).natAbs < (y a).natAbs := by unfold Y; rw [hd]; split <;> simp <;> unfold y at * <;> omega
  constructor
  · refine (Finset.sum_lt_sum (f:=fun i=> (Y i).natAbs) (g:=fun i=> (y i).natAbs) (fun i _=>?_) ⟨a,Finset.mem_univ _,hk⟩)
    by_cases h:i=a
    · subst i; exact hk.le
    rw [he i h]
  rw [box_test]
  have hY (j : Axis) : (Y j).natAbs ≤ P.L.val/2 := by
    have h (x : Site P.L) (j:Axis) : (lift x j).natAbs≤P.L.val/2 := by
      obtain hh := lift_centers (n:=P.L) x j; omega
    have hh:= h x j
    by_cases hv : j=a
    · subst j; exact hk.le.trans hh
    rw [he j hv]; exact hh
  change (∀ i, _ ≤ Y i) ∧ ∀ i,Y i ≤ _
  constructor <;> intro i <;> specialize hY i <;> omega

def routes (P : Patch) : Lodge P where
  aim := slideTo P
  lean _ h := (inside _ h).1
  here _ h := (inside _ h).2
lemma reversed (P : Patch) (x : Site P.L) (hp : x≠0) : (routes P).aim (-x)= ((routes P).aim x).rev := by
  have hx := neg_ne_zero.mpr hp
  have h := lift_negate x P.odd_side
  have hg : orderedAxis P (-x) hx=orderedAxis P x hp := by
    unfold orderedAxis; congr 1
    unfold direction; rw [h]; simp
  let a := orderedAxis P x hp
  have hh : lift x a≠0 := (Finset.mem_filter.mp (Finset.min'_mem (direction (P:=P) x) (exists_point hp))).2
  unfold routes slideTo; dsimp only; rw [dif_pos hp,dif_pos hx]; rw [hg,h]
  change (if -(lift x a)<0 then posDir a else negDir a) = _
  by_cases H : lift x a<0
  · rw [if_pos H,if_neg (by omega)]; rfl
  rw [if_neg H,if_pos (by omega)]; rfl

namespace Lodge
variable (T : Lodge S.patch)
lemma is_leaf (S : StepData c f) (x : Site f) : leaf S.ratio x ↔ S.ratio.residue x≠0 := not_congr (S.ratio.root_id x)
private lemma moves (x : Site f) (hx : leaf S.ratio x) :
    let d := (T.aim (S.ratio.residue x)).vec
    lift (S.ratio.residue (x+d))= lift (S.ratio.residue x)+(T.aim (S.ratio.residue x)).vec ∧
      S.ratio.parent (x+d)=S.ratio.parent x := S.ratio.internal S.patch.odd_side (T.here _ ((is_leaf S x).1 hx))

def forest : Forest S.ratio where
  up i:= T.aim (S.ratio.residue i)
  height x := Laurent.size (lift (S.ratio.residue x))
  bound x := Finset.sum_le_sum (g:=fun _=> S.ratio.count.val) (fun (i:Axis) _=>by have hh := lift_centers (S.ratio.residue x) i; omega)|>.trans_eq (by simp [Axis])
  rise i h:= (congr_arg _ (T.moves i h).1).trans_lt (T.lean _ ((is_leaf S i).1 h))
  stays i h := (T.moves i h).2

def retain (P : Patch) (T : Lodge P) (x : Site P.L) (k : Axis) :=
    ¬ ∃ y : Site P.L, y ≠ 0 ∧ (T.aim y).used y=(x,k)

lemma repeats (i : Edge (Site f)) : i ∈ T.forest.trunks ↔ ∃ y : Site S.patch.L, y ≠ 0 ∧ (T.aim y).used y=(S.ratio.residue i.1,i.2) := by
  have he (p : Step) (x : Site f) : (p.used (S.ratio.residue x)) = (S.ratio.residue (p.used x).1, (p.used x).2) := by
    rcases p with ⟨a,h|h⟩; · rfl
    unfold Step.used; simp only [↓reduceIte,map_sub]; rw [← (wrap_step a (n:=f)), Ratio.residue_wrap, wrap_step]
  rw [Forest.trunk_mem_iff]; constructor
  · rintro ⟨x,h,rfl⟩; exact ⟨S.ratio.residue x,(is_leaf S x).1 h,he ..⟩
  rintro ⟨x,hx,H⟩
  let y:=S.ratio.assemble (S.ratio.parent i.1,x)
  have hw : S.ratio.residue y=x:=Ratio.assemble_res ..
  have hl : leaf S.ratio y := (is_leaf S _).mpr (hw ▸ hx)
  have hp : T.forest.up y=T.aim x := congr_arg T.aim hw
  rw [← hp] at H
  let J:= T.forest.up y
  have HH : J.used x=(S.ratio.residue i.1,i.2) := H
  have hk : S.ratio.residue (J.used y).1=S.ratio.residue i.1 ∧ (J.used y).2=i.2 := by
    rw [← hw] at HH; exact Prod.mk.inj ((he J y).symm.trans HH)
  have hv : S.ratio.parent (J.used y).1 = S.ratio.parent i.1 := by
    have hh := (T.moves y hl).2; change S.ratio.parent (y+J.vec)=S.ratio.parent y at hh
    have ht : S.ratio.parent y=S.ratio.parent i.1:=S.ratio.assemble_parent _
    cases h : J with
    | mk a n=>
      rw [h] at hh
      cases n
      · exact ht
      change S.ratio.parent (y-step a)= _
      rw [sub_eq_add_neg]; exact hh.trans ht
  refine ⟨y,hl,Prod.ext ?_ hk.2⟩
  apply S.ratio.splitSites.injective; rw [← Ratio.unpack,← Ratio.unpack,hv,hk.1]

-- Alive alphabet over residues.
abbrev selected (G : Gauge) (P : Patch) (T : Lodge P) := {i : Co P.L (Loc G 1) // retain P T i.1 (axisEquiv.symm i.2.1)}
noncomputable instance chosenT (i : Co P.L (Loc G 1)) (U : Lodge P) : Decidable (retain P U i.1 (axisEquiv.symm i.2.1)) := Classical.propDecidable _
lemma occupies (i : Lines G f 1) :
  let x := unitSplit G S 1 i
  lives T.forest i ↔ retain S.patch T x.2.1 (axisEquiv.symm x.2.2.1) := by
    dsimp only; rcases i with ⟨i,j⟩; rw [unitSplit,split_co]; exact not_congr (T.repeats (i,axisEquiv.symm j.1))

def splitting : Alive G S T.forest ≃ Co c (selected G S.patch T) :=
    Equiv.ofBijective (fun x=> ((unitSplit G S 1 x.val).1, ⟨_,(T.occupies x.val).mp x.property⟩)) (by
      constructor
      · rintro ⟨x,h⟩ ⟨w,p⟩ e
        obtain ⟨ha,hb⟩:=Prod.mk.inj e
        exact Subtype.ext ((unitSplit G S 1).injective (Prod.ext ha (Subtype.mk.inj hb)))
      rintro ⟨x,y,h⟩
      let a:= (unitSplit G S 1).symm (x,y)
      have he : unitSplit G S 1 a=(x,y):=Equiv.apply_symm_apply ..
      refine ⟨⟨a,(T.occupies a).mpr (by rw [he]; exact h)⟩,?_⟩
      apply Prod.ext (show (unitSplit G S 1 a).1=x from congr_arg Prod.fst he)
      apply Subtype.ext; change (unitSplit G S 1 a).2=y; rw [he])
lemma alignment (x : Alive G S T.forest) :
    unitSplit G S 1 x.val=((T.splitting x).1,(T.splitting x).2.val):=rfl

lemma compatible (K : KernelChoices) (P : Patch) (T : Lodge P) (c c' : Side) (x y)
    (h : (primary P K c).ratio.residue x=(primary P K c').ratio.residue y) :
    (forest (S:=primary P K c) T).hike x=(forest (S:=primary P K c') T).hike y := by
  let S:=primary P K c; let S':=primary P K c'
  induction x using Forest.hike.induct (forest (S:=primary P K c) T) generalizing y with
  | case1 x hx ih =>
    have hw := (is_leaf S x).1 hx; rw [h] at hw
    have he : (forest (S:=S) T).up x=(forest (S:=S') T).up y := congr_arg T.aim h
    have h':leaf S'.ratio y := (is_leaf S' _).mpr hw
    conv_lhs => rw [Forest.hike,dif_pos hx]
    conv_rhs => rw [Forest.hike,dif_pos h']
    exact congr_arg₂ List.cons he (ih _ (lift_inj ( (moves _ _ hx).1 |>.trans ((congr_arg₂ (·+·) (congr_arg lift h) (congr_arg Step.vec he)).trans (moves _ _ h').1.symm))))
  | case2 x hx=>
    have hw : ¬leaf S'.ratio y:= by rw [is_leaf S'] ; rw [← h]; exact fun h=> hx ((is_leaf S x).mpr h)
    conv_lhs => rw [Forest.hike,dif_neg hx]
    conv_rhs => rw [Forest.hike,dif_neg hw]
end Lodge
end YM.FormalBulk08.Flat
