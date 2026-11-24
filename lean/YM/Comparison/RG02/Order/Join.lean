import YM.Comparison.RG02.Cumulants.Partition

/-!
# Pair two independent sets of markers

`room` uses the actual `Census` and not an unrestricted family. Coupling expansion uses this
with sufficiently many extra polarization names. The two sets of *variables* in this algebra
have no cross exclusions; independence says nothing probabilistic. This representation makes
cumulant and factorial identities applicable also at coupling orders. Cross insertions still
may have common sources and supports (vertices, etc.). -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Order.Join
open YM.Marker YM.Multi YM.Primitives.GCC.Anchor
open YM.Extra.Trajectories (connected connected_quiet pass_connected)
open YM.Comparison.RG02.Cumulants
open Finset Function
open scoped BigOperators Classical

variable {V W : Type} [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W]
variable (R : Census V) (S : Census W)

def room : Census (V ⊕ W) where
  choices := univ.filter (fun s : Finset (V⊕W)=> s.toLeft ∈ R.choices ∧ s.toRight∈S.choices)
  blank := by
    apply mem_filter.mpr; rw [show (∅:Finset (V⊕W)) = disjSum ∅ ∅ by simp]; simp only [toLeft_disjSum,toRight_disjSum,R.blank,S.blank,and_self]; simp
  solo i := by
    refine mem_filter.mpr ⟨mem_univ _,?_⟩; rcases i with i|i
    · rw [show ({Sum.inl i}:Finset (V⊕W)) = disjSum {i} ∅ from (by simp)]
      simp only [toLeft_disjSum,toRight_disjSum,R.solo,S.blank,and_self]
    rw [show ({Sum.inr i}:Finset (V⊕W)) = disjSum ∅ {i} from (by simp)]
    simp only [toLeft_disjSum,toRight_disjSum,R.blank,S.solo,and_self]
  down {_} hi j hj := by
    obtain ⟨h,h'⟩:= mem_filter.mp hi|>.2; exact mem_filter.mpr ⟨mem_univ _, R.down h _ (toLeft_subset_toLeft hj), S.down h' _ (toRight_subset_toRight hj)⟩

variable {R S}
abbrev Layer := (room R S).Mode
/-- `pair s t`: evaluate mixed at these (left,right) physical marker slots. -/
def pair (s : R.Mode) (t : S.Mode) : (room R S).Mode :=
  ⟨s.val.disjSum t.val, mem_filter.mpr ⟨mem_univ _, by simp⟩⟩
def left (u : (room R S).Mode) : R.Mode := ⟨u.val.toLeft,(mem_filter.mp u.property).2.1⟩
def right (u : (room R S).Mode) : S.Mode := ⟨u.val.toRight,(mem_filter.mp u.property).2.2⟩
lemma pair_eq {s u : R.Mode} {t v : S.Mode} : pair s t=pair u v ↔ s=u ∧ t=v := by
  simp only [Subtype.ext_iff,pair,disjSum_inj]
@[simp] lemma left_pair (s : R.Mode) (t : S.Mode) : left (pair s t)=s := Subtype.ext toLeft_disjSum
@[simp] lemma right_pair (s : R.Mode) (t : S.Mode) : right (pair s t)=t := Subtype.ext toRight_disjSum
@[simp] lemma pair_quiet : pair R.quiet S.quiet = (room R S).quiet := Subtype.ext (Finset.disjSum_eq_empty.mpr ⟨rfl,rfl⟩)
@[simp] lemma pair_reunite (s : (room R S).Mode) : pair (left s) (right s)=s := Subtype.ext toLeft_disjSum_toRight

def pairs (R : Census V) (S : Census W) : (R.Mode × S.Mode) ≃ (room R S).Mode where
   toFun st:= pair st.1 st.2
   invFun s:= (left s,right s)
   left_inv st := by simp
   right_inv := pair_reunite
lemma sum_pair {A : Type*} [AddCommMonoid A] (f : (room R S).Mode→A) :
    ∑ t,f t = ∑ x : R.Mode, ∑ y : S.Mode, f (pair x y) := by
  rw [← Equiv.sum_comp (pairs R S) f, Fintype.sum_prod_type]; rfl
lemma merge_pair (s t u : R.Mode) (x y z : S.Mode) :
    Poly.merges (pair s x) (pair t y) (pair u z) ↔ Poly.merges s t u ∧ Poly.merges x y z := by
  simp only [Poly.merges, disjoint_left, pair]
  rw [show s.val.disjSum x.val ∪ t.val.disjSum y.val = (s.val∪t.val).disjSum (x.val∪y.val) by ext (x|x) <;> simp]
  simp only [disjSum_inj, Sum.forall, inl_mem_disjSum, inr_mem_disjSum, and_and_and_comm]

lemma both_parts {x y : Poly (room R S)} (h : ∀ (s:R.Mode)(t:S.Mode),x.part (pair s t)=y.part (pair s t)) : x=y :=
  Poly.ext fun s => pair_reunite s ▸ h (left s) (right s)

-- mixed product (costs later)
lemma pair_product (x y : Poly (room R S)) (t : R.Mode) (u : S.Mode) :
    (x*y).part (pair t u) = ∑ i : R.Mode, ∑ j : S.Mode, ∑ k : R.Mode, ∑ l : S.Mode,
      if Poly.merges i k t ∧ Poly.merges j l u then x.part (pair i j)*y.part (pair k l) else 0 := by
  rw [Poly.part_mul]; simp_rw [sum_pair,merge_pair]

variable (R S)
private def lhs : Poly R→ₗ[ℂ] Poly (room R S) where
  toFun a := Poly.inject (fun x=> if right x=S.quiet then a.part (left x) else 0)
  map_add' a b:= Poly.ext fun i=> by change (if _ then (a+b).part _ else 0)=
                                            (if _ then a.part _ else 0)+(if _ then b.part _ else 0);
                                      split_ifs <;> simp
  map_smul' c a:= Poly.ext fun i=> by change (if _ then (c•a).part _ else 0)=c*(if _ then a.part _ else 0);
                                      split_ifs <;> simp
private def rhs : Poly S→ₗ[ℂ] Poly (room R S) where
  toFun a := Poly.inject (fun x=> if left x=R.quiet then a.part (right x) else 0)
  map_add' a b:= Poly.ext fun i=> by change (if _ then (a+b).part _ else 0)=
                                            (if _ then a.part _ else 0)+(if _ then b.part _ else 0);
                                      split_ifs <;> simp
  map_smul' c a:= Poly.ext fun i=> by change (if _ then (c•a).part _ else 0)=c*(if _ then a.part _ else 0);
                                      split_ifs <;> simp
private lemma lhs_side (x : Poly R) (t : R.Mode) (s : S.Mode) : (lhs R S x).part (pair t s)=
    if s=S.quiet then x.part t else 0 := by
  change (if right (pair t s)=S.quiet then _ else (0:ℂ)) = _; simp only [right_pair,left_pair]
private lemma rhs_side (x : Poly S) (t : R.Mode) (s : S.Mode) : (rhs R S x).part (pair t s)=
    if t=R.quiet then x.part s else 0 := by
  change (if left (pair t s)=R.quiet then _ else (0:ℂ)) = _; simp only [right_pair,left_pair]

lemma one_pair (t : R.Mode) (s : S.Mode) : (1 : Poly (room R S)).part (pair t s)=
    if t=R.quiet ∧ s=S.quiet then 1 else 0 := by simp only [Poly.one_part,← pair_quiet,pair_eq]

def injectLeft : Poly R→ₐ[ℂ] Poly (room R S) := AlgHom.ofLinearMap (lhs R S)
    (both_parts fun x y=> by rw [lhs_side, Poly.one_part, one_pair]; split_ifs <;> tauto) (fun p q=> by
  apply both_parts; intro x y; by_cases h : y=S.quiet
  · subst y; rw [lhs_side,pair_product];
    -- two sums over S deleted by quiet
    simp_rw [Poly.merge_vac, lhs_side];
    rw [if_pos True.intro,Poly.part_mul]; refine Finset.sum_congr rfl fun i _=> ?_
    rw [sum_eq_single S.quiet];
    · refine sum_congr rfl fun j _=> ?_; rw [sum_eq_single S.quiet]; simp
      · intro l _ hl; simp [hl]
      simp
    · intro l _ hl; simp [hl]
    simp
  rw [lhs_side, if_neg h, pair_product]
  simp_rw [lhs_side]; symm; refine sum_eq_zero fun i _ => sum_eq_zero fun j _ => sum_eq_zero fun k _ => sum_eq_zero fun l _ => ?_
  split_ifs with ht hi hk <;> first | exact False.elim (by obtain rfl : j=S.quiet := hi; obtain rfl : l=S.quiet:=hk; exact h ((Poly.vacuum S.quiet y).mp ht.2).symm) | simp)

def injectRight : Poly S→ₐ[ℂ] Poly (room R S) := AlgHom.ofLinearMap (rhs R S)
    (both_parts fun x y=> by rw [rhs_side, Poly.one_part, one_pair]; split_ifs <;> tauto) (fun p q=> by
  apply both_parts; intro x y; by_cases h : x=R.quiet
  · subst x; rw [rhs_side,pair_product]
    simp_rw [Poly.merge_vac,rhs_side]; rw [if_pos True.intro,Poly.part_mul, sum_eq_single R.quiet];
    · refine Finset.sum_congr rfl fun i _=> ?_; rw [sum_eq_single R.quiet]; simp
      · intro l _ hl; simp [hl]
      simp
    · intro l _ hl; simp [hl]
    simp
  rw [rhs_side, if_neg h, pair_product]
  simp_rw [rhs_side]; symm; refine sum_eq_zero fun i _ => sum_eq_zero fun j _ => sum_eq_zero fun k _ => sum_eq_zero fun l _ => ?_
  split_ifs with ht hi hk <;> first | exact False.elim (by obtain rfl : i=R.quiet := hi; obtain rfl : k=R.quiet:=hk; exact h ((Poly.vacuum R.quiet x).mp ht.1).symm) | simp)

lemma left_part (x : Poly R) (t : R.Mode) (s : S.Mode) : (injectLeft R S x).part (pair t s)=
    if s=S.quiet then x.part t else 0 := lhs_side ..
lemma right_part (x : Poly S) (t : R.Mode) (s : S.Mode) : (injectRight R S x).part (pair t s)=
    if t=R.quiet then x.part s else 0 := rhs_side ..
lemma inject_left_quiet (x : Poly R) :
    (injectLeft R S x).part (room R S).quiet=x.part R.quiet := by rw [← pair_quiet, left_part, if_pos rfl]
lemma inject_right_quiet (x : Poly S) :
    (injectRight R S x).part (room R S).quiet=x.part S.quiet := by rw [← pair_quiet, right_part, if_pos rfl]

/-- No cross exclusions. -/
lemma separate (x : Poly R) (y : Poly S) (t : R.Mode) (s : S.Mode) :
    (injectLeft R S x * injectRight R S y).part (pair t s)=x.part t*y.part s := by
  rw [pair_product]; simp_rw [left_part,right_part]; rw [sum_eq_single t];
  · rw [sum_eq_single S.quiet, sum_eq_single R.quiet];
    · simp [Poly.wind t R.quiet]
    · intro b _ hb; simp [hb]
    · simp
    · intro b _ hb; simp [hb]
    simp
  · intro b _ hb; refine sum_eq_zero fun i _ => sum_eq_zero fun j _ => sum_eq_zero fun k _ => ?_
    by_cases h : j=R.quiet
    · subst j; simp [Poly.wind b R.quiet,hb]
    simp [h]
  simp

-- kill one half.
private def lprojection : Poly (room R S) →ₗ[ℂ] Poly R where
   toFun x := Poly.inject (fun i=> x.part (pair i S.quiet))
   map_add' _ _ := rfl
   map_smul' _ _ := rfl
private def rprojection : Poly (room R S) →ₗ[ℂ] Poly S where
   toFun x := Poly.inject (fun i=> x.part (pair R.quiet i))
   map_add' _ _ := rfl
   map_smul' _ _ := rfl

def projectLeft : Poly (room R S) →ₐ[ℂ] Poly R := AlgHom.ofLinearMap (lprojection R S)
    (by ext i; change (1 : Poly (room R S)).part _=_; rw [one_pair]; simp) (fun p q => by
   apply Poly.ext; intro i
   change (p*q).part (pair i S.quiet)=_
   rw [pair_product, Poly.part_mul]; simp_rw [Poly.merge_vac]
   apply Finset.sum_congr rfl; intro j _; rw [sum_eq_single S.quiet]
   · apply Finset.sum_congr rfl; intro k _; rw [sum_eq_single S.quiet]
     · simp only [and_true,eq_self]; rfl
     · intro b _ hb; simp [hb]
     simp
   · intro b _ hb; simp [hb]
   simp)
def projectRight : Poly (room R S) →ₐ[ℂ] Poly S := AlgHom.ofLinearMap (rprojection R S)
    (by ext i; change (1 : Poly (room R S)).part _=_; rw [one_pair]; simp) (fun p q => by
   apply Poly.ext; intro i
   change (p*q).part (pair R.quiet i)=_
   rw [pair_product, Poly.part_mul]; simp_rw [Poly.merge_vac]; rw [sum_eq_single R.quiet]
   · apply Finset.sum_congr rfl; intro k _; rw [sum_eq_single R.quiet]
     · simp only [true_and]; rfl
     · intro b _ hb; simp [hb]
     simp
   · intro b _ hb; simp [hb]
   simp)

lemma left_projection (x : Poly (room R S)) (t : R.Mode) :
    (projectLeft R S x).part t=x.part (pair t S.quiet) := rfl
lemma right_projection (x : Poly (room R S)) (t : S.Mode) :
    (projectRight R S x).part t=x.part (pair R.quiet t) := rfl
lemma lprojection_quiet (x : Poly (room R S)) :
    (projectLeft R S x).part R.quiet=x.part (room R S).quiet := by rw [left_projection,pair_quiet]
lemma rprojection_quiet (x : Poly (room R S)) :
    (projectRight R S x).part S.quiet=x.part (room R S).quiet := by rw [right_projection,pair_quiet]
lemma project_inject_left (x : Poly R) : projectLeft R S (injectLeft R S x)=x := by
  ext t; rw [left_projection,left_part,if_pos rfl]
lemma project_inject_right (x : Poly S) : projectRight R S (injectRight R S x)=x := by
  ext t; rw [right_projection,right_part,if_pos rfl]

end YM.Comparison.RG02.Order.Join
