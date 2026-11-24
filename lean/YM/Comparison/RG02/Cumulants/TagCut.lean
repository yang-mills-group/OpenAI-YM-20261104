import YM.Comparison.RG02.Cumulants.Moment
/-!
# Tag disconnections

Only available if the *joint* average factors on the actual tag footprints.
A convenient case is the field-independent **reference** product law, with the
likelihoods of any shared site being read consistently in the integrands. It is NOT generally
a statement on the actual kernel at arbitrary fields. Keep all neighborhoods/dependencies,
including projections of candidate covariance lines, when using the lemma on
`total_log`. `mix` with no factorization premises is always possible (using single tag law).
-/
set_option autoImplicit false
noncomputable section

namespace YM.Comparison.RG02.Cumulants
open YM.Marker YM.Multi YM.Primitives.GCC.Anchor
open YM.Extra.Trajectories (connected connected_quiet pass_connected)
open Finset
open scoped BigOperators Classical

namespace TagCut
variable {J : Type*} {W : J → Type*} [DecidableEq J]

/-- Swap across the outside of U, not independent resampling. -/
def hybrid (U : Finset J) (x y : ∀ j,W j) : ∀ j,W j := fun j=> if j∈U then x j else y j

def swap (U : Finset J) : Equiv.Perm ((∀ j,W j) × (∀ j,W j)) :=
  Function.Involutive.toPerm (f:=fun (q : (∀ j,W j) × (∀ j,W j))=> (hybrid U q.1 q.2,hybrid U q.2 q.1))
    (by rintro ⟨x,y⟩; ext <;> rename_i j <;> by_cases h : j∈U <;> simp [hybrid,h])

def Reads (f : (∀ j, W j)→ℂ) (U : Finset J) : Prop := ∀ x y : ∀ j,W j,
    (∀ j∈U,x j=y j) → f x = f y
omit [DecidableEq J] in
lemma Reads.mono {f : (∀ j,W j)→ℂ} {U R : Finset J} (h : Reads f U) (hu : U⊆R) : Reads f R :=
  fun x y hh=> h x y fun j hj=> hh j (hu hj)
omit [DecidableEq J] in
lemma reads_prod {ι : Type*} (u : Finset ι) (f : ι → (∀ j, W j)→ℂ) {U : Finset J}
    (h : ∀ i∈u, Reads (f i) U) : Reads (∏ i∈u, f i) U := by
  intro x y he; simp_rw [Finset.prod_apply]; exact Finset.prod_congr rfl fun i hi=> h i hi x y he

variable [Fintype J]

def productLaw (w : ∀ j,W j→ℂ) (x: ∀ j,W j) : ℂ := ∏ j,w j (x j)
lemma invariant_swap (w : ∀ j,W j→ℂ) (U : Finset J) (x : (∀ j,W j) × (∀ j,W j)) :
    productLaw w ((swap U x).1)*productLaw w ((swap U x).2)=productLaw w x.1*productLaw w x.2 := by
  unfold productLaw; simp_rw [← Finset.prod_mul_distrib]; refine Finset.prod_congr rfl fun j _=> ?_
  change w j (hybrid U x.1 x.2 j) * w j (hybrid U x.2 x.1 j) = _
  by_cases h : j∈U <;> simp [hybrid,h,mul_comm]

variable [∀ j,Fintype (W j)]

lemma normalized (w : ∀ j,W j→ℂ) (h : ∀ j, ∑ i, w j i=1) : ∑ a, productLaw w a = 1 := by
  unfold productLaw; rw [← Fintype.prod_sum]; simp [h]

lemma factorization (w : ∀ j,W j→ℂ) (h : ∑ a, productLaw w a=1) (f g : (∀ j,W j)→ℂ)
    {U R : Finset J} (hu : Disjoint U R) (hf : Reads f U) (hg : Reads g R) :
    tagAverage (productLaw w) (f*g) = tagAverage (productLaw w) f * tagAverage (productLaw w) g := by
  let L := productLaw w
  let X := (∀ j,W j)
  let F (x : X × X) := L x.1 * L x.2 * (f*g) x.1
  let E := swap (W:=W) U
  have he (x : X × X) : F (E x) = (L x.1*f x.1)*(L x.2*g x.2) := by
    unfold F L E; rw [invariant_swap]
    have hH : f (hybrid U x.1 x.2) = f x.1 := hf _ _ (fun j hj=>if_pos hj)
    have hK : g (hybrid U x.1 x.2) = g x.2 := hg _ _ fun j hj=> if_neg (fun hh=>disjoint_left.mp hu hh hj)
    change _* (f (hybrid U x.1 x.2)*g (hybrid U x.1 x.2))=_; rw [hH,hK]; ring
  have hz a : ∑ b:X,F (a,b)= L a*(f*g) a := by
    let c := L a*(f*g) a
    calc
      _ = ∑ b:X,L b*c := Finset.sum_congr rfl fun b _=> by unfold c F; simp; ring
      _ = c := by rw [← Finset.sum_mul, show ∑ b:X,L b=1 from h, one_mul]
  calc
    _ = ∑ a : X × X,F a := by rw [Fintype.sum_prod_type]; simp_rw [hz]; rfl
    _ = _ := by
      rw [← Equiv.sum_comp E F]; simp_rw [he]; rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]; rfl

-- Pair of disjoint *aggregate* tag footprints. Apply repeatedly by connected overlap of true
-- dependencies. Neither `R` nor `t` has to come from a primary-source mode rather than shards.
lemma cumulant_vanish {V : Type*} [DecidableEq V] [Fintype V] {R : Census V} (t : R.Mode)
    (w : ∀ j,W j→ℂ) (h : ∑ a, productLaw w a=1) (f : V → (∀ j,W j)→ℂ) (U : Finset V)
    (hi : (t.val∩U).Nonempty) (ho : (t.val\U).Nonempty) {I O : Finset J} (he : Disjoint I O)
    (hI : ∀ i∈t.val∩U,Reads (f i) I) (hO : ∀ i∈t.val\U,Reads (f i) O) :
    (connected (moments R (tagAverage (productLaw w)) f)).part t=0 := by
  refine cumulant_split _ _ t (averaged (productLaw _) h) hi ho (fun s hs=> ?_)
  have hF : (∏ i∈s.val,f i)=(∏ i∈s.val∩U,f i)*(∏ i∈s.val\U,f i) := Eq.trans (by rw [← (merges_side s U).2] : (∏ i∈s.val,f i)=(∏ i∈(inside s U).val∪(diff s U).val,f i)) (prod_union (merges_side s U).1)
  rw [hF]; exact factorization w h _ _ he (reads_prod _ f fun i hi=> hI i (Finset.inter_subset_inter_right hs hi)) (reads_prod _ f fun i ho=> hO i ((sdiff_subset_sdiff hs (Finset.Subset.refl U)) ho))
end TagCut
end YM.Comparison.RG02.Cumulants
