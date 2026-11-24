import YM.FormalOPE.RG10.MarkerLog
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Algebra

/-!
# Connection between log-of-output and the anchored primitive cumulant recursion

Authenticate without Gaussian assumptions. The expression to be continued is exactly a mixed
cumulant, not a bound paying for individual moments after canceling against spectators.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10
open Marker Extra.Trajectories PowerSeries MeasureTheory Filter Finset Word Primitives.GCC
open Primitives.GCC.Anchor
open scoped BigOperators

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
namespace PolyUtil
section
omit [Fintype V]

def asleep (i : V) : Poly R →ₐ[ℂ] Poly R := YM.Multi.dilation R (fun x => if x=i then 0 else 1)

@[simp] lemma asleep_view (i : V) (A : Poly R) (s : R.Mode) :
    (asleep i A).part s = if i ∈ s.val then 0 else A.part s := by
  rw [asleep, YM.Multi.dilation_part]; split
  · rename_i h; rw [Finset.prod_eq_zero (f:=fun j:V => if j=i then (0:ℂ) else 1) h (if_pos rfl), zero_mul]
  rename_i h
  rw [Finset.prod_eq_one, one_mul]
  intro b hb; exact if_neg (show ¬ b=i from fun e => h (e ▸ hb))

def protrude (i : V) (A : Poly R) := A - asleep i A

@[simp] lemma protrude_part (i : V) (s : R.Mode) (A : Poly R) :
    (protrude i A).part s = if i ∈ s.val then A.part s else 0 := by
  by_cases h:i∈s.val <;> simp [protrude, part_sub,h]

lemma touches_zero (i : V) (A B : Poly R) : protrude i A * protrude i B = 0 := by
  ext s; rw [Poly.part_mul, Poly.part_nil]; apply sum_eq_zero; intro a _
  apply sum_eq_zero; intro b _; split <;> rename_i h
  · by_cases hx : i∈a.val
    · have hny := Finset.disjoint_left.mp h.1 hx; simp [hny]
    simp [hx]
  rfl

end
lemma marked_defect (i : V) (A : Poly R) (hA : A.part R.quiet = 1) :
    protrude i A = protrude i (connected A) * asleep i A := by
  let p := connected A
  have hp : p.part R.quiet=0 := connected_quiet hA
  have ho : (asleep i p).part R.quiet=0 := by simp only [asleep_view, Census.quiet] at *; simp [hp]
  have hh : Poly.pass (asleep i p) = asleep i A := by
    rw [← YM.Multi.pass_map (asleep i) _ hp ho]; exact congr_arg (asleep i) (pass_connected hA)
  have he : A = asleep i A * (1+protrude i p) := by
    rw [← hh, ← YM.Multi.append_pass (asleep i p) (protrude i p) ho _ (touches_zero i p p),
      (show asleep i p + protrude i p = p by rw [protrude, add_sub_cancel]), pass_connected hA]
    simp [Census.quiet]
  change A-asleep i A=_
  conv_lhs => lhs; rw [he]
  unfold p; ring

/-- Moment-cumulant recursion that includes disconnected external factors. -/
lemma marked (i : V) (A : Poly R) (hA : A.part R.quiet = 1) :
    protrude i A = protrude i (connected A) * A := by
  have h := touches_zero i (connected A) A
  rw [show protrude i (connected A)*protrude i A =
    protrude i (connected A) * A - protrude i (connected A)*asleep i A from mul_sub ..] at h
  rw [marked_defect _ _ hA, (eq_of_sub_eq_zero h)]

/-- The `Anchor.quotient` supplying the Gaussian primitive-tree cost. -/
lemma at_marker (i : V) (A : Poly R) (hA : A.part R.quiet = 1) (s : R.Mode) (hi : i ∈ s.val) :
    (Anchor.quotient s.val {i} A).part s = (connected A).part s := by
  have ht (s : R.Mode) : Anchor.UpTo s.val (Anchor.root s.val {i} A) (protrude i A) := by
    intro j hj; rw [Anchor.root_part]; simp [hj]
  have hw : Anchor.UpTo s.val (Anchor.outer s.val {i} A) (asleep i A) := by
    intro j hj; rw [Anchor.outer_part]; by_cases hz:i∈j.val <;> simp [hj,hz]
  have hg : Anchor.UpTo s.val (-connected (Anchor.outer s.val {i} A)) (-connected (asleep i A)) := fun j hj => by
    rw [Poly.part_neg, Poly.part_neg, hw.conn j hj]
  unfold Anchor.quotient inverseMass
  have hr : (asleep i A).part R.quiet=1 := by rw [asleep_view]; simpa [Census.quiet] using! hA
  rw [((ht s).mul hg.pass) s (Finset.Subset.refl _), marked_defect _ _ hA, mul_assoc,
    show asleep i A * ((-connected (asleep i A)).pass)=1 from right_inverse hr, mul_one]
  simp [hi]
end PolyUtil
namespace Word

variable (i : V)
open Polar PolyUtil

omit [Fintype V] in
def noLeaf : Word R →+* Word R := PowerSeries.map (asleep i (R:=R)).toRingHom
omit [Fintype V] in
def withLeaf (A : Word R) := A - noLeaf i A

omit [Fintype V] in
@[simp] lemma no_leaf (A : Word R) (s : R.Mode) :
    see s (noLeaf i A) = if i ∈ s.val then 0 else see s A := by
  split_ifs with hm <;> apply PowerSeries.ext <;> intro k <;>
  simp [see, noLeaf, PowerSeries.coeff_map, hm]

omit [Fintype V] in
@[simp] lemma leaf_pick (A : Word R) (s : R.Mode) :
    see s (withLeaf i A) = if i ∈ s.val then see s A else 0 := by
  by_cases h:i∈s.val <;> simp [withLeaf, h]

variable {I : Type} [Fintype I] [DecidableEq I]

lemma ancestor (A : Word R) : certify I (withLeaf i A) = protrude (Sum.inl i) (certify I A) := by
  ext s; rw [← pay_sep s, protrude_part]
  generalize mark s = u
  generalize tickets s = t
  simp_rw [certify_present, present_pay, ← unfold_see, leaf_pick];
  by_cases h : i ∈ u.val <;> simp [h, pay]

/-- Log-of-output rooted identity; project further to get the recursion in any allowed
subset order. -/
lemma adjoin (A : Word R) (h : boot A = 1) : withLeaf i A = withLeaf i (logWord A) * A := by
  apply detects; intro k; rw [map_mul, ancestor, ancestor, consistent A h]
  exact marked _ _ ((present_quiet A).trans h)
end Word
end YM.FormalOPE.RG10
