import YM.MergeProof.North.Harvest
import YM.Next.UV_STRESS.Atom
import YM.MergeProof.Glacier

/-!
Exact initialization of a signed product together with its physical
counterterm, on every supplied region at once.  The old census forbids a
counterterm and any product factor in the same region.  The projection is
linear on the complete polynomial density; it is not an algebra homomorphism.

The input representation is never changed.  In particular its scalar,
unmarked activities and forced alphabet are those of the original vacuum.
The region and factor types are arbitrary finite types, so callers retain
all copy/root alternatives and all ancestor/preimage factors in those types.
This file proves exact identities, not a grouped `Served` estimate.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.JointSignedInitialization
open Function Finset MeasureTheory Lattice Wilson RG Marker
open MergeProof MergeProof.Accent Extra.Trajectories
open scoped BigOperators Classical Topology

variable {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]

/-- Product factors and the separate compensating physical column. -/
abbrev Name (I J : Type) := (I × J) ⊕ I

/-- A selected counterterm excludes every selected product factor in its
own region.  There are no extra restrictions between different regions. -/
def Compatible (s : Finset (Name I J)) : Prop :=
  ∀ i j, Sum.inr i ∈ s → Sum.inl (i, j) ∉ s

def original : Census (Name I J) where
  choices := Finset.univ.filter Compatible
  blank := by simp [Compatible]
  solo x := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    cases x <;> simp [Compatible]
  down := by
    intro s hs t hts
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro i j hi hj
    exact (Finset.mem_filter.mp hs).2 i j (hts hi) (hts hj)

abbrev grouped : Census I := Stock.census I

/-- The complete product is selected on `s \ t`, and just the physical
counterterm on `t`.  Every factor is retained on the product branch. -/
def branch (s t : Finset I) : (original (I := I) (J := J)).Mode :=
  ⟨((s \ t) ×ˢ (Finset.univ : Finset J)).disjSum t,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      intro i j hi hj
      exact (Finset.mem_sdiff.mp
        (Finset.mem_product.mp (Finset.inl_mem_disjSum.mp hj)).1).2
          (Finset.inr_mem_disjSum.mp hi)⟩⟩

/-- The full-density grouping.  Each chosen counterterm contributes one
minus sign.  Partial products and incompatible selections are not read. -/
def project : Poly (original (I := I) (J := J)) →L[ℂ] Poly (grouped (I := I)) :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun P => Poly.inject fun s =>
         ∑ t ∈ s.val.powerset, (-1 : ℂ) ^ t.card * P.part (branch s.val t)
       map_add' := by
         intro P Q
         apply Marker.Poly.ext
         intro s
         change (∑ t ∈ s.val.powerset, (-1 : ℂ) ^ t.card *
           (P.part (branch s.val t) + Q.part (branch s.val t))) =
           (∑ t ∈ s.val.powerset, (-1 : ℂ) ^ t.card * P.part (branch s.val t)) +
           ∑ t ∈ s.val.powerset, (-1 : ℂ) ^ t.card * Q.part (branch s.val t)
         simp only [mul_add, Finset.sum_add_distrib]
       map_smul' := by
         intro c P
         apply Marker.Poly.ext
         intro s
         change (∑ t ∈ s.val.powerset,
           (-1 : ℂ) ^ t.card * (c * P.part (branch s.val t))) =
           c * ∑ t ∈ s.val.powerset,
             (-1 : ℂ) ^ t.card * P.part (branch s.val t)
         rw [Finset.mul_sum]
         apply Finset.sum_congr rfl
         intro t _
         ring } : Poly (original (I := I) (J := J)) →ₗ[ℂ] Poly (grouped (I := I)))

theorem project_part (P : Poly (original (I := I) (J := J)))
    (s : (grouped (I := I)).Mode) :
    (project P).part s =
      ∑ t ∈ s.val.powerset, (-1 : ℂ) ^ t.card * P.part (branch s.val t) := rfl

/-- The projection preserves the original unmarked coefficient exactly. -/
theorem project_quiet (P : Poly (original (I := I) (J := J))) :
    (project P).part (grouped (I := I)).quiet =
      P.part (original (I := I) (J := J)).quiet := by
  rw [project_part]
  simp only [Census.quiet, Finset.powerset_empty, Finset.sum_singleton,
    Finset.card_empty, pow_zero, one_mul]
  apply congrArg P.part
  apply Subtype.ext
  simp [branch]

/-- The singleton is the original complete-product coefficient minus the
original counterterm coefficient, from this same full density. -/
theorem project_fire (P : Poly (original (I := I) (J := J))) (i : I) :
    (project P).part ((grouped (I := I)).fire i) =
      P.part (branch {i} ∅) - P.part (branch {i} {i}) := by
  rw [project_part]
  change (∑ t ∈ ({i} : Finset I).powerset,
    (-1 : ℂ) ^ t.card * P.part (branch {i} t)) = _
  have hp : ({i} : Finset I).powerset = {∅, {i}} := by
    ext t
    simp [Finset.mem_powerset, Finset.subset_singleton_iff]
  rw [hp]
  simp [sub_eq_add_neg]

/-- Original occurrences retain their region identifier throughout the
linear grouping; callers may include copy and ancestor keys in `I`. -/
def region : Name I J → I := Sum.elim Prod.fst id

theorem branch_regions [Nonempty J] (s t : Finset I) (ht : t ⊆ s) :
    (branch (J := J) s t).val.image region = s := by
  ext i
  constructor
  · intro hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    cases a with
    | inl a =>
        exact (Finset.mem_sdiff.mp
          (Finset.mem_product.mp (Finset.inl_mem_disjSum.mp ha)).1).1
    | inr a => exact ht (Finset.inr_mem_disjSum.mp ha)
  intro hi
  by_cases hti : i ∈ t
  · exact Finset.mem_image.mpr
      ⟨Sum.inr i, Finset.inr_mem_disjSum.mpr hti, rfl⟩
  let j : J := Classical.choice (inferInstance : Nonempty J)
  exact Finset.mem_image.mpr ⟨Sum.inl (i, j),
    Finset.inl_mem_disjSum.mpr (Finset.mem_product.mpr
      ⟨Finset.mem_sdiff.mpr ⟨hi, hti⟩, Finset.mem_univ j⟩), rfl⟩

/-- Delete entire regions in the original alphabet, including their
counterterms and every one of their product occurrences. -/
def keepOriginal (a : Finset I) (P : Poly (original (I := I) (J := J))) :
    Poly (original (I := I) (J := J)) :=
  Poly.inject fun q => if q.val.image region ⊆ a then P.part q else 0

def keepGrouped (a : Finset I) (P : Poly (grouped (I := I))) :
    Poly (grouped (I := I)) :=
  Poly.inject fun q => if q.val ⊆ a then P.part q else 0

/-- Deleting other marks recovers precisely the same selected signed
sources.  No new singleton or test-dependent presentation is selected. -/
theorem project_keep [Nonempty J] (a : Finset I)
    (P : Poly (original (I := I) (J := J))) :
    project (keepOriginal a P) = keepGrouped a (project P) := by
  apply Marker.Poly.ext
  intro s
  rw [project_part]
  change (∑ t ∈ s.val.powerset, (-1 : ℂ) ^ t.card *
      (if (branch (J := J) s.val t).val.image region ⊆ a
        then P.part (branch s.val t) else 0)) =
    if s.val ⊆ a then (project P).part s else 0
  by_cases hs : s.val ⊆ a
  · rw [if_pos hs, project_part]
    apply Finset.sum_congr rfl
    intro t ht
    rw [branch_regions s.val t (Finset.mem_powerset.mp ht), if_pos hs]
  rw [if_neg hs]
  apply Finset.sum_eq_zero
  intro t ht
  rw [branch_regions s.val t (Finset.mem_powerset.mp ht), if_neg hs, mul_zero]

variable {X : Type}

def sources (F : I → J → X → ℂ) (K : I → X → ℂ) : Name I J → X → ℂ :=
  Sum.elim (fun ij => F ij.1 ij.2) K

def signed (F : I → J → X → ℂ) (K : I → X → ℂ) : I → X → ℂ :=
  fun i U => (∏ j : J, F i j U) - K i U

theorem branch_product (F : I → J → X → ℂ) (K : I → X → ℂ)
    (s t : Finset I) (U : X) :
    (∏ a ∈ (branch (J := J) s t).val, sources F K a U) =
      (∏ i ∈ s \ t, ∏ j : J, F i j U) * ∏ i ∈ t, K i U := by
  unfold branch
  rw [Finset.prod_disjSum, Finset.prod_product]
  rfl

variable {G : Gauge} {n : Side}

/-- A single original-vacuum birth of every old factor and compensating
column projects to the single birth of every signed product. -/
theorem project_birth (R : Rep G n)
    (F : I → J → Config G n → ℂ) (K : I → Config G n → ℂ) :
    (fun U => project (Accent.birth original R (sources F K) U)) =
      Accent.birth grouped R (signed F K) := by
  funext U
  apply Marker.Poly.ext
  intro s
  rw [project_part]
  simp only [Accent.birth, Poly.part_smul, Mach, pass_fire]
  simp_rw [branch_product]
  unfold signed
  rw [Finset.prod_sub, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- This identity holds after every actual push along the same history.
It does not multiply separately pushed factors or replace the vacuum. -/
theorem gust_project (H : History G) (N p : ℕ)
    (P : Config G (H.S.side N p) → Poly (original (I := I) (J := J)))
    (hP : Integrable P (prior G (H.S.side N p))) {m : ℕ} (hm : m ≤ N) :
    gust H N p N (fun U => project (P U)) m hm =
      fun U => project (gust H N p N P m hm U) := by
  induction hm using Nat.decreasingInduction with
  | self => simp only [gust_base]
  | of_succ i hi ih =>
      rw [gust_step H N p N _ hi, ih]
      funext U
      rw [gust_step H N p N _ hi]
      unfold StepData.push
      let L := (project (I := I) (J := J)).restrictScalars ℝ
      have he := L.integral_comp_comm
        (StepData.push_slice (H.levels.transition_mass i p (H.β N p (i + 1)))
          U _ (gust_live H N p N P hP hi))
      simp_rw [L.map_smul] at he
      exact he

theorem signed_birth_integrable (R : Rep G n)
    (F : I → J → Config G n → ℂ) (K : I → Config G n → ℂ)
    (hP : Integrable (Accent.birth original R (sources F K)) (prior G n)) :
    Integrable (Accent.birth grouped R (signed F K)) (prior G n) := by
  rw [← project_birth R F K]
  exact ((project (I := I) (J := J)).restrictScalars ℝ).integrable_comp hP

/-- The concrete signed product is read from the jointly pushed old
polynomial, with every product/counterterm branch still present. -/
theorem signed_gust (H : History G) (N p : ℕ)
    (F : I → J → Config G (H.S.side N p) → ℂ)
    (K : I → Config G (H.S.side N p) → ℂ)
    (hP : Integrable (Accent.birth original (H.rep N p N) (sources F K))
      (prior G (H.S.side N p))) {m : ℕ} (hm : m ≤ N) :
    gust H N p N (Accent.birth grouped (H.rep N p N) (signed F K)) m hm =
      fun U => project
        (gust H N p N (Accent.birth original (H.rep N p N) (sources F K)) m hm U) := by
  rw [← project_birth (H.rep N p N) F K]
  exact gust_project H N p _ hP hm

section PhysicalCopies
open Cells

omit [DecidableEq J] in
/-- All reflected copies retain the sign of the physical subtraction,
including the complex conjugation in an odd reflection cell. -/
theorem copies_signed (T : Tiling n) (F : J → Config G n → ℂ)
    (K : Config G n → ℂ) :
    signed (fun i j => T.copy i (F j)) (fun i => T.copy i K) =
      fun i => T.copy i (fun U => (∏ j : J, F j U) - K U) := by
  funext i U
  unfold signed Tiling.copy
  by_cases h : T.hand i
  · simp only [if_pos h, star_sub, star_prod]
  · simp only [if_neg h]

private theorem copy_continuous (T : Tiling n) (i : T.Cell)
    {F : Config G n → ℂ} (hF : Continuous F) : Continuous (T.copy i F) := by
  unfold Tiling.copy
  split_ifs
  · exact (hF.comp (continuous_pull ..)).star
  exact hF.comp (continuous_pull ..)

/-- A tested physical column retains every supplied root, with its own
test value.  Neither a common test nor a distinguished root is selected. -/
def column (C : Family G) (N p d : ℕ) (v : C.label d)
    (roots : Finset (Site (C.side N p))) (test : Site (C.side N p) → ℂ)
    (U : Config G (C.side N p)) : ℂ :=
  ∑ x ∈ roots, test x * C.O N p v x U

theorem column_continuous (C : Family G) (N p d : ℕ) (v : C.label d)
    (roots : Finset (Site (C.side N p))) (test : Site (C.side N p) → ℂ) :
    Continuous (column C N p d v roots test) := by
  exact continuous_finsetSum _ fun x _ =>
    continuous_const.mul (C.continuousO N p d v x)

/-- Concrete actual Wilson columns, arbitrary independent tests and all
their reflected copies are initialized together.  The same statement holds
at each actual level of the fixed cutoff and period.  The entire finite
root sets are retained, including any required ancestor/preimage blocks.
There is no `Served`, projection-smallness or new-density premise. -/
theorem actual_copied_signed_gust (C : Family G) (hC : C.Makes) (N p : ℕ)
    (T : Tiling (C.side N p)) (d : J → ℕ) (v : (j : J) → C.label (d j))
    (roots : J → Finset (Site (C.side N p)))
    (test : J → Site (C.side N p) → ℂ)
    (e : ℕ) (z : C.label e) (counterRoots : Finset (Site (C.side N p)))
    (counterTest : Site (C.side N p) → ℂ) {m : ℕ} (hm : m ≤ N) :
    let F := fun j => column C N p (d j) (v j) (roots j) (test j)
    let K := column C N p e z counterRoots counterTest
    gust C.path N p N
      (Accent.birth grouped (C.path.rep N p N)
        (fun i => T.copy i (fun U => (∏ j : J, F j U) - K U))) m hm =
      fun U => project
        (gust C.path N p N
          (Accent.birth original (C.path.rep N p N)
            (sources (fun i j => T.copy i (F j)) (fun i => T.copy i K))) m hm U) := by
  intro F K
  have hF : ∀ j, Continuous (F j) := fun j => column_continuous C N p _ _ _ _
  have hK : Continuous K := column_continuous C N p _ _ _ _
  have hsrc : ∀ a : Name T.Cell J,
      Continuous (sources (fun i j => T.copy i (F j)) (fun i => T.copy i K) a) := by
    intro a
    cases a with
    | inl a => exact copy_continuous T a.1 (hF a.2)
    | inr i => exact copy_continuous T i hK
  have hR : Continuous (C.path.rep N p N).eval := by
    rw [(hC.wilson.starts N p).2]
    exact bare_cont _
  have hP : Integrable
      (Accent.birth original (C.path.rep N p N)
        (sources (fun i j => T.copy i (F j)) (fun i => T.copy i K)))
      (prior G (C.side N p)) := (hatCont C N p
    (sources (fun i j => T.copy i (F j)) (fun i => T.copy i K))
    hsrc hR original).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [← copies_signed T F K]
  exact signed_gust C.path N p _ _ hP hm

end PhysicalCopies

end YM.Integration.JointSignedInitialization
