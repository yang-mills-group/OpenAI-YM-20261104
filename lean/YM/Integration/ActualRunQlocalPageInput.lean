import YM.Integration.QlocalFinitePageTaste
import YM.Integration.ActualRunFullPages

/-! The original rooted tuple of physical kernels, with every native forced
partner, in one fixed all-test Taste. Scalar readers remain explicit data;
the signed native reader is supplied separately, without changing this layout. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunQlocalPageInput
open Function Finset Lattice Wilson RG Marker FVA1
open PhysicalNext.Repeat.Legato MergeProof MergeProof.Accent
open RG3.Held RG3.Script.Picnic LocalComparison QlocalFinitePageTaste
open OriginalForcedAddresses MergeProof.Replicums
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) (hG : G.Simple) (N p L : ℕ)
  (hL : L ≤ N) {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
  (o : Positions V (R.family.side L p)) (d : V → ℕ)
  (v : ∀ i, R.family.label (d i))
  (D : V → ComparisonDensity.Address.Orbit)
  (readout : ∀ i, (D i).Mood →ₗ[ℂ] ℂ)

abbrev pages := ActualRunFullPages.pages R hG N p L hL o d v

def coefficient (j : ActualRunFullPages.Index o) (x : TestSpace D) : ℂ :=
  ∏ i ∈ (pages R hG N p L hL o d v j).s.val, readout i (x i)

def input : Taste (TestSpace D) o.origin (R.family.path.rep N p L) (Stock.census V) :=
  QlocalFinitePageTaste.presentation (pages R hG N p L hL o d v) o
    (coefficient R hG N p L hL o d v D readout)

omit [Fintype V] [Nonempty V] in
private theorem coordinate_letter (i : V) :
    Letter ℂ (fun i => (D i).Mood) {i} (fun x => readout i (x i)) := by
  constructor
  · intro x y h
    exact congrArg (readout i) (h i (Finset.mem_singleton_self i))
  · intro x j hj a b
    have he : j = i := Finset.mem_singleton.mp hj
    subst j
    simp
  · intro x j hj a b
    have he : j = i := Finset.mem_singleton.mp hj
    subst j
    simp

omit [Fintype V] [Nonempty V] in
private theorem product_letter (s : Finset V) :
    Letter ℂ (fun i => (D i).Mood) s
      (fun x => ∏ i ∈ s, readout i (x i)) := by
  induction s using Finset.induction_on with
  | empty =>
    simpa using (Letter.const (K := ℂ) (T := fun i => (D i).Mood) (1 : ℂ))
  | @insert i s hi ih =>
    have hd : Disjoint ({i} : Finset V) s := by simpa using hi
    have h := (coordinate_letter D readout i).bind ih hd
    change Letter ℂ (fun i => (D i).Mood) ({i} ∪ s)
      (fun x => readout i (x i) * ∏ j ∈ s, readout j (x j)) at h
    simpa only [Finset.singleton_union, Finset.prod_insert hi] using h

omit [Nonempty V] in
private theorem page_stubs (j : ActualRunFullPages.Index o) :
    ∀ i ∈ (pages R hG N p L hL o d v j).s.val,
      o.stub i ⊆ Seal.scope (R.family.path.rep N p L)
        (pages R hG N p L hL o d v j).shellx := by
  rcases j with j | j
  · intro i hi
    have he : i = j := Finset.mem_singleton.mp hi
    subst i
    exact Finset.subset_union_right
  · intro i hi
    have hs := congrArg Prod.fst
      (cardK (actual_keeper R hG N L p hL) j.1)
    change o.stub i ⊆ ((R.family.path.rep N p L).activities.forced
      (cart (actual_keeper R hG N L p hL) j.1)).support
    change ((R.family.path.rep N p L).activities.forced
      (cart (actual_keeper R hG N L p hL) j.1)).support = j.1.val.1 at hs
    rw [hs]
    exact j.2.property.2 i hi

/-- The original zero-test layout is active, with all old vacuum rows intact. -/
theorem active_zero :
    ((input R hG N p L hL o d v D readout).leaf (fun i => (0 : (D i).Mood))).Active := by
  apply QlocalFinitePageTaste.active_zero
  intro j
  obtain ⟨i, hi⟩ := (pages R hG N p L hL o d v j).marked
  exact Finset.prod_eq_zero hi (map_zero (readout i))

/-- Every row is complex multilinear in precisely its original marker set. -/
theorem multilinear :
    LocalComparison.Multilinear D (input R hG N p L hL o d v D readout) := by
  apply QlocalFinitePageTaste.multilinear
  intro j
  exact product_letter D readout _

/-- Complete original tuple stubs, for every nonzero all-test row. -/
theorem retains :
    FunctionalRetains (input R hG N p L hL o d v D readout) o.stub :=
  QlocalFinitePageTaste.functionalRetains _ _ _ (page_stubs R hG N p L hL o d v)

/-- Exact full Page expression, before any field integral or projection. -/
theorem density_pages (x : TestSpace D) (U : Config G (R.family.side L p)) :
    ((input R hG N p L hL o d v D readout).leaf x).density U =
      essence (pages R hG N p L hL o d v) (fun _ => 0)
        (fun j => coefficient R hG N p L hL o d v D readout j x) U :=
  QlocalFinitePageTaste.density _ _ _ (page_stubs R hG N p L hL o d v) x U

end YM.Integration.ActualRunQlocalPageInput
