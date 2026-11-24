import YM.Integration.WilsonExteriorGeometry

/-! Actual right-ceiling sites retain fixed physical coordinate gaps after
modular wrapping.  The period is chosen before the mesh tail, as required by
the original extraction filter; no generic-coordinate condition is used. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace YM.Integration.WilsonExteriorSeparation

open Function Filter Set Lattice Cells Extraction StressFlux.Matching
open scoped Topology Classical

variable {G : Gauge} (C : Family G) {f : Extraction.Order}

/-- A genuine coordinate gap in the original physical positions gives a
strict gap between the actual modular ceiling sites. -/
theorem ceilSite_gap (b : ℕ) (x y : E4) (a : Axis)
    (hgap : C.S.a b < |x a - y a|) :
    ∀ᶠ z : ℕ × ℕ in f.fuse, ∀ hb : b ≤ z.1,
      span C.S hb z.2 < separation (ceilSite C z.1 z.2 x) (ceilSite C z.1 z.2 y) := by
  let X : Points 2 := points ![x, y]
  obtain ⟨K, hK, hX, _⟩ := exists_compact_subset isOpen_univ (mem_univ X)
  have hround := chosen (S := C.S) X
  have hcoord : Tendsto
      (fun N => |Gaps.distances (tag (C.S.a N) (address (C.S.a N) X)) 1 0 a|)
      atTop (𝓝 |x a - y a|) := by
    simpa only [Gaps.distances, X, points_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, comp_def] using
      ((Gaps.ct (1 : Fin 2) 0 a).abs.tendsto X).comp hround
  rw [Order.fused, Order.late]
  filter_upwards [f.per.cofinal.eventually (Gaps.expand_equivalent C.S hK)] with p hp
  filter_upwards [(hround.comp f.mesh.cofinal).eventually
      (mem_interior_iff_mem_nhds.mp hX),
    (hcoord.comp f.mesh.cofinal).eventually (lt_mem_nhds hgap)] with N hN hNgap hb
  let u := address (C.S.a (f.mesh N)) X
  let A := ceilSite C (f.mesh N) (f.per p) x
  let B := ceilSite C (f.mesh N) (f.per p) y
  let q : Cover := lift (A - B)
  have hu0 : wrap (C.side (f.mesh N) (f.per p)) (u 0) = A := rfl
  have hu1 : wrap (C.side (f.mesh N) (f.per p)) (u 1) = B := rfl
  have hq : wrap (C.side (f.mesh N) (f.per p)) (u 0 - u 1) a =
      ((q a : ℤ) : Per (C.side (f.mesh N) (f.per p))) := by
    rw [map_sub, hu0, hu1]
    exact (congrFun (wrap_lift (A - B)) a).symm
  have hbound := Gaps.torus C.S (i := (1 : Fin 2)) (j := 0) (q a) hq
    (hp _ hN 1 0 a)
  have hcomponent : |(q a : ℝ)| ≤ (separation A B : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast component_le (A - B) a
  have hstrict : C.S.a b < C.S.a (f.mesh N) * (separation A B : ℝ) :=
    hNgap.trans_le (hbound.trans
      (mul_le_mul_of_nonneg_left hcomponent (C.S.a_pos _).le))
  rw [← C.S.embeds_scale (C.S.toDepth hb (f.per p))] at hstrict
  have hnat := lt_of_mul_lt_mul_left hstrict (C.S.a_pos (f.mesh N)).le
  exact_mod_cast hnat

/-- A finite collection of literal ceiling sites satisfies the same fixed
coarse-cell gap once all of its original coordinate gaps do. -/
theorem ceilSites_apart {I : Type} [Fintype I] (b : ℕ) (x : I → E4)
    (hx : ∀ i j, i ≠ j → ∃ a : Axis, C.S.a b < |x i a - x j a|) :
    ∀ᶠ z : ℕ × ℕ in f.fuse, ∀ hb : b ≤ z.1, ∀ i j, i ≠ j →
      span C.S hb z.2 < separation (ceilSite C z.1 z.2 (x i))
        (ceilSite C z.1 z.2 (x j)) := by
  have H := eventually_all.mpr fun i => eventually_all.mpr fun j =>
    eventually_all.mpr fun hij : i ≠ j => by
      obtain ⟨a, ha⟩ := hx i j hij
      exact ceilSite_gap C (f := f) b (x i) (x j) a ha
  exact H.mono fun z hz hb i j hij => hz i j hij hb

/-- Every separated finite physical configuration admits sufficiently small
coarse cells.  This choice precedes any fine cutoff or replica index. -/
theorem eventual_coordinate_gaps {I : Type} [Fintype I] (x : I → E4)
    (hx : Injective x) :
    ∀ᶠ b : ℕ in atTop, ∀ i j, i ≠ j →
      ∃ a : Axis, C.S.a b < |x i a - x j a| := by
  refine eventually_all.mpr fun i => eventually_all.mpr fun j =>
    eventually_all.mpr fun hij => ?_
  obtain ⟨a, ha⟩ : ∃ a : Axis, x i a ≠ x j a := by
    by_contra hn
    push Not at hn
    apply hij
    apply hx
    exact PiLp.ext hn
  have hpos : 0 < |x i a - x j a| := abs_pos.mpr (sub_ne_zero.mpr ha)
  exact (C.S.shrinks.eventually (gt_mem_nhds hpos)).mono fun b hb => ⟨a, hb⟩

/-- Literal right-ceiling separation for arbitrary separated physical points,
with no genericity restriction. -/
theorem ceilSites_apart_of_injective {I : Type} [Fintype I]
    (x : I → E4) (hx : Injective x) :
    ∀ᶠ b : ℕ in atTop, ∀ᶠ z : ℕ × ℕ in f.fuse, ∀ hb : b ≤ z.1,
      ∀ i j, i ≠ j → span C.S hb z.2 <
        separation (ceilSite C z.1 z.2 (x i)) (ceilSite C z.1 z.2 (x j)) :=
  (eventual_coordinate_gaps C x hx).mono fun b hb => ceilSites_apart C b x hb

end YM.Integration.WilsonExteriorSeparation
