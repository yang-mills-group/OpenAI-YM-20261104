import YM.Integration.WilsonPhysicalHistoryInverse

/-! Select the physical counterterm from the full periodic germ of the
captured column. Its cost and uniqueness refer to the original factory
entry, on the same cutoff and torus as the captured coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedGermCounterterm
open Filter Lattice RG Source Labels PhysicalNext.Repeat.Legato
open Trace.Physical Trace.Physical.GermGraph Work.G08
open scoped Classical Topology

variable {G : Gauge} (R : Run G) (d : ℕ) {N p u : ℕ}
local notation "F" => R.family.labels.level d
local notation "π" => page (C:=R.family) d p u

theorem matched (opened : Opened R.family d u p) (hN : u ≤ N)
    (q : Coefficient F (R.family.side u p)) :
    ∃ x : R.family.label d,
      π q - π ((R.family.factory d N p).entries u x) = 0 ∧
      reads (C:=R.family) d N p u ((R.family.factory d N p).entries u x) (2 * stock R.family u * (F).coeffSize (π q)) ∧
      (∀ y, π ((R.family.factory d N p).entries u y) = π q → y = x) := by
  let fit := fitting d N p u R.makes opened hN
  let x := fit.symm (π q)
  have paid : fit x = π q := fit.apply_symm_apply _
  have seen : π ((R.family.factory d N p).entries u x) = π q := by
    exact (fitting_apply d N p u R.makes opened hN x).symm.trans paid
  have cost := graph_cost d N p u R.makes opened hN x
  change reads (C:=R.family) d N p u ((R.family.factory d N p).entries u x) (2 * stock R.family u * (F).coeffSize (fit x)) at cost
  rw [paid] at cost
  refine ⟨x,sub_eq_zero.mpr seen.symm,cost,?_⟩
  intro y hy
  apply fit.injective
  change π ((R.family.factory d N p).entries u y) = π ((R.family.factory d N p).entries u x)
  exact hy.trans seen.symm

theorem cofinal (hG : G.Simple) :
    ∀ᶠ u : ℕ in atTop, ∀ p N, u ≤ N →
      ∀ q : Coefficient F (R.family.side u p), ∃ x : R.family.label d,
        page (C:=R.family) d p u q -
          page (C:=R.family) d p u ((R.family.factory d N p).entries u x) = 0 ∧
        reads (C:=R.family) d N p u ((R.family.factory d N p).entries u x)
          (2 * stock R.family u * (F).coeffSize (page (C:=R.family) d p u q)) ∧
        (∀ y, page (C:=R.family) d p u ((R.family.factory d N p).entries u y) =
          page (C:=R.family) d p u q → y = x) := by
  filter_upwards [open_late R.family hG d] with u hu
  intro p N hn q
  exact matched R d (hu p) hn q

end YM.Integration.WilsonCapturedGermCounterterm
