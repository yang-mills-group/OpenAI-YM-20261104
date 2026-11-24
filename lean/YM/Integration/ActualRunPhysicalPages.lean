import YM.FVA1.LeafRoster
import YM.Integration.ActualRG05PhysicalSource
import YM.Integration.OriginalForcedAddresses
import YM.Extra.MULTISOURCE_BOUNDS.Columns

/-!
Actual regular Page entries on the retained Run.  The kernel, original terminal
map and price are fixed before any scalar test coefficient.  This file does
not identify the Healthy-masked Page with a full unmasked physical source;
its complementary forced partners remain a separate construction.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRunPhysicalPages
open Finset Function Lattice Wilson RG Source Marker Extra.Multi Push
open FVA1 PhysicalNext.Repeat.Legato
open scoped BigOperators Classical

variable {G : Gauge} (R : Run G) (N p L d : ℕ)

def kernel (v : R.family.label d) (o : Site (R.family.side L p)) :
    Config G (R.family.side L p) → ℂ :=
  Local.presented (R.family.localSection d) o
    (R.family.path.rep N p L).p.threshold v

def price (v : R.family.label d) : ℝ :=
  (R.family.path.levels.params L).columns * (R.family.labels.level d).coeffSize v

theorem priced (hLN : L ≤ N) (href : R.family.ref d ≤ L)
    (v : R.family.label d) (o : Site (R.family.side L p)) :
    (R.family.path.rep N p L).p.Regular
      ((R.family.localSection d).footprint o) (kernel R N p L d v o) ∧
    (R.family.path.rep N p L).p.supBounds o
      ((R.family.localSection d).footprint o) (kernel R N p L d v o)
      (price R L d v) := by
  have hp := BasisCost.analytic (R.family.localSection d)
    (R.family.path.rep N p L).p v o (C := (R.family.path.levels.params L).columns)
    (by
      have hpoint : (R.family.path.rep N p L).p = R.family.path.levels.budget L :=
        (R.makes.wilson.represents N p L hLN).vac
      rw [hpoint]
      exact R.makes.priced d L p href o)
  simpa only [kernel, price, Local.presented, LinearMap.coe_mk,
    AddHom.coe_mk] using hp

/-- The cutoff is L, including its own original terminal map and a_L^d. -/
theorem kernel_physical (hLN : L ≤ N) (v : R.family.label d)
    (o : Site (R.family.side L p)) :
    kernel R N p L d v o = (R.family.S.a L : ℂ) ^ d •
      R.family.O L p ((R.family.factory d L p).terminal v) o := by
  have ht : (R.family.path.rep N p L).p.threshold =
      (R.family.path.rep L p L).p.threshold := by
    have hpoint : (R.family.path.rep N p L).p = R.family.path.levels.budget L :=
      (R.makes.wilson.represents N p L hLN).vac
    have hbase : (R.family.path.rep L p L).p = R.family.path.levels.budget L :=
      (R.makes.wilson.represents L p L le_rfl).vac
    exact congrArg BudgetPoint.threshold (hpoint.trans hbase.symm)
  unfold kernel
  rw [ht]
  exact ActualRG05PhysicalSource.presented_physical R.family R.makes L p d v o

variable {V : Type} [DecidableEq V] {B : Census V}

/-- Keep the actual requested stub as well as the complete native footprint. -/
def cover (o : Positions V (R.family.side L p)) (i : V) :
    Support (R.family.side L p) :=
  (R.family.localSection d).footprint (o.origin i) ∪ o.stub i

def page (o : Positions V (R.family.side L p)) (i : V)
    (v : R.family.label d) : Page B (R.family.path.rep N p L) where
  s := B.fire i
  marked := Finset.singleton_nonempty i
  shellx := .inl (cover R p L d o i)
  term := kernel R N p L d v (o.origin i)
  chip := 1

theorem entry (hLN : L ≤ N) (href : R.family.ref d ≤ L)
    (o : Positions V (R.family.side L p)) (i : V) (v : R.family.label d) :
    (page R N p L d o i v (B := B)).Entry o (price R L d v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have he : j = i := Finset.mem_singleton.mp hj
    subst j
    exact Finset.subset_union_right
  · intro s hs
    change Sum.inl (cover R p L d o i) = Sum.inl s at hs
    have he := Sum.inl.inj hs
    subst s
    obtain ⟨hr, hb⟩ := priced R N p L d hLN href v (o.origin i)
    refine ⟨Next.Foundations.regular_larger hr Finset.subset_union_left, ?_⟩
    intro j hj
    have he : j = i := Finset.mem_singleton.mp hj
    subst j
    exact Next.Foundations.bound_larger hb Finset.subset_union_left
  intro k hk
  cases hk

theorem ready_physical (hLN : L ≤ N)
    (o : Positions V (R.family.side L p)) (i : V) (v : R.family.label d) :
    (page R N p L d o i v (B := B)).ready =
      masked (R.family.path.rep N p L).p.threshold (cover R p L d o i)
        ((R.family.S.a L : ℂ) ^ d •
          R.family.O L p ((R.family.factory d L p).terminal v) (o.origin i)) := by
  change masked _ _ (kernel R N p L d v (o.origin i)) = _
  rw [kernel_physical R N p L d hLN]

end YM.Integration.ActualRunPhysicalPages
