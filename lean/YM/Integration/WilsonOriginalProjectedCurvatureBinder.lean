import YM.Integration.WilsonOriginalProjectedCurvaturePassport

/-! The original singleton mask binds its own test root. Every input stencil
has already been wired on the cover; any additional occupied height is billed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureBinder
open Function Finset Lattice Wilson RG Source Labels Marker QuadraticLocal.Earn
open MergeProof.Accent FVA1 PhysicalNext.Repeat.Legato LocalComparison
open WilsonOriginalProjectedCurvaturePassport
open scoped Classical BigOperators
variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {p L n : ℕ} {hn : n ≤ L} {V : Type} [DecidableEq V] [Fintype V]
  (D : ActualRunQlocalNativeTuple.Datum R p L n hn V) (u : V → MS.Rake.Label B)
  (i : V) (extra : ℕ)

def selected : Binder (paper D u) (Stock.census V) where
  mode := (Stock.census V).fire i
  front := i
  east := Finset.mem_singleton_self _
  path _ := []
  span j hj := by
    have h : j = i := Finset.mem_singleton.mp hj
    subst j
    rfl
  extra := extra

theorem filed : (selected D u i extra).mode = (Stock.census V).fire i ∧
    (selected D u i extra).center = ActualRunQlocalNativeTuple.root D i ∧
    (selected D u i extra).length = (paper D u).height i + extra := by
  refine ⟨rfl,rfl,?_⟩
  change extra + ∑ j ∈ ({i}:Finset V), (0 + (paper D u).height j) = _
  simp [Nat.add_comm]

end YM.Integration.WilsonOriginalProjectedCurvatureBinder
