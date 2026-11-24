import YM.LocalLTE.Furnace.Feed
import YM.LocalLTE.Tile.Allot
import YM.QuadraticLocal.Advent
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Seminal

/-! The singleton-parameter Spring may be built from the guide selected by
the actual marked course, with both of its physical mergers still available. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullHouse
open Function Filter Set Lattice Wilson RG RG.Shoot Marker Overlay Extra.Histories
open PhysicalNext Repeat Legato Graces Roost Mallow
open Pressure Testing Input Precision Org Supply Push SectorMeasure PriceCompiler
open ConnectedActivityE6 Progress.DirectedRecipe
open AllOrder AllOrder.Transit WheelP AllOrder.Floe
open AnalyticBridge VerifiedReset Time UVNext.CouplingReset QuadraticLocal.Advent
open scoped Topology Classical
variable {G : Gauge} (R : Run G) {m N per k i : ℕ}
variable (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin)
    (Ψ : ∀ j, RG.Rep G (R.family.side j per))
    (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)

def point : Icc (0 : ℝ) 0 := ⟨0, by simp⟩

include course
theorem original (start : m ≤ i) (live : i < N) :
    ∃ S : Spring R.kit N i per 0 0 (fun _ => Ψ (i+1)),
      let K := houseS S point
      let c := R.alloy.B.a
      Nonempty (QuadraticLocal.Travel.Walk K (Ψ i)
        (forecastK c i R.kit.scout (Ψ (i+1)).beta / 8)
        (forecastK c i R.kit.scout (Ψ (i+1)).beta)
        (quoteHard c i R.kit.book (Ψ (i+1)).beta) (QuadraticLocal.Willow.haloSlack (c.budget i).B)) := by
  obtain ⟨K, price, walk⟩ := (course.2 i start live).earns
  let U := Ψ (i+1)
  have seen := QuadraticLocal.Advent.later R π Γ Ψ course (Nat.le_succ_of_le start) live
  have banded : U.beta ∈ band R.alloy.B.a (i+1) := by
    change (Ψ (i+1)).beta ∈ _
    rw [seen.beta]
    exact ((R.T.sticks N per).prices (i+1) (Nat.zero_le _) live).2
  have sound := And.intro seen.truep banded
  have curve : Curve (R.alloy.B.a.budget (i+1)) (fun _ => U) (Icc 0 0) :=
    (Urns.uniform_curve _ U).mono (Set.subset_univ _)
  let X : Roof.Embrasure (U:=R.alloy) (Y:=R.kit.shape) (N:=N)
      (m:=i) (n:=per) (fun _ => U) (Icc 0 0) 0 :=
    { houses := fun _ => K, honors := fun _ => price, he := point.2,
      sister := fun _ => Meadow.intern K, agrees := fun _ => rfl }
  let F := R.kit.pledging
  let W := Classical.choice (Rain.learns (R:=R.kit.shape) (A:=R.alloy)
    live F.conducts.income.grow.1 F.conducts.full)
  obtain ⟨d, hD, hE⟩ := (Rain.topped F live X curve (fun _ _ => sound) R.kit.inn
    (R.kit.settles _ _) R.kit.floor W isCompact_Icc).exists
  let forest := Classical.choice
    (Tree.select (R.alloy.B.a.clock.op i per).ratio (R.alloy.B.a.clock.op i per).patch.odd_side)
  exact ⟨⟨curve, fun _ _ => sound, X, W, d, forest,
    fun x hx => ⟨hE x hx, hD x hx⟩⟩, walk⟩

end YM.Integration.WilsonOriginalNullHouse
