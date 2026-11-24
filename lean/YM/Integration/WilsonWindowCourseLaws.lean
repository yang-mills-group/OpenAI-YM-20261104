import YM.Integration.WilsonWindowVacuumLaws
import YM.QuadraticLocal.Perspective.Tenants
import YM.QuadraticLocal.Class.Clockwork
import YM.QuadraticLocal.Class.Raffle
import YM.QuadraticLocal.HaloMix.Lotus
import YM.QuadraticLocal.Neighborhood.Era
import YM.QuadraticLocal.Tariff.Torch

/-! Purchase the elementary laws of the original marked university on the
chosen physical price. The same roots, physical roll, books, and future delay
are used for every conjunct of the original `Tracks.vine`. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonWindowCourseLaws

open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open ThroughLaunch Pressure QuadraticLocal QuadraticLocal.Mentor
open WilsonWindowBookPurchase WilsonWindowVacuumLaws
open scoped Classical

variable {G : Gauge} {ψ : ℕ → ℕ} {s : Sheet G} {price : MapPrices}

theorem walking : Permitted (Spill.Walking.short G ψ) s price := by
  intro R C E flags
  refine ⟨0,?_⟩
  intro l hl D w q Z post scouts pocket P θ tab book sold V
  exact Spill.Walking.outcomes (X := raised s price l) G R V ψ

theorem raffle : Permitted (Spill.Raffle.scroll G ψ) s price := by
  intro R C E flags
  refine ⟨0,?_⟩
  intro l hl D w q Z post scouts pocket P θ tab book sold V
  exact Spill.Raffle.accrues (X := raised s price l) G R V ψ

theorem cycles : Permitted (Rebirth.Scholar.cycles (ψ := ψ) G) s price := by
  intro R C E flags
  refine ⟨0,?_⟩
  intro l hl D w q Z post scouts pocket P θ tab book sold V
  exact Rebirth.Scholar.renews (X := raised s price l) D R tab V

theorem pavilion : Permitted (MintClock.Pavilion.scroll (ψ := ψ) G) s price := by
  intro R C E flags
  refine ⟨0,?_⟩
  intro l hl D w q Z post scouts pocket P θ tab book sold V
  exact MintClock.Pavilion.builder (X := raised s price l) R D tab (show Targets _ _ from C) ψ book V

theorem rent : Permitted (MintClock.Pavilion.Quantity.renter (ψ := ψ) G) s price := by
  intro R C E flags
  refine ⟨0,?_⟩
  intro l hl D w q Z post scouts pocket P θ tab book sold V
  exact MintClock.Pavilion.Quantity.builder (X := raised s price l) D V

theorem vineyard (split : MintClock.splits ≤ ψ) :
    Permitted (MintClock.vineyard (ψ := ψ) G split) s price := by
  intro R C E flags
  obtain ⟨n,hn⟩ := MintClock.opens (G := G) R ψ split
  refine ⟨n,?_⟩
  intro l hl D w q Z post scouts pocket P θ tab book sold V
  obtain ⟨forecast⟩ := Mentor.speculate (X := raised s price l) R D tab ψ book
  have employed (x : ℕ) : MintClock.Employment R ψ x (D.L x) :=
    hn x _ ((hl x).trans (D.large x).need)
  let targets : Targets (ThroughLaunch.raise s l) price := C
  obtain ⟨V₁,h₁,holds⟩ := MintClock.hospitals (X := raised s price l) R D tab
    targets ψ book forecast V employed
  obtain ⟨V₂,h₂,regents⟩ := MintClock.regents (X := raised s price l) R D tab
    targets ψ book forecast V₁ employed
  exact ⟨V₂,h₁.trans h₂,fun Y hY => ⟨forecast,holds Y (h₂.trans hY),regents Y hY⟩⟩

theorem vine {C : VowsR.LawScroll G ψ} (split : MintClock.splits ≤ ψ)
    (paid : Permitted C s price) :
    Permitted (Advent.Sycamore.Tracks.vine C split) s price := by
  unfold Advent.Sycamore.Tracks.vine
  exact both (vineyard split) (both volume
    (both (both paid genesis) (both raffle (both readyYear training))))

/-- This is the specific additional flow charged by the manuscript's
variable-house proof before it opens the marked course. -/
theorem physical_course {C : VowsR.LawScroll G ψ} (split : MintClock.splits ≤ ψ)
    (paid : Permitted C s price) :
    Permitted (Advent.Sycamore.Tracks.vine
      (MintClock.both G ψ C
        (MintClock.both G ψ (Spill.Walking.short G ψ)
          (MintClock.both G ψ
            (MintClock.both G ψ (MintClock.Pavilion.scroll (ψ := ψ) G)
              (MintClock.Pavilion.Quantity.renter (ψ := ψ) G))
            (Rebirth.Scholar.cycles (ψ := ψ) G)))) split) s price := by
  apply vine split
  exact both paid (both walking (both (both pavilion rent) cycles))

end YM.Integration.WilsonWindowCourseLaws
end

