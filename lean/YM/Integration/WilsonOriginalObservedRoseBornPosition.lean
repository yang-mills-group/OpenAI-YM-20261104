import YM.Integration.WilsonOriginalObservedRoseBornLedger
import YM.Integration.WilsonMaxwellThermometerKineticCoordinate

/-! The finite physical mesh retains its own Galop and the offset to the conventional inversion mesh. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornPosition
open Finset PowerSeries Lattice Wilson Maxwell XSpace XSpace.Rose XSpace.Structure1 XSpace.Cirrus
open FVA2 FVA2.Register FVA2.Scale MS MS.WilsonBridge.Coupling XSpace.Normalize
open WilsonOriginalObservedRoseBornLedger
open WilsonOlderFreshSoftSocketStationPortfolio (reading)
open scoped Classical
variable {G:Gauge}(Z:WilsonPrescription G){Y:Type}[Fintype Y](μ:Y→ℂ)(r:ℝ)
    (points:Y→Sample 3)(g:ℕ→ℝ)(N:ℕ)(rows:Y→Badge→ℂ)(raw:ℂ)(earned:ℝ)

def Balance:Prop:=∀(j k:ℕ), k≤N → ‖(g k:ℂ)‖≤1 →
    let z:=XSpace.Rose.tag G
    let c:=center Z.scheme (V:=Z.store) μ points z j (g k:ℂ)
    let d:=debit Z.scheme (V:=Z.store) μ r points z j (g k:ℂ) rows
    let t:=truncation Z.scheme (V:=Z.store) μ points z j (g k:ℂ)
    let b:=cost Z.scheme (V:=Z.store) μ r points z j (g k:ℂ) rows
    ‖raw-c-d‖≤earned+t ∧ ‖raw-c‖≤earned+t+b ∧ ∀n:ℕ,
      let printed:=WilsonMaxwellThermometerKineticCoordinate.printed Z (Z.run.step n) j (g k)
      let offset:=c.re-printed
      |raw.re-printed-(d.re+offset)|≤earned+t

theorem original (bought:‖raw-reading μ ((r:ℂ)^14) rows‖≤earned):Balance Z μ r points g N rows raw earned:=by
  intro j k _ low z c d t b
  obtain ⟨first,second⟩:=WilsonOriginalObservedRoseBornLedger.observed Z.scheme (V:=Z.store) μ r
    points z j (g k:ℂ) rows low raw earned bought
  refine ⟨first,second,?_⟩
  intro n printed offset
  have e:raw.re-printed-(d.re+offset)=(raw-c-d).re:=by
    dsimp only [offset,Complex.sub_re]
    ring
  rw [e]
  exact (Complex.abs_re_le_norm _).trans first

end YM.Integration.WilsonOriginalObservedRoseBornPosition
