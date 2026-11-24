import YM.MS.Arts.Range

set_option autoImplicit false
noncomputable section
namespace YM.MS.Alps
open Function Set Filter Finset MeasureTheory Real Plane Koszul Flux Landau Arts
open Momentum Metric
open scoped Topology ContDiff
variable {G : Gauge} {A P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {m : ℕ}

def amount (a:ℂ)(t:ℝ): ℂ:= Complex.exp ((t:ℂ)*a)
def mass (l:Legs (Mode (Cfield G m) P)): ℤ:= fieldDim wfield l
def sr (t:ℝ) : Legs (Mode A P)→ Legs (Mode A P):= List.map (fun i=> (i.1,Real.exp t • i.2))
def plow (a:ℂ)(t:ℝ)(F:Mob G): Mob G := fun _ l=> amount (a+(mass l:ℂ)) t * F _ (sr t l)
end YM.MS.Alps
