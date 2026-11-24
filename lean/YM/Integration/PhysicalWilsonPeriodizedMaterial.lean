import YM.Integration.PhysicalWilsonMaterialGenerators
import YM.Integration.PhysicalWilsonPeriodizedAffine

/-! Actual nonlinear finite vertices, with their original varying fields, on
the independently prescribed periodic covariance and stationary coefficients. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.PhysicalWilsonPeriodizedMaterial
open Finset Function Matrix Lattice Wilson RG RG.Supply Precision Tree Exterior Laurent Bloch
open Marker Multi PhysicalNext.Repeat.Legato Comparison.RG02 Comparison.RG02.Order
open Comparison.RG02.Cumulants Next.Rank Next.SectorChange WilsonCoeffUV FreeResolvent MeasureTheory
open scoped Classical BigOperators Matrix.Norms.Frobenius

variable {G:Gauge} {V:Type} [Fintype V] [DecidableEq V] {Γ:Census V}
def drawn {c f:Side} {S:StepData c f} {p:Clip} {P:PathData G} {O:ChartRatio G}
    (_:Bulk.Kernel S p P O) (F:Forest S.ratio) (W:Bulk.Colors Γ G f) (y:Bulk.Joint S F (G:=G)) (r:ℕ):
    Hot (Board Γ r)→Normal.poly (Key F G):=
  Assembly.generator y (Bulk.hinge F) W.power (PhysicalWilsonJointMaterial.mark S F W)
    (PhysicalWilsonJointMaterial.measured S F W p P O) r

variable (R:Run G) (N m p:ℕ) (hm:m<N)
local notation "S" => R.family.path.levels.clock.op m p
local notation "F₀" => repeatF (S)
local notation "K₀" => (RunFormalChain.fromRun R).step N m p hm
variable (B:fieldDir G (R.family.side m p) 1) (W:Bulk.Colors Γ G (R.family.side (m+1) p)) (r:ℕ)

def rows:Hot (Board Γ r)→Normal.poly (Key (F₀) G):=drawn (K₀) (F₀) W
  ((1:ℝ),B,profile (F₀) (PhysicalWilsonPeriodizedAffine.relativeMean R N m p B)) r

theorem authentic:
    PhysicalWilsonPeriodizedAffine.vertex R N m p hm B W r=rows R N m p hm B W r:=
  PhysicalWilsonMaterialGenerators.generators W (K₀) (F₀) (PhysicalWilsonPeriodizedProgram.branch (S)) _ _ r

def reference:Grade Γ r:=Poly.inject fun s=>
  ∫z,Cloud.paint z (Cloud.integrand (rows R N m p hm B W r) s)
    ∂Gaussian.cloud (PhysicalWilsonPeriodizedProgram.kernel R N m p)

variable (F:Forest (R.family.path.levels.clock.op m p).ratio)
variable (tag:(R.family.path.levels.clock.op m p).Choices)
theorem original (hw:Bulk.Well W):
    Bulk.Fk (K₀) F tag W B r=reference R N m p hm B W r:=by
  rw [PhysicalWilsonPeriodizedAffine.program R N m p hm B W r F tag hw]
  unfold PhysicalWilsonPeriodizedAffine.cover reference
  rw [authentic R N m p hm B W r]

theorem connected (hw:Bulk.Well W) (s:(Board Γ r).Mode):
    (logMarked (Bulk.Fk (K₀) F tag W B r)).part s=
      (logMarked (reference R N m p hm B W r)).part s:=
  congrArg (fun Z=> (logMarked Z).part s) (original R N m p hm B W r F tag hw)

end YM.Integration.PhysicalWilsonPeriodizedMaterial
end
