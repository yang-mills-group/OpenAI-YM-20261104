import YM.Integration.WilsonGeneralReducedPhysicalSelfBoard
import YM.Integration.WilsonIndependentFittedReflectedGram

/-! A single evaluated public vector is planted as the two conjugate fields of
the fully normalized finite Wilson computation before the smooth reflected
sites are drawn. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonGeneralReducedPhysicalSelfFullWord
open Filter Set Function Finset MeasureTheory Lattice Maxwell MS MS.Land MS.Menus Local.Physical
open XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Register Table.Pairing PowerSeries
open WilsonPositionProgramPublicBulb WilsonPositionProgramPublicReflectedRead WilsonPositionProgramPublicDirectoryCoin
open WilsonPositionProgramPublicContrast (assay)
open WilsonOriginalPublicPlantedGram (measured)
open WilsonIndependentFittedReflectedGram (fields paired)
open WilsonIndependentFittedNumericalProduct (fitted numerical pivot)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonPositionProgramPublicDirectoryBoard (table)
open scoped Classical BigOperators Topology
variable {G:Gauge}(Z:WilsonPrescription G)(a:Axis){B:Deck G}{h:ℕ}
local notation "I" => Glyph B h
local notation "leg" => (id : I→I)

def reflected (d:I→ℂ):Fin 2→I→ℂ:=![fun i=>star (d i),d]
def finiteWord (j:ℕ)(s:Sample 2)(d:I→ℂ):PowerSeries ℂ:=
  fitted Z.scheme s (fields Z a leg j s) (fun l i=>C (reflected d l i))

private theorem constantCash (q:ℕ)(u:ℝ)(z:ℂ):cash q u (C z)=z:=by
  simp [cash,coeff_C]

private theorem constantProduct {α:Type}[Fintype α]{β:α→Type}[∀a,Fintype (β a)]
    (Q:ℕ)(u:ℝ)(W:Initialize G)(s:Sample 2)(P:(i:α)→β i→Bare.Series (W.tree s.F.p) G)(d:(i:α)→β i→ℂ):
    cash Q u (fitted W s P (fun i b=>C (d i b)))=numerical W s P (fun i b=>C (d i b)) Q Q u:=by
  rw [WilsonIndependentFittedNumericalProduct.expanded,WilsonIndependentFittedNumericalProduct.added]
  unfold numerical
  apply sum_congr rfl
  intro b _
  simp only [constantCash,←map_prod]
  simp only [cash,coeff_mul_C,mul_sum]
  apply sum_congr rfl
  intro k _
  ring

theorem atNode (j:ℕ){cap:ℕ}(P:Handoff.Directory Z j cap)(s:Sample 2)(d:I→ℂ)(q:ℕ)(u:ℝ)
    (onBoard:s.F=Z.run.step j)(room:Handoff.Directory.budget G 2 h+q≤cap):
    cash q u (finiteWord Z a j s d)=assay d d (measured Z a leg q P u s):=by
  rw [finiteWord,constantProduct]
  have conj:(fun l i=>C (reflected d l i))=paired (fun i=>C (d i)):=by
    funext l i
    fin_cases l <;>simp [paired,reflected]
  rw [conj,WilsonIndependentFittedReflectedGram.purchased Z a leg j P s (fun i=>C (d i)) q q u onBoard room]
  simp only [constantCash]

end YM.Integration.WilsonGeneralReducedPhysicalSelfFullWord
