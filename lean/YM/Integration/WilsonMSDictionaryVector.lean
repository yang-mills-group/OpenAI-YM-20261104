import YM.Integration.WilsonMSDictionaryFarRead
import YM.Integration.WilsonPositionHomogeneousComparison

/-! Multilinear testing of the ordinary MS matching formula on the physical Maxwell quotient.
Both the finite Gram reading and the independent prediction are reassembled through the
same original field basis on all the inputs and the entire output space through grade h. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMSDictionaryVector
open Filter Function Lattice Maxwell XSpace XSpace.Normalize XSpace.Structure1
open FVA2 FVA2.Register FVA2.Scale FVA2.O FVA2.O.Score FVA2.O.Project
open MS MS.Land MS.Fleet MS.Theater PowerSeries RG17 WilsonMSDictionaryFarRead
open scoped Classical BigOperators Topology
variable {G : Gauge} (C : Family G) {n : ℕ} (d : Fin n → ℕ) (h : ℕ)

/-- The cumulative sector contains each legitimate positive output as well as its lower counterterms. -/
abbrev basis (k : ℕ) : Module.Basis (Dframe.Toon G k) ℂ (Free C k) :=
  (Daylight (Press.portDeck G) k).map (Maxwell.Free.fields C.labels k).symm

/-- Evaluate every input of the ordinary coefficient at its actual field, then sum over the full output. -/
def assemble (v : (i : Fin n) → Free C (d i))
    (a : ((i : Fin n) → Dframe.Toon G (d i)) → Dframe.Toon G h → ℂ) : Free C h :=
  ∑ j : (i : Fin n) → Dframe.Toon G (d i),
    (∏ i, (basis C (d i)).repr (v i) (j i)) •
      (∑ b : Dframe.Toon G h, a j b • basis C h b)

variable (Z : WilsonPrescription G) (T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
  (ν : ℝ) (v : (i : Fin n) → Free C (d i)) (ψ : Test n)

def prediction (q : ℕ) (t : ℝ) : Free C h := assemble C d h v
  (fun j b => cutoff q t (converted Z T ν (fun i=>Dframe.flash (j i)) ψ (Dframe.flash b)))

def experiment (P : Read.Geology G h) (q : ℕ) (t s : ℝ) : Free C h := assemble C d h v
  (fun j b => cutoff q t (nearby Z T ν P (fun i=>Dframe.flash (j i)) ψ s b))

theorem experiment_limit {hG : G.Simple} {σ : Prescription (Press.portDeck G)} {dial : Bool}
    (M : Main.Match Z hG T σ dial) (P : Read.Geology G h)
    (live : Read.Detected (Measure.outlook Z.scheme Z.criterion) P) (q : ℕ) (t : ℝ) :
    Tendsto (experiment C d h Z T ν v ψ P q t) atTop (𝓝 (prediction C d h Z T ν v ψ q t)) := by
  unfold experiment prediction assemble
  apply tendsto_finsetSum
  intro j _
  apply tendsto_const_nhds.smul
  apply tendsto_finsetSum
  intro b _
  exact (far Z T ν M P live (fun i=>Dframe.flash (j i)) ψ b q t).smul tendsto_const_nhds

end YM.Integration.WilsonMSDictionaryVector
