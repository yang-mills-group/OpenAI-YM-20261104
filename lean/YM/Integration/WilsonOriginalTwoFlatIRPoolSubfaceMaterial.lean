import YM.Integration.WilsonOriginalTwoFlatIRPoolSubfaceCourse
import YM.Integration.WilsonMovingForkStencilCatalogue
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRPoolSubfaceMaterial
open Finset Function Lattice Wilson RG Marker Source Labels Trace.Pilot OPE
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonOriginalMixedBlockRows
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Extra.Histories Extra.Trajectories Extra.Multi
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Embroider
open WilsonMovingForkPrintedFile (parent Board)
open WilsonMovingForkStencilCatalogue (Catalogue table)
open WilsonMovingForkDepositedPrint (Sheet board polynomial)
open WilsonMovingForkStencilLine (Received)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonOriginalTwoFlatIRPoolSubfaceCourse (expanded)
open WilsonThermometerUnitFilingCoarse (reading)
open Pert.Asymptotics Planned.GuardedAtom Extra.Histories Next.Foundations
open RG16 RG16.Literal Trace.Physical.GermGraph
open RG12 Bid Extra.Histories.Relay MergeProof MergeProof.Accent Overlay Cells Trace.Physical
open scoped Classical BigOperators

def print {G : Gauge} {n : ℕ} {side : Side} {pins : Fin n → Site side}
    (page : Board G pins) (g : ℝ) (U : Config G side) : Marker.Poly (Stock.census (Fin n)) :=
  WilsonOriginalTwoFlatIRMounted.value page.binder page.load page.copies g page.wallet U

variable {G:Gauge}(R:Run G){n K N per i:ℕ}(grades:Fin n→ℕ)
  (source:Catalogue R grades K)(v:∀j,R.family.label (grades j))
  (ξ:Fin n→Site (R.family.side K per))(live:i<K)(s:(Stock.census (Fin n)).Mode)

def word (U:Config G (R.family.side i per)):ℂ:=
  ∑q:Selection R grades s.val,weight R grades N per K v s.val q*
    (print (table source N per v ξ (expanded R grades s q) i live) (regulatorRun R.family N per i) U).part s

/-- Hear the complete filed ordinary component on its own measured coordinates, including
all marked coefficients that have become scalar in its previous history. -/
theorem original (raw:Selection R grades s.val → Config G (R.family.side i per) → Marker.Poly (Stock.census (Fin n)))
    (received:∀q,∃H:Sheet R N i (parent R live.le per ξ),
      source N per ξ (expanded R grades s q) i live=some H ∧ Received H (raw q)):
    (∀U,((R.family.path.rep N per i).eval U:ℂ)*word R grades (N:=N) source v ξ live s U=
      ∑q:Selection R grades s.val,weight R grades N per K v s.val q*(raw q U).part s) ∧
    (∑q:Selection R grades s.val,weight R grades N per K v s.val q*
      reading R (N:=N) (fun U=>(raw q U).part s) i le_rfl)=word R grades (N:=N) source v ξ live s 1:=by
  classical
  refine ⟨?_,?_⟩
  · intro U
    unfold WilsonOriginalTwoFlatIRPoolSubfaceMaterial.word
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    obtain ⟨H,posted,read⟩:=received q
    have same : table source N per v ξ (expanded R grades s q) i live = board H := by
      unfold WilsonMovingForkStencilCatalogue.table
      rw [posted]
    rw [same,read.2.1 U,Poly.part_smul]
    unfold print
    ring
  · unfold word
    apply Finset.sum_congr rfl
    intro q _
    obtain ⟨H,posted,read⟩:=received q
    have same : table source N per v ξ (expanded R grades s q) i live = board H := by
      unfold WilsonMovingForkStencilCatalogue.table
      rw [posted]
    rw [read.2.2 s,same]
    exact congrArg (fun t:Marker.Poly (Stock.census (Fin n))=>weight R grades N per K v s.val q*t.part s)
      (WilsonMovingForkDepositedPrint.flat H (regulatorRun R.family N per i)).symm

def numerator (raw : Selection R grades s.val → Config G (R.family.side i per) → Marker.Poly (Stock.census (Fin n)))
    (U : Config G (R.family.side i per)) : ℂ :=
  ∑ q : Selection R grades s.val, weight R grades N per K v s.val q * (raw q U).part s

/-- Both old flat reports apply the original normalized functional to the same whole numerator. -/
theorem stops (raw:Selection R grades s.val → Config G (R.family.side i per) → Marker.Poly (Stock.census (Fin n)))
    (received:∀q,∃H:Sheet R N i (parent R live.le per ξ),
      source N per ξ (expanded R grades s q) i live=some H ∧ Received H (raw q)):
    (∀ (e : ℕ) (he : e ≤ i),
      reading R (N:=N) (numerator R grades (K:=K) (N:=N) v s raw) e he =
      reading R (N:=N) (fun U => ((R.family.path.rep N per i).eval U : ℂ) *
        word R grades (N:=N) source v ξ live s U) e he) ∧
    reading R (N:=N) (numerator R grades (K:=K) (N:=N) v s raw) i le_rfl =
      word R grades (N:=N) source v ξ live s 1 := by
  classical
  have income:=original R grades source v ξ live s raw received
  refine ⟨fun e older=>congrArg (fun z=>reading R (N:=N) z e older) (funext (fun U=>(income.1 U).symm)),?_⟩
  refine Eq.trans ?_ income.2
  unfold WilsonOriginalTwoFlatIRPoolSubfaceMaterial.numerator WilsonThermometerUnitFilingCoarse.reading
  simp only [gust_base,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

end YM.Integration.WilsonOriginalTwoFlatIRPoolSubfaceMaterial

