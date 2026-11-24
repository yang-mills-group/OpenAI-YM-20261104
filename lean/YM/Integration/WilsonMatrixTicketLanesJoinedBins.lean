import YM.Integration.WilsonMatrixTicketLanesMarkedCatalogue
import YM.OPE.Compatible.Eyrie.Return

/-! Keep the ordinary physical section bounds and the matrix-screen estimate
on one chosen catalogue and precisely its own projected table. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesJoinedBins
open OPE.RigE
open Set Function MeasureTheory Filter Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Guard Next.Foundations Local Next.Rank Edition Spindle Extra.Multi Motion
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction Extraction.Lease Exponential Bid Next.Extract RelayDifference Opening
open Labels Maxwell
open YM.MergeProof
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {C : Family G}
variable (H:C.Makes)(B:Stock.Tabs C.path.levels){W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (h:Scrim C W u ψ φ δ ζ r D)(hF:Fridge C u ζ){f:Extraction.Order} {N p d:ℕ} (V:∀ d:ℕ,SectionData (C.labels.level d))(R:Mark.Weave G)(hV:∀ d, Mark.Portfolio C.params (V d) (R d))(hG:G.Simple)
include h hV H hG hF B

theorem issue (hb : ∀ d : ℕ, ∃ a : ℕ → ℝ, Braze (C := C) (V d) a) :
    ∃ P tr, Hearthside C V R P tr ζ ∧ ∀ (T : Table C.book) (L : Dash.Bin T) (f : Extraction.Order)
      (a : ∀ d : ℕ, ℕ → CoordMap C d), Projected tr f L a →
      ∀ d : ℕ, OPE.RigE.StrongBin C L f d := by
  choose price paid using hb
  choose E Y U hearth sun using fun d => glowT_is H B h hF (V d) (hV d).valid hG (paid d)
  obtain ⟨tr,stock⟩ := WilsonMatrixTicketLanesMarkedCatalogue.file H B h hF V R hV hG E Y U hearth
  refine ⟨_,tr,stock,?_⟩
  intro T L f a projected d
  obtain ⟨r,m,micro⟩ := OPE.RigE.uniform_micro R (V d) (hV d)
  refine ⟨r,m,fun x kernel bounded => OPE.RigE.marshal_strong H (V d) R (hV d) _ (hearth d)
    micro (sun d) x bounded (fun j => ((stock.foundation.step d j.1 j.2).ker) ▸
    (show x j ∈ LinearMap.ker (tr.step d j).toLinearMap from LinearMap.mem_ker.mpr ?_))⟩
  rw [← projected.same d];exact kernel j

end YM.Integration.WilsonMatrixTicketLanesJoinedBins
