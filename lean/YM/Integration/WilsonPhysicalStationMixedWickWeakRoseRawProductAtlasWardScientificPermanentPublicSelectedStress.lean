import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressEntry
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicMovingJets
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicSelectedStress
open Function Filter Set MeasureTheory Spec Extraction Table Maxwell Maxwell.Free
open Climb Lattice RG Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction Table
open PhysMS.Frame WilsonPhysicalWeakRisingStaff WilsonPhysicalWeakSundial
open scoped Topology BigOperators Classical
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true


open scoped Matrix


open WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressRows


variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}

open WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressMenus

theorem original (F:Final C f S)(X:Scaling S)(first:Pert.FirstExtension F X)
    (J:ℝ→PhysMS.tower S)(leading:Leading F J)(simple:G.Simple)
    (Q:OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)(foundation:OPE.Orbits.Foundation F Q)
    {n:ℕ}(q:Fin n→(Bel C.book).Tag)(marks:Fin n→Bool)(ab:Fin n→Axis×Axis)(j:ℕ)
    {K:Set (Points n)}(compact:IsCompact K)(inside:K⊆conf n){ε:ℝ}(pos:0<ε):
    ∀ᶠ k:ℕ in atTop,∀x∈K,∀p:Viewers F,
      ‖iteratedFDeriv ℝ j (fun y=>S.useAt (spectator F p) (X.r k • y)
          (Pert.scaledPhysical X F.sector.energy k q marks ab)) x-
        iteratedFDeriv ℝ j (Ward.disc (Pert.freeWithStress C.labels q marks ab)) x‖≤ε:=by
  obtain ⟨D,B,buyer⟩:=WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressMenus.original C
  obtain ⟨V,posV,income⟩:=buyer F X first q marks ab
  have wallet:=WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicMovingJets.original F X first J leading simple Q foundation (fun i=>WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressMenus.height (q i) (marks i))
    (fun i=>WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressMenus.basis B (q i) (marks i)) j compact inside
  have cst:Tendsto (fun _:ℕ=>V) atTop (𝓝 V):=tendsto_const_nhds
  have tail:Tendsto (fun k:ℕ=>(X.r k)^3*V) atTop (𝓝 0):=by simpa using (X.drips.pow 3).mul cst
  have tiny:=tail.eventually_lt_const (half_pos pos)
  have mean:=first.jets n j q marks ab compact inside (half_pos pos)
  filter_upwards [wallet,income,tiny,mean] with k bank paid small measured
  intro x hx p
  have back:=bank x hx p none (fun i=>WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressMenus.pupil F X (q i) (ab i) k (marks i))
  rw [WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressEntry.original F X k q marks ab p,WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressEntry.original F X k q marks ab none] at back
  have gap:=back.trans (mul_le_mul_of_nonneg_left paid (pow_nonneg (X.positive k).le 3))
  let A:=iteratedFDeriv ℝ j (fun y=>S.useAt (spectator F p) (X.r k • y) (Pert.scaledPhysical X F.sector.energy k q marks ab)) x
  let M:=iteratedFDeriv ℝ j (fun y=>Ward.disc (Pert.scaledPhysical X F.sector.energy k q marks ab) (X.r k • y)) x
  let E:=iteratedFDeriv ℝ j (Ward.disc (Pert.freeWithStress C.labels q marks ab)) x
  change ‖A-E‖≤ε
  change ‖A-M‖≤(X.r k)^3*V at gap
  have m:‖M-E‖≤ε/2:=measured x hx
  have step:‖A-E‖≤‖A-M‖+‖M-E‖:=by simpa only [dist_eq_norm] using dist_triangle A M E
  linarith

end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicSelectedStress
end
