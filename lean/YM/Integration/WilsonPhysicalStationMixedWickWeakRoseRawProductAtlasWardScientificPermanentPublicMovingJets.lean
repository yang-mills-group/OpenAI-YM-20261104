import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicSparsePhases
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicJetSalary
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicMovingJets
open Function Filter Set MeasureTheory Spec Extraction Table Maxwell Maxwell.Free
open Climb Lattice RG Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction Table
open PhysMS.Frame WilsonPhysicalWeakRisingStaff WilsonPhysicalWeakSundial
open scoped Topology BigOperators Classical
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true



variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}

theorem balance {n:ℕ}(F:Final C f S)(X:Scaling S)(d:Caps n)(j:ℕ)(k:ℕ)(x:Points n)(hx:x∈conf n)
    (p q:Viewers F){I:Fin n→Type*}[∀i,Fintype (I i)]
    (B:∀i,Module.Basis (I i) ℂ ((Spin.comparator C.book).Field (d i)))
    (v:MaxwellSlots C d)(a:ℝ)
    (paid:∀t:(i:Fin n)→I i,
      ‖iteratedFDeriv ℝ j (measured F p (X.U k) (fun i=>B i (t i)) (X.r k)) x-
        iteratedFDeriv ℝ j (measured F q (X.U k) (fun i=>B i (t i)) (X.r k)) x‖≤a):
    ‖iteratedFDeriv ℝ j (measured F p (X.U k) v (X.r k)) x-
      iteratedFDeriv ℝ j (measured F q (X.U k) v (X.r k)) x‖≤a*WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicJetSalary.salary B v:=by
  let wallet:=fun i=>(X.U k (d i)).toLinearMap
  let D:=((jet F j p d (X.r k) x)-(jet F j q d (X.r k) x)).compLinearMap wallet
  have seen (v:MaxwellSlots C d):D v=iteratedFDeriv ℝ j (measured F p (X.U k) v (X.r k)) x-
      iteratedFDeriv ℝ j (measured F q (X.U k) v (X.r k)) x:=by
    change jet F j p d (X.r k) x (fun i=>X.U k (d i) (v i))-
      jet F j q d (X.r k) x (fun i=>X.U k (d i) (v i))=_
    rw [jet_from_measure F _ _ _ _ j (Work.A05.smul_conf (X.positive k) hx),
      jet_from_measure F _ _ _ _ j (Work.A05.smul_conf (X.positive k) hx)]
  rw [←seen v]
  exact WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicJetSalary.original D B v a fun t=>by rw [seen];exact paid t

theorem original (F:Final C f S)(X:Scaling S)(first:Pert.FirstExtension F X)
    (J:ℝ→PhysMS.tower S)(leading:Leading F J)(simple:G.Simple)
    (Q:OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)(foundation:OPE.Orbits.Foundation F Q)
    {n:ℕ}(d:Caps n){I:Fin n→Type*}[∀i,Fintype (I i)]
    (B:∀i,Module.Basis (I i) ℂ ((Spin.comparator C.book).Field (d i)))
    (j:ℕ){K:Set (Points n)}(compact:IsCompact K)(inside:K⊆conf n):
    ∀ᶠ k:ℕ in atTop,∀x∈K,∀p q:Viewers F,∀v:MaxwellSlots C d,
      ‖iteratedFDeriv ℝ j (measured F p (X.U k) v (X.r k)) x-
        iteratedFDeriv ℝ j (measured F q (X.U k) v (X.r k)) x‖≤(X.r k)^3*WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicJetSalary.salary B v:=by
  have bank:∀ᶠ k:ℕ in atTop,∀t:(i:Fin n)→I i,∀x∈K,∀p q:Viewers F,
      ‖iteratedFDeriv ℝ j (measured F p (X.U k) (fun i=>B i (t i)) (X.r k)) x-
        iteratedFDeriv ℝ j (measured F q (X.U k) (fun i=>B i (t i)) (X.r k)) x‖≤(X.r k)^3:=
    Filter.eventually_all.mpr fun t=>(WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicSparsePhases.original F X first J leading simple Q foundation d (fun i=>B i (t i)) j compact inside).2
  filter_upwards [bank] with k earned x hx p q v
  exact balance F X d j k x (inside hx) p q B v _ fun t=>earned t x hx p q

end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicMovingJets
end
