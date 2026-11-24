import YM.Integration.WilsonPhysicalStationThermalCoordinates
import YM.Integration.WilsonPhysicalStationWickFees
import YM.Integration.WilsonPhysicalStationHorizontalWallet

/-! Directional Wick testing on one enrolled Wilson sensor, at its original
sites and with its complete signed numerator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationDirectedRead
open Function Filter RG Wilson MergeProof Labels Source Lattice
open Next.Rank Next.Rank.East Next.Rank.Price MergeProof.East
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open WilsonPhysicalStationHorizontalWallet (normAt)
open WilsonPhysicalStationThermalPair (cell)
open WilsonPhysicalStationThermalCoordinates (filed)
open WilsonPhysicalStationTableJump (pair)
open scoped BigOperators Classical Topology
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {H:(Bel R.family.book).Hierarchy}
    {D:ℕ} (A:Vane R.family D) (d:Fin (D+1)) {N p:ℕ}
    (check:A.checked f H D) (top:A.k<N) (j:ℕ) (o:Fin 2 → Cover) (z:(Bel R.family.book).Field d)
local notation "F₀" => R.family.labels.level d
local notation "P₀" => (shrink R.family A.k N p)⁻¹
local notation "M₀" => Station.mag R.family.path.levels A.b A.k
local notation "faculty" => cell R A d (p:=p) check top j o
local notation "ear" => pair R d N p j o

theorem heard (y:R.family.label d) :
    ear y (A.wheel.atCut (N,p) d z)=
      ∑ a,filed R A d N p y a * faculty (Pi.single a 1) z := by
  calc
    _ = ear (∑ a,filed R A d N p y a • WilsonPhysicalStationThermalPair.raw R A d (p:=p) check top (Pi.single a 1)) _ :=
      congrArg (fun w=>ear w (A.wheel.atCut (N,p) d z)) (WilsonPhysicalStationThermalCoordinates.expands R A d (p:=p) check top y)
    _ = _ := WilsonPhysicalStationWickFees.sum_read R d N p j o (A.wheel.atCut (N,p) d z) _ _

theorem original (y:R.family.label d) (born:(F₀).Index → ℂ) (Q:ℕ) (eps B:ℝ)
    (scale:1 ≤ P₀) (he:0 ≤ eps) (hb:0 ≤ B) (reserve:1 ≤ P₀*eps)
    (low:∀ a, ((F₀).grades a).2 ≤ Q →
      ‖faculty (Pi.single a 1) z-born a‖*(P₀)^Q ≤ B*(P₀)^((F₀).grades a).2*eps)
    (high:∀ a,Q<((F₀).grades a).2 → ‖faculty (Pi.single a 1) z-born a‖ ≤ B) :
    ‖ear y (A.wheel.atCut (N,p) d z)-∑ a,filed R A d N p y a*born a‖*(P₀)^Q ≤
      normAt (F₀) (M₀)⁻¹ (A.R N p d y)*B*eps := by
  rw [heard R A d check top j o z y,← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  have exactCash:=WilsonPhysicalStationThermalCoordinates.original R A d (p:=p) top y
  change (∑ a,_) = normAt (F₀) (M₀)⁻¹ (A.R N p d y) at exactCash
  rw [← exactCash]
  exact WilsonPhysicalStationWickFees.price (fun a=>((F₀).grades a).2) _ _ Q (P₀) eps B
    scale he hb reserve low high

end YM.Integration.WilsonPhysicalStationDirectedRead
end
