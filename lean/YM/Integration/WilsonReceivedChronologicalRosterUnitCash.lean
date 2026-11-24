import YM.Integration.WilsonReceivedChronologicalRosterMixed
import YM.Integration.WilsonReceivedChronologicalFixedRoseFittedBank

/-! The original full fitted panel pays the scalar factors in the signed positive-grade reduction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterUnitCash
open Function Finset Lattice RG Wilson Source Labels
open MergeProof MergeProof.Accent MergeProof.East MergeProof.Replicums
open PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Bank
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Soil WilsonCoeffUV.Embroider
open WilsonThermometerDeclaredSeeds WilsonReceivedFixedDigitCanonical WilsonReceivedFixedDigitHistory
open WilsonIndependentCollarOrbitalBasisPayment WilsonIndependentCollarPaidWindingPanel
open WilsonOriginalCensusUnitVerse (observed)
open WilsonOriginalCensusUnitLamp (fee)
open WilsonOriginalCensusPositiveSites (Group names part)
open WilsonOriginalCensusPositiveDose (reduced)
open WilsonOriginalCensusUnitDose (enrolled)
open WilsonOriginalCensusFundedUnits (ordinary receipt)
open WilsonReceivedCanonicalVersePortfolio (weight)
open scoped BigOperators Classical

open WilsonOlderFreshSoftSocketTotal (normalized)
open WilsonOlderFreshHybridClock (flat)
open WilsonCoeffUV.Mer WilsonCoeffUV.Bank
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner


open WilsonOlderFreshSoftSocketHeard
open WilsonOlderFreshSoftSocketRestored

open WilsonReceivedCanonicalSocketSeed (contact present)
open WilsonCoeffUV.Wheel.Mark (mass)
open WilsonOriginalCensusPositiveSites (mapped)
open WilsonOriginalCensusUnitLamp (fee)

open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonReceivedCanonicalVersePortfolio (Selection weight wallet)
open Pert.Asymptotics RG LocalComparison
open WilsonReceivedChronologicalRosterOccupiedTurn (product)

variable {G:Gauge} (R:Run G) {n:ℕ} (k:Fin n → ℕ)
  {N per f K requested power t:ℕ} {B:ℝ} {fk:f ≤ K} {kn:K ≤ N}
  (A:Panel R k N per f K fk kn requested power t B) (file:Filed R k K)
  (station:A.slot=file.station) (axes:A.axis=file.A N per)

include station axes in
theorem original (s:(Stock.census (Fin n)).Mode):
    let x:=votes R k (N:=N) (per:=per) file A.names A.turn
    ‖∏j∈s.val,x j 0‖ ≤ wallet R k (fun _=>B) s.val*R.family.path.levels.clock.hatBeta K^(power*s.val.card):=by
  classical
  intro x
  let unit:Selection R k s.val:=fun _=>.inl ()
  have omitted:weight R k N per K x s.val unit=∏j∈s.val,x j 0:=by
    change (∏j:s.val,x j.val 0)=∏j∈s.val,x j 0
    exact Finset.prod_coe_sort s.val (fun j=>x j 0)
  rw [←omitted]
  exact (Finset.single_le_sum (f:=fun a:Selection R k s.val=>‖weight R k N per K x s.val a‖)
    (fun a _=>norm_nonneg _) (Finset.mem_univ unit)).trans
    (WilsonReceivedChronologicalFixedRoseFittedBank.original R k A file station axes s)

include station axes in
theorem paid (lens:Fin n → ℕ)(pt:Fin n → Chamber)(c v:ℕ)(digits:Digits R.family.path.levels (Fin n))
    (o:Fin n → Cover)(simple:G.Simple)(ck:c ≤ K)(q:ℕ)(θ:ℝ)(ξ:Fin n → Site (R.family.side K per))
    {l:ℕ}(lk:l ≤ K)(W:Config G (R.family.side l per))(s:(Stock.census (Fin n)).Mode):
    let x:=votes R k (N:=N) (per:=per) file A.names A.turn
    let e:=names k
    let dropped:=s.val.filter (fun j=>k j=0)
    ‖actualTransport R.family (N:=N) (product R k (N:=N) x ξ s) lk W-
      normalized R k (fun j=>contact (lens j)) pt N per K c v digits s.val x o (touch (present lens) s.val) q θ‖ ≤
      (wallet R k (fun _=>B) dropped*R.family.path.levels.clock.hatBeta K^(power*dropped.card))*
        ‖actualTransport R.family (N:=N) (product R (k ∘ e) (N:=N) (fun j=>x (e j)) (ξ ∘ e) (part k s)) lk W-
          normalized R (k ∘ e) (D:=lens ∘ e) (fun j=>contact (lens (e j))) (pt ∘ e) N per K c v
            (fun a=>digits a ∘ e) (part k s).val (fun j=>x (e j)) (o ∘ e)
            (touch (present (lens ∘ e)) (part k s).val) q θ‖:=by
  intro x e dropped
  rw [WilsonReceivedChronologicalRosterMixed.original R k lens pt N per K c v digits s x o simple ck kn q θ ξ lk W,norm_mul]
  exact mul_le_mul_of_nonneg_right (original R k A file station axes ⟨dropped,mem_univ _⟩) (norm_nonneg _)

end YM.Integration.WilsonReceivedChronologicalRosterUnitCash
