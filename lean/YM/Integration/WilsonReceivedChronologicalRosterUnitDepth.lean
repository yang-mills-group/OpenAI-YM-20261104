import YM.Integration.WilsonReceivedChronologicalRosterUnitCash
import YM.Integration.WilsonReceivedChronologicalFixedRoseCashPower

/-! Restore the original zero-grade doses at the prescribed power of the moving coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterUnitDepth
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

open Filter

variable {G:Gauge}(R:Run G){n:ℕ}(k:Fin n → ℕ)
local notation "H" => R.family.path.levels.clock.hatBeta

theorem original (simple:G.Simple)(travel power p target:ℕ)(enough:target+1+2*power*n ≤ p)
    {B:ℝ}(bp:0 ≤ B):∀ᶠv:ℕ in atTop,∀{N per f K requested time:ℕ}{fk:f ≤ K}{kn:K ≤ N},
    0 < v → R.family.S.scale K-R.family.S.scale (v-1) ≤ (travel:ℝ)*(1+Real.log (H v)) → 
    ∀(A:Panel R k N per f K fk kn requested power time B)(file:Filed R k K),
    A.slot=file.station → A.axis=file.A N per → 
    ∀(lens:Fin n → ℕ)(pt:Fin n → Chamber){c:ℕ},v ≤ c → c ≤ K → ∀(digits:Digits R.family.path.levels (Fin n))
      (o:Fin n → Cover)(q:ℕ)(θ:ℝ)(ξ:Fin n → Site (R.family.side K per)){l:ℕ}(lk:l ≤ K)
      (W:Config G (R.family.side l per))(s:(Stock.census (Fin n)).Mode),
      let x:=votes R k (N:=N) (per:=per) file A.names A.turn
      let e:=names k
      let live:=actualTransport R.family (N:=N) (product R (k∘e) (N:=N) (fun j=>x (e j)) (ξ∘e) (part k s)) lk W-
        normalized R (k∘e) (D:=lens∘e) (fun j=>contact (lens (e j))) (pt∘e) N per K c v
          (fun a=>digits a∘e) (part k s).val (fun j=>x (e j)) (o∘e) (touch (present (lens∘e)) (part k s).val) q θ
      ‖live‖ ≤ (regulatorRun R.family N per v)^p → 
      ‖actualTransport R.family (N:=N) (product R k (N:=N) x ξ s) lk W-
        normalized R k (fun j=>contact (lens j)) pt N per K c v digits s.val x o (touch (present lens) s.val) q θ‖ ≤ 
          (regulatorRun R.family N per v)^target:=by
  classical
  have wage(s:(Stock.census (Fin n)).Mode):=WilsonReceivedChronologicalFixedRoseCashPower.dated R simple k
    (s.val.filter fun j=>k j=0) travel power p target enough B 1 bp
  filter_upwards [eventually_all.mpr wage] with v bought
  intro N per f K requested time fk kn vp span A file station axes lens pt c vc ck digits o q θ ξ l lk W s x e live paid
  let zero:=s.val.filter fun j=>k j=0
  have cash:=WilsonReceivedChronologicalRosterUnitCash.original R k A file station axes ⟨zero,Finset.mem_univ _⟩
  have restored:=bought s (per:=per) vp le_rfl (vc.trans (ck.trans kn)) kn span
  calc _ ≤ (wallet R k (fun _=>B) zero*(H K)^(power*zero.card))*‖live‖:=
      WilsonReceivedChronologicalRosterUnitCash.paid R k A file station axes lens pt c v digits o simple ck q θ ξ lk W s
    _ ≤ _*(regulatorRun R.family N per v)^p:=
      mul_le_mul_of_nonneg_left paid ((norm_nonneg _).trans cash)
    _ ≤ _:=by simpa only [zero,one_mul,WilsonReceivedChronologicalFixedRoseFittedBank.factor] using restored

end YM.Integration.WilsonReceivedChronologicalRosterUnitDepth
