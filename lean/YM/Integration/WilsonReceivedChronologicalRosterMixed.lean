import YM.Integration.WilsonReceivedChronologicalRosterUnits

/-! The exact signed physical error of a roster in terms of its genuinely positive subroster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterMixed
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

variable {G:Gauge}{n:ℕ}(R:Run G)(k lens:Fin n → ℕ)(pt:Fin n → Chamber)(N per K c v:ℕ)
  (digits:Digits R.family.path.levels (Fin n))(s:(Replicum.Bud (Fin n)).Mode)
  (x:(j:Fin n) → R.family.label (k j))(o:Fin n → Cover)

open Pert.Asymptotics RG LocalComparison
open WilsonReceivedChronologicalRosterOccupiedTurn (product)

theorem original (simple:G.Simple)(ck:c ≤ K)(kn:K ≤ N)(q:ℕ)(θ:ℝ)
    (ξ:Fin n → Site (R.family.side K per)){l:ℕ}(lk:l ≤ K)(W:Config G (R.family.side l per)):
    let e:=names k
    let t:=(part k s).val
    actualTransport R.family (N:=N) (product R k (N:=N) x ξ s) lk W-
      normalized R k (fun j=>contact (lens j)) pt N per K c v digits s.val x o (touch (present lens) s.val) q θ=
    (∏j∈s.val.filter (fun j=>k j=0),x j 0)*(actualTransport R.family (N:=N) (product R (k ∘ e) (N:=N) (fun j=>x (e j)) (ξ ∘ e) (part k s)) lk W-
      normalized R (k ∘ e) (D:=lens ∘ e)
        (fun j=>contact (lens (e j))) (pt ∘ e) N per K c v (fun a=>digits a ∘ e) t
        (fun j=>x (e j)) (o ∘ e) (touch (present (lens ∘ e)) t) q θ):=by
  classical
  intro e t
  have same:(fun U=>∏j∈s.val.filter (fun j=>¬k j=0),
        WilsonPositionProgramBlockedTrialAddBack.uncut R (k j) N per K (ξ j) (x j) U)=
      product R (k ∘ e) (N:=N) (fun j=>x (e j)) (ξ ∘ e) (part k s):=by
    funext U
    rw [←mapped k s,product]
    simp only [Finset.prod_map,Function.comp_apply,e]
    exact (Finset.prod_coe_sort (part k s).val (fun j=>
      WilsonPositionProgramBlockedTrialAddBack.uncut R (k (e j)) N per K (ξ (e j)) (x (e j)) U)).symm
  rw [WilsonReceivedChronologicalRosterZero.original R k (fun j=>contact (lens j)) pt kn x ξ s simple lk W,
    same,WilsonReceivedChronologicalRosterUnits.original R k lens pt N per K c v digits s x o simple ck kn q θ,mul_sub]

end YM.Integration.WilsonReceivedChronologicalRosterMixed
