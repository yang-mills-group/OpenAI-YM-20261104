import YM.Integration.WilsonReceivedChronologicalRosterUnitRows
import YM.Integration.WilsonReceivedChronologicalRosterZero

/-! Grade-zero contractions commute with the original fixed-child and the funded stopped normalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterUnits
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

private theorem contact_fee (j:Fin n):fee (fun i=>contact (lens i)) pt (present lens) j=1:=by
  change claim (lens j) ⟨⟨0,Nat.zero_lt_succ _⟩,Fin.elim0⟩ (pt j) (page _ (WilsonReceivedCanonicalSocketSeed.sheet _))=1
  rw [nib _ (Nat.zero_le _) Fin.elim0]
  simp [crease,WilsonReceivedCanonicalSocketSeed.sheet,iteratedFDeriv_zero_apply]

theorem original (simple:G.Simple)(ck:c ≤ K)(kn:K ≤ N)(q:ℕ)(θ:ℝ):
    let e:=names k
    let t:=(part k s).val
    normalized R k (fun j=>contact (lens j)) pt N per K c v digits s.val x o (touch (present lens) s.val) q θ=
      (∏j∈s.val.filter (fun j=>k j=0),x j 0)*normalized R (k ∘ e) (D:=lens ∘ e)
        (fun j=>contact (lens (e j))) (pt ∘ e) N per K c v (fun a=>digits a ∘ e) t
        (fun j=>x (e j)) (o ∘ e) (touch (present (lens ∘ e)) t) q θ:=by
  intro e t
  have faces:mass k s.val=mass (k ∘ e) t:=by
    have active:mass k (s.val.filter (fun j=>k j≠0))=mass k s.val:=by
      unfold mass
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j js outside
      by_contra actual
      exact outside (mem_filter.mpr ⟨js,actual⟩)
    rw [←active,←mapped]
    simp [mass,e,t]
  have flag:(∏j∈s.val.filter (fun j=>k j=0),fee (fun i=>contact (lens i)) pt (present lens) j)=1:=
    Finset.prod_eq_one (fun j _=>contact_fee lens pt j)
  have paid:=WilsonReceivedChronologicalRosterUnitRows.original R k (fun j=>contact (lens j)) pt N K c digits o (present lens)
    simple ck kn per v q θ x s
  dsimp only at paid
  simp only [flag,one_smul,faces] at paid
  exact paid

end YM.Integration.WilsonReceivedChronologicalRosterUnits
