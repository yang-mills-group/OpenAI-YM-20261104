import YM.Integration.WilsonReceivedChronologicalRosterUnitWallet
import YM.Integration.WilsonOlderFreshSoftSocketTotal

/-! The physical normalized row after removing the actual zero-grade legs, including its shared earlier scalar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterUnitRows
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

variable {G:Gauge}{n:ℕ}(R:Run G)(k:Fin n→ℕ){h:Fin n→ℕ}(κ:(j:Fin n)→Knob (h j))(pt:Fin n→Chamber)
    (N K i:ℕ)(digit:Digits R.family.path.levels (Fin n))(o:Fin n → Cover)(A:Case h)

theorem sum (simple:G.Simple)(called:i≤K)(live:K≤N)(per:ℕ)(x:(j:Fin n)→R.family.label (k j))
    (s:(Replicum.Bud (Fin n)).Mode)(read:Era G ℝ→ℂ):
    let e:=names k
    let t:=(part k s).val
    let dropped:=s.val.filter (fun j=>k j=0)
    (∑a:Choices R k s.val,WilsonReceivedCanonicalVersePortfolio.weight R k N per K x s.val a*read (ordinary R k κ pt N K i digit o A s.val a))=
      (∏j∈dropped,x j 0)*∑b:Choices R (k ∘ e) t,WilsonReceivedCanonicalVersePortfolio.weight R (k ∘ e) N per K (fun j=>x (e j)) t b*
        read ((∏j∈dropped,fee κ pt A j) • ordinary R (k ∘ e) (h:=h ∘ e) (fun j=>κ (e j)) (pt ∘ e)
          N K i (fun d=>digit d ∘ e) (o ∘ e) (fun j=>A (e j)) t b):=by
  intro e t dropped
  let keep:=fun a:Choices R k s.val=>∀j:s.val,k j=0 → a j=.inl ()
  let pay:=fun a:Choices R k s.val=>WilsonReceivedCanonicalVersePortfolio.weight R k N per K x s.val a*read (ordinary R k κ pt N K i digit o A s.val a)
  have trim:∑a,pay a=∑a∈univ.filter keep,pay a:=by
    apply (sum_subset (filter_subset _ _) ?_).symm
    intro a _ no
    have inactive:¬keep a:=fun accepted=>no (mem_filter.mpr ⟨mem_univ _,accepted⟩)
    exact mul_eq_zero_of_left (WilsonReceivedChronologicalRosterUnitWallet.absent R k N per K x simple s.val a inactive) _
  change ∑a,pay a=_
  rw [trim,Finset.mul_sum]
  refine Finset.sum_bij' (fun a _=>reduced R k s a) (fun b _=>WilsonOriginalCensusUnitMenu.fixed R k s b) ?_ ?_ ?_ ?_ ?_
  · exact fun _ _=>mem_univ _
  · exact fun b _=>mem_filter.mpr ⟨mem_univ _,WilsonOriginalCensusUnitMenu.funded R k s b⟩
  · exact fun a ha=>WilsonOriginalCensusUnitMenu.restored R k s a (mem_filter.mp ha).2
  · exact fun b _=>WilsonOriginalCensusUnitMenu.crop R k s b
  · intro a ha
    have done:= (mem_filter.mp ha).2
    change WilsonReceivedCanonicalVersePortfolio.weight R k N per K x s.val a*read (ordinary R k κ pt N K i digit o A s.val a)=_
    rw [WilsonReceivedChronologicalRosterUnitWallet.supported R k N per K x s a done,
      receipt R k κ pt N K i digit o A simple called live s a done,mul_assoc]


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

theorem original (simple:G.Simple)(called:i≤K)(live:K≤N)(per v p:ℕ)(θ:ℝ)(x:(j:Fin n)→R.family.label (k j))
    (s:(Replicum.Bud (Fin n)).Mode):
    let e:=names k
    let t:=(part k s).val
    let dropped:=s.val.filter (fun j=>k j=0)
    let read:=fun E:Era G ℝ=>(flat (cruises R.family.path.levels R.metals.O N
      (WilsonCoeffUV.Wheel.Mark.mass k s.val) i v E) p θ:ℂ)
    normalized R k κ pt N per K i v digit s.val x o (touch A s.val) p θ=
      (∏j∈dropped,x j 0)*∑b:Choices R (k ∘ e) t,WilsonReceivedCanonicalVersePortfolio.weight R (k ∘ e)
        N per K (fun j=>x (e j)) t b*read ((∏j∈dropped,fee κ pt A j) •
        ordinary R (k ∘ e) (h:=h ∘ e) (fun j=>κ (e j)) (pt ∘ e) N K i (fun d=>digit d ∘ e)
          (o ∘ e) (fun j=>A (e j)) t b):=by
  intro e t dropped read
  exact sum R k κ pt N K i digit o A simple called live per x s read

end YM.Integration.WilsonReceivedChronologicalRosterUnitRows
