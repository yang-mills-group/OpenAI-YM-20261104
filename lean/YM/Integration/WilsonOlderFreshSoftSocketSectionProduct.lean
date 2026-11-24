import YM.Integration.WilsonOlderFreshSoftSocketMeasuredInverse
import YM.Integration.WilsonOlderFreshSoftSocketVerseWord
import YM.Integration.WilsonOlderFreshSoftSocketVerseHearing

/-! Common-source ordinary hearings for the measured heterogeneous product and its entire compensated section. -/
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketSectionProduct
open Function Filter Finset PowerSeries Lattice RG Wilson Tree Source Labels
open Laurent Bloch Metric FreeResolvent Work.F08 Precision Exterior Gauge XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.StableStrip
open PertExtension RegulatorIR RegulatorIR.Budget PhysicalNext.Repeat.Legato RG16 RG16.Literal
open WilsonThermometerUnitFilingCoarse WilsonMovingForkMixedSeed WilsonAddressedFiniteGuardTrial
open WilsonIndependentMatchedOpeningFiled (planted)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonIndependentMatchedFreshGroupFilm (named)
open WilsonIndependentMatchedFreshInverseIncome (age)
open WilsonIndependentMatchedFreshWhole (projected)
open WilsonPositionProgramTrialReverseLens (received)
open WilsonPositionProgramTrialFittedLens (ticket)
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonIndependentMatchedOrdinaryProfile (stems)
open WilsonOlderFreshSoftSocketTotal (listen)
open WilsonOlderFreshSoftRoseScalarLedger (feed)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonPositionProgramReportedField (entire)
open WilsonOriginalPhysicalFruitVerse (written)
open scoped Classical BigOperators Topology
variable {G:Gauge}{n D h H k u e:ℕ}(R:Run G)(W:Initialize G)(d:Fin (n+1)→ℕ)(fit:∀i,d i<D)
local notation "Q" => named R W (fun _=>false) d fit
local notation "F" i:max => R.family.labels.level (d i)
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O

open WilsonOlderFreshSoftSocketVerseWord (filed)
open WilsonOlderFreshSoftSocketVerseProduct (Paid)
open WilsonOlderFreshSoftSocketVerseHearing (Heard debit)
open WilsonIndependentMatchedCoverProfile (word)

def whole (φ:Wilt Q)(m K:ℕ)(y:ℝ)(o:CellR)(c:(i:Fin (n+1))→Verse (F i)):Era G ℝ:=
  MassP G ℝ n (fun i=>filed R W false (fit i) (c i) (φ i) (paceT R.family.path.levels.S m K) y o (d i))

theorem paidSeed (φ:Wilt Q)(b:Herit Q)(m K:ℕ)(y:ℝ)(o:CellR):
    Ashore Q L O φ (normalized L O Q b m K) m K K y o=
      whole R W d fit φ m K y o (fun i=>received L O (Q i) m K K (b i)):=by
  apply congrArg (MassP G ℝ n)
  funext i
  change word (Shrine (Peaks L O (R.family.localSection (d i)) (fit i) K K)
    (received L O (Q i) m K K (b i))) _ _ _ _ _=_
  rw [Peak_initial]
  rfl

theorem original (e:ℕ):∃A:(i:Fin (n+1))→Alma (F i)→ℝ, (∀i a,0≤A i a)∧
    ∀(_patch:Patch)(m K N per ear:ℕ),m≤K→ear≤K→K≤N→
    ∀(book:Filed R d K)(Y:∀i,R.family.label (d i))(turn:Fin (n+1)→Extra.Histories.Motion)
      (phase:Fin (n+1)→ℂ→L[ℝ]ℝ)(b:Herit Q)(φ:Wilt Q)(B:Fin (n+1)→ℝ),
    (∀i,Amplitude (φ i) (B i))→∀(y:ℝ)(o:CellR),
    let measured (i:Fin (n+1)):=written (F i) (entire R (d i) K (N,per) (votes R d (N:=N) (per:=per) book Y turn i)) (phase i)
    let fresh (i:Fin (n+1)):Verse (F i):=received L O (Q i) m K K (b i)
    let difference (i:Fin (n+1)):=measured i-fresh i
    let fee i (c:Verse (F i)):=WilsonIndependentMatchedCoverProfile.charge (φ i) 0 (d i)
      (paceT R.family.path.levels.S m K) y (charge e c (A i)) (B i)
    let originalWord:=whole R W d fit φ m K y o measured
    let freshWord:=Ashore Q L O φ (normalized L O Q b m K) m K K y o
    (freshWord=whole R W d fit φ m K y o fresh) ∧
    ∀(V:Realm G (e+1) Credit.leanC),V.draws=L→V.paid=O→Dormitory V (∑i,d i) 0 Credit.leanC→
    V.anchor≤ear→∀z,PadRank V ear K z→
      Heard V N K ear (∑i,d i) originalWord freshWord z
        (debit e d (fun i=>fee i (difference i)) (fun i=>fee i (fresh i))):=by
  classical
  choose A nonneg post using fun i=>WilsonOlderFreshSoftSocketVerseWord.original R W false (fit i) e
  refine ⟨A,nonneg,?_⟩
  intro patch m K N per ear mk ek kn book Y turn phase b φ B test y o measured fresh difference fee originalWord freshWord
  have complete:freshWord=whole R W d fit φ m K y o fresh:=paidSeed R W d fit φ b m K y o
  refine ⟨complete,?_⟩
  intro V _ _ dorm alive z pad
  let Fld (i:Fin (n+1))(c:Verse (F i)):=filed R W false (fit i) c (φ i) (paceT R.family.path.levels.S m K) y o (d i)
  have purchase (i:Fin (n+1))(c:Verse (F i)):Paid (d i) e (Fld i c) (fee i c):=
    post i patch (φ i) (B i) _ y o (d i) (pace_pos ..) (pace_le _ mk) (test i) c
  have replace (i:Fin (n+1)):Fld i (difference i)+Fld i (fresh i)=Fld i (measured i):=by
    rw [show Fld i (difference i)=Fld i (measured i)-Fld i (fresh i) from
      WilsonOlderFreshSoftSocketVerseWord.linear R W false (fit i) _ _ _ _ y o (d i) (pace_pos ..),sub_add_cancel]
  rw [complete]
  have issued:=WilsonOlderFreshSoftSocketVerseHearing.original d
    (fun i=>Fld i (difference i)) (fun i=>Fld i (fresh i)) _ _ (fun i=>purchase i _) (fun i=>purchase i _)
    V dorm alive ek kn z pad
  simp only [replace] at issued
  simpa only [originalWord,whole,Fld] using issued

end YM.Integration.WilsonOlderFreshSoftSocketSectionProduct
