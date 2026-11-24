import YM.Integration.WilsonIndependentMatchedOpeningFee
/-! One actual native canonical composite and a single external thermal coefficient per assignment. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedOpeningComposite
open Function Filter Finset PowerSeries Lattice RG Wilson Tree Source Labels
open Laurent Bloch Metric FreeResolvent Work.F08 Precision Exterior Gauge XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.Bank
open WilsonCoeffUV.Wheel.Flooring PertExtension RegulatorIR RegulatorIR.Budget
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentMatchedSectionIncome (leaf)
open WilsonIndependentMatchedOrdinarySeat (here received)
open WilsonIndependentSpoutOrdinaryPlate (sample)
open scoped Classical BigOperators
open WilsonIndependentMatchedTopReceipt (realDose)
open WilsonIndependentMatchedOpeningColumn (column)
open WilsonIndependentMatchedOpeningRoster (seat)
open WilsonIndependentMatchedOpeningPayment (affiled)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentMatchedOpeningFiled (terms planted)
open WilsonCoeffUV.StableStrip
open WilsonIndependentMatchedCensusReceipt (Filed)
open WilsonIndependentMatchedFittedSeat (receiving)
open WilsonIndependentMatchedOpeningPorts (Port submitted)
open WilsonIndependentMatchedOpeningColumn (column)
open WilsonIndependentMatchedOpeningRoster (field seat)
open WilsonIndependentMatchedOpeningPayment (affiled)
open RegulatorIR.Cluster
open WilsonIndependentMatchedOpeningCensus (entry pace Sites)
open WilsonIndependentRawRosterWord (degree)
variable {G:Gauge}{I:Type}
def branch :(n:ℕ)→(Fin (n+1)→I)→ Composite I
  | 0,sel=>.atom (sel 0)
  | slots+1,sel=>.pair (.atom (sel 0)) (branch slots (Fin.tail sel))

theorem canonical (R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
    (s:I→Bool)(d:I→ℕ)(key:∀i,(R.family.labels.level (d i)).Index)
    {D:I→ℕ}(cut:∀i,d i<D i)(o:I→ Cover){n:ℕ}(sel:Fin (n+1)→I):
    MassP G ℝ n (fun t=>column R W (s (sel t)) (cut (sel t))
       (seat (R.family.labels.level (d (sel t))) (key (sel t))) (o (sel t)))=
    field R W s d key cut o (branch n sel):=by
  induction n with
  | zero=>rfl
  | succ n ih=>exact congrArg (agateV _) (ih (Fin.tail sel))

theorem ranks {d:I→ℕ}(n:ℕ)(sel:Fin (n+1)→I):
    (branch n sel).accounts d=∑i,d (sel i):=by
  induction n with
  | zero=>simp [branch,Composite.accounts]
  | succ n ih=>rw [Fin.sum_univ_succ];exact congrArg (_ + ·) (ih (Fin.tail sel))

theorem money (q:ℝ)(b:Blue.Cost)(P:Era G ℝ):q • affiled b P=affiled (PowerSeries.C q * b) P:=by
  apply Prod.ext
  · funext n
    change q • affix b (P.1 n)=affix (PowerSeries.C q * b) (P.1 n)
    rw [←purePayment,affix_mul]
  · change q • affix b P.2=affix (PowerSeries.C q * b) P.2
    rw [←purePayment,affix_mul]

variable {H:Hol G}{n h D k u e:ℕ}{p:h<D}{native:Labels.Frame G h}
  {T:SectionData native}{v:Rails h k u e}{E A K U:Credit}
variable (R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
    (s:Fin (n+1)→Bool)(d:Fin (n+1)→ℕ)(cut:∀i,d i<D)
    (c:(i:Fin (n+1))→Verse (R.family.labels.level (d i)))(φ:Fin (n+1)→Rarity D)
    (y:ℝ)(o:Fin (n+1)→ CellR)(a:Fin (n+1)→ℝ)
    (X:Fin (n+1)→ CutsP H T p v E A K U)
    (z:(i:Fin (n+1))→Sites R d φ y o X i)

def keys (i:Fin (n+1)): (R.family.labels.level (d i)).Index:=sheet _ (z i).2
def points (i:Fin (n+1)):Cover:=(z i).1.val
def weight (i:Fin (n+1)):Blue.Cost:=PowerSeries.C (drumB h (pace X i)) *
    realDose R (w:=cut i) (wheelC (pace X i) y (z i).1.val (φ i).ψ (o i)) (a i • c i) (z i).2

theorem original:
    MassP G ℝ n (fun i=>entry R W s d cut c φ y o a X i (z i))=
      affiled (∏i,weight R d cut c φ y o a X z i)
      (field R W s d (keys R d φ y o X z) (D:=fun _=>D) cut (points R d φ y o X z)
        (branch n id)):=by
  let Z (i:Fin (n+1)):=column R W (s i) (cut i)
    (seat (R.family.labels.level (d i)) (keys R d φ y o X z i)) (points R d φ y o X z i)
  let f:=weight R d cut c φ y o a X z
  have split (i:Fin (n+1)):entry R W s d cut c φ y o a X i (z i) =affiled (f i) (Z i):=money .. 
  have bought (i:Fin (n+1)):Auth (degree R d (keys R d φ y o X z) i) (Z i):=
    WilsonIndependentMatchedOpeningRoster.enrolled R W s d _ (D:=fun _=>D) cut _ (.atom i)
  rw [funext split,WilsonIndependentMatchedOpeningFee.risk Z _ bought f]
  exact congrArg _ (canonical R W s d _ (D:=fun _=>D) cut _ (id:Fin (n+1)→Fin (n+1)))
end YM.Integration.WilsonIndependentMatchedOpeningComposite
