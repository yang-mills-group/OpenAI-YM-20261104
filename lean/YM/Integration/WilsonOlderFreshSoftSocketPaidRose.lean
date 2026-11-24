import YM.Integration.WilsonOlderFreshSoftSocketFare

/-! The independent stop on the registered faces of the three physical fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketPaidRose
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Bank.Mosaic.Near
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOlderFreshSoftSocketTotal (figure normalized cost)
open WilsonOlderFreshSoftSocketMeasuredCash (packet seats)
open WilsonOlderFreshSoftFigureReading (reading)
open WilsonOlderFreshSoftRoseCourse (grade seat)
open WilsonOlderFreshSoftRoseMarket (Probe row)
open WilsonReceivedCanonicalVersePortfolio (Selection)
open WilsonReceivedFixedDigitHistory ActualRunPhysicalPages Pert.Asymptotics
variable {G:Gauge}{I:Type}[Fintype I][LinearOrder I](R:Run G)(d:I→ℕ)
local notation "L_" => R.family.path.levels
local notation "O_" => R.metals.O

open WilsonOlderFreshSoftSocketCensus (fee)
open WilsonOlderFreshSoftSocketGross (gross)
open WilsonOlderFreshSoftSocketFare (bracket)
open WilsonCoeffUV.Winding
open WilsonIndependentCollarOrdinaryCruise
open WilsonIndependentCollarOpticalTrial

def basis (w:(i:I)→R.family.label (d i))(N per K:ℕ):ℝ:=
  ∑b:Columns R d,‖WilsonOriginalPublicTrialFigure.weight R d (regulatorRun R.family N per K)
      (fun i=>WilsonPositionProgramReportedField.entire R (d i) K (N,per) (w i)) b‖

theorem salary (w:(i:I)→R.family.label (d i))(N per K:ℕ):
    (∑b:Columns R (fun i:(univ:Finset I)=>d i),‖packet R d univ w N per K b‖)=basis R d w N per K:=by
  symm
  apply Fintype.sum_equiv (WilsonOlderFreshSoftSocketRose.names R d)
  intro b
  congr 1
  exact (Finset.prod_coe_sort univ (fun i=>WilsonOriginalPublicTrialFigure.amount R d
    (regulatorRun R.family N per K) (fun j=>WilsonPositionProgramReportedField.entire R (d j) K (N,per) (w j))
    i (b i))).symm

def Measured (p target:ℕ)(D:Fin 3→ℕ)(V:Realm G (p+1) Credit.leanC)(t:Finset (Fin 3))
    (draw:V.draws=R.family.path.levels)(N per K c w₀ v:ℕ)
    (a:Probe D V t)(w:(i:Fin 3)→R.family.label (grade i))(A B:ℝ):Prop:=
  let d:=grade ∘ seat t
  let cells:=cast (congrArg (fun l=>Digits l t) draw) a.digit
  let w':=(fun i:t=>w (seat t i))
  let θ:=regulatorRun R.family N per v
  let Z:=normalized R d a.coeff a.phase N per K c v cells univ w' a.root a.test p θ
  ‖row (R:=R) D V t N K c w₀ v a (regulatorRun R.family N per K)
    (fun i=>WilsonPositionProgramReportedField.entire R (grade i) K (N,per) (w i)) p θ false-Z‖≤
      (basis R d w' N per K*fee R d univ)*(θ^target*(‖a.test‖*gross R (D ∘ seat t) d p univ A B))

def Sold (p target N per K v:ℕ):Prop:=
  ∀(D:Fin 3→ℕ)(V:Realm G (p+1) Credit.leanC)(t:Finset (Fin 3)),t.Nonempty→
    ∀(draw:V.draws=R.family.path.levels),V.paid=R.metals.O→
    Dormitory V (mass (grade ∘ seat t) univ) 0 Credit.leanC→
    ∀(c w₀:ℕ),V.anchor≤v→v≤c→c≤K→∀(a:Probe D V t)(w:(i:Fin 3)→R.family.label (grade i))
      (A B:ℝ),PadRank V c K A→PadRank V v c B→Measured R p target D V t draw N per K c w₀ v a w A B

theorem original (p target N per K v:ℕ)(live:K≤N)(hv:regulatorRun R.family N per v≤1)
    (hK:regulatorRun R.family N per K≤1)(hrs:7≤p)
    (bought:∀h≤7,bracket R N per K v h p≤regulatorRun R.family N per v^target):Sold R p target N per K v:=by
  intro D V t occ draw paid dorm c w₀ first vc ck a w A B front march
  obtain ⟨i,h⟩:=occ
  have filled:(univ:Finset t).Nonempty:=⟨⟨i,h⟩,mem_univ _⟩
  unfold Measured
  dsimp only
  rw [WilsonOlderFreshSoftSocketRose.printed R D V t draw paid,←salary]
  exact WilsonOlderFreshSoftSocketFare.original R (D ∘ seat t) (grade ∘ seat t) p univ filled V draw paid
    dorm N per K c v first vc ck live hK hv A B front march a.coeff a.phase (fun i=>w (seat t i)) a.digit a.root a.test
    target 7 (fun q=>WilsonOlderFreshSoftSocketCensus.seven R t _) hrs bought

end YM.Integration.WilsonOlderFreshSoftSocketPaidRose
end
