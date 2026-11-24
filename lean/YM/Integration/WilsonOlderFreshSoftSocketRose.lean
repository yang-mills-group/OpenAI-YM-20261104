import YM.Integration.WilsonOlderFreshSoftSocketTotal
import YM.Integration.WilsonOlderFreshSoftRoseNodes

/-! The actual 6,4,4 independently reannounced physical row in the original finite measured frame on each occupied face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketRose
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

def names:Columns R d≃Columns R (fun i:(univ:Finset I)=>d i) where
  toFun b i:=b i
  invFun b i:=b ⟨i,mem_univ _⟩
  left_inv _:=rfl
  right_inv b:=by funext i;rfl

theorem first {D:I→ℕ}(κ:(i:I)→Knob (D i))(pt:I→Chamber)(L:Levels G)(O:ChartRatio G)
    (draw:L=R.family.path.levels)(paid:O=R.metals.O)(N per K c v:ℕ)(cells:Digits L I)
    (w:(i:I)→R.family.label (d i))(y:I → Cover)(f:Pen D (univ:Finset I)→L[ℝ]ℝ)(p:ℕ)(θ:ℝ):
    WilsonOlderFreshSoftFigureReading.reading R d (regulatorRun R.family N per K)
      (fun i=>WilsonPositionProgramReportedField.entire R (d i) K (N,per) (w i))
      (fun b=>cruises L O N (mass d univ) c v
        (WilsonOlderFreshSoftTrialCut.source R D d N K c L O κ pt cells y univ f b)) p θ=
    figure R d κ pt N per K c v (cast (congrArg (fun l=>Digits l I) draw) cells) univ w y f p θ:=by
  subst L O
  classical
  unfold WilsonOlderFreshSoftFigureReading.reading figure
  apply Fintype.sum_equiv (names R d)
  intro b
  have id:seats R d univ (names R d b)=b:=by
    funext i
    rw [WilsonOlderFreshSoftSocketMeasuredCash.seats,dif_pos (mem_univ i)]
    rfl
  have price:packet R d univ w N per K (names R d b)=
        WilsonOriginalPublicTrialFigure.weight R d (regulatorRun R.family N per K)
          (fun i=>WilsonPositionProgramReportedField.entire R (d i) K (N,per) (w i)) b:=by
    unfold WilsonOlderFreshSoftSocketMeasuredCash.packet WilsonOriginalPublicTrialFigure.weight
    exact Finset.prod_coe_sort univ (fun i=>WilsonOriginalPublicTrialFigure.amount R d
      (regulatorRun R.family N per K) (fun j=>WilsonPositionProgramReportedField.entire R (d j) K (N,per) (w j)) i (b i))
  rw [id,price]
  rfl

theorem printed {e:ℕ}(D:Fin 3→ℕ)(V:Realm G (e+1) Credit.leanC)(t:Finset (Fin 3))
    (draw:V.draws=R.family.path.levels)(paid:V.paid=R.metals.O)(N per K c w₀ v:ℕ)
    (a:Probe D V t)(w:(i:Fin 3)→R.family.label (grade i))(p:ℕ)(θ:ℝ):
    row (R:=R) D V t N K c w₀ v a (regulatorRun R.family N per K)
      (fun i=>WilsonPositionProgramReportedField.entire R (grade i) K (N,per) (w i)) p θ false=
    figure R (grade ∘ seat t) a.coeff a.phase N per K c v
      (cast (congrArg (fun l=>Digits l t) draw) a.digit) univ (fun i=>w (seat t i)) a.root a.test p θ:=by
  exact first R (grade ∘ seat t) a.coeff a.phase V.draws V.paid draw paid N per K c v a.digit
    (fun i=>w (seat t i)) a.root a.test p θ

theorem original {e:ℕ}(D:Fin 3→ℕ)(V:Realm G (e+1) Credit.leanC)(t:Finset (Fin 3))
    (draw:V.draws=R.family.path.levels)(paid:V.paid=R.metals.O)(N per K c w₀ v:ℕ)
    (a:Probe D V t)(w:(i:Fin 3)→R.family.label (grade i))
    (simple:G.Simple)(ratio:LocalRatio O_)(vc:v≤c)(ck:c≤K)(live:K≤N)(p:ℕ)
    (kept:∀q:Selection R (grade ∘ seat t) univ,
      WilsonOlderFreshSoftSocketRestored.degree R (grade ∘ seat t) univ
        (WilsonOlderFreshSoftSocketFaces.fill R (grade ∘ seat t) univ q)≤p)
    {θ:ℝ}(θ0:0≤θ)(θ1:θ≤1):
    let d:=grade ∘ seat t
    let cells:=cast (congrArg (fun l=>Digits l t) draw) a.digit
    let w':=(fun i:t=>w (seat t i))
    let Z:=normalized R d a.coeff a.phase N per K c v cells univ w' a.root a.test p θ
    ‖row (R:=R) D V t N K c w₀ v a (regulatorRun R.family N per K)
      (fun i=>WilsonPositionProgramReportedField.entire R (grade i) K (N,per) (w i)) p θ false-Z‖≤
      ∑q:Selection R d univ,‖WilsonReceivedCanonicalVersePortfolio.weight R d N per K w' univ q‖*
        cost R d a.coeff a.phase N per K c v cells univ a.root a.test p θ q:=by
  dsimp only
  rw [printed R D V t draw paid N per K c w₀ v a w p θ]
  exact WilsonOlderFreshSoftSocketTotal.original R _ a.coeff a.phase N per K c v _ univ _ a.root a.test
    simple ratio vc ck live p kept θ0 θ1

end YM.Integration.WilsonOlderFreshSoftSocketRose
end
