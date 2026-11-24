import YM.Integration.WilsonPointChildNamedReading
import YM.Integration.WilsonPointChildWindingRoot
import YM.Integration.WilsonPointChildPairedHistory
import YM.Integration.WilsonPointChildFoldedField
import YM.Integration.WilsonPointChildDigitReturn
import YM.Integration.WilsonPointChildDigitLedger
import YM.Integration.WilsonPointChildHalfCell
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildNamedSalary
open Function Filter Finset Matrix Lattice Wilson RG Laurent PowerSeries Work.F08
open FormalBulk08 Flat Reef Jets Orb Wick Stationary Series Shore Gorge Lotus Mesa Rift Lava Dawn Kemp Roof Sierra Rial
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Power
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Winding
open YM Next.Foundations PhysicalNext.Repeat.Legato Pose Palm Quire Wine Dove WilsonCoeffUV.Embroider
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{d D:ℕ}
open WilsonCoeffUV.Wheel WilsonCoeffUV.Embroider.Canvas
open WilsonPointChildTestJet WilsonPointChildTestCoordinates WilsonCoeffUV.Wheel.Mark
variable {ι:Type}

open WilsonPointChildNamedBasis WilsonPointChildFiledPress WilsonPointChildCoveredTariff
open WilsonCoeffUV.Shard WilsonCoeffUV.Bank.Mosaic
theorem rooted {α:Type}{r:ℕ}{T:Ten ℝ (Cloth α) r}{s A:ℝ}(positive:0 ≤ s)
    (paid:Wig terrain (fun _:Unit=>0) s A {()} T):Cork terrain 0 s A T:=by
  refine ⟨paid.1,fun x=>(paid.2 x).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr ?_) (neg_nonpos.mpr positive))) paid.1)⟩
  let go:Fin (r+1)  →  ({()} : Finset Unit)⊕Fin r:=Fin.cases (.inl ⟨(),mem_singleton_self _⟩) .inr
  have chosen (j:Fin (r+1)):foyer (fun _:Unit=>0) {()} x (go j)=stud 0 x j:=
    Fin.cases rfl (fun _=>rfl) j
  apply league_le
  intro j k
  rw [←chosen j,←chosen k]
  exact leg_le ..

/-- Each prescribed field keeps its own cover address.  The one physical
torus and all actual top cutoffs enter after the uniform reporting date. -/
def factor (h:ι → ℕ)(s:ι):ℝ:=∑t:Spring (h s),‖atom h s t‖*‖physical (basisScroll _ t)‖

theorem factor_nonneg (h:ι → ℕ)(s:ι):0≤factor h s:=Finset.sum_nonneg fun _ _=>by positivity

def seat (R:Run G)(u:G.ColorIndex)(k:ℕ)(h:ι → ℕ)(s:ι)(depth:k<h s)(N j:ℕ)
    (v:Letter (R.family.labels.level k))(z:Cover):Era G (Pen h {s}):=
  ∑t:Spring (h s),tuftV (atom h s t) (shifted (WilsonPointChildPairedHistory.ledger R u depth N (N-j) j v (basisScroll _ t)) z)

theorem authorized (R:Run G)(simple:G.Simple)(o:Loc G 1)(u:G.ColorIndex)(k:ℕ)(h:ι → ℕ)(s:ι)(depth:k<h s)
    (N j:ℕ)(live:j≤N)(v:Letter (R.family.labels.level k))(z:Cover):Auth k (seat R u k h s depth N j v z):=by
  apply Auth.sum
  intro t _
  exact ((WilsonPointChildPairedHistory.honest R u depth simple o N (N-j) j (by omega) v (basisScroll _ t)).shifted z).tuft _

theorem original (R:Run G)(simple:G.Simple)(booked:WilsonPointChildFiledTest.Filed R)
    (u:G.ColorIndex)(k:ℕ)(h:ι → ℕ)(s:ι)(depth:k<h s)(o:Loc G 1)
    (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (price:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)(E:ℕ){η:ℝ}(pos:0<η):
    ∀ᶠj:ℕ in atTop,∀N,j≤N→∀v:Letter (R.family.labels.level k),∀y:ι → Cover,∀e≤E,∀r,
      Wig terrain y (width R j) ((R.family.path.levels.clock.hatBeta j)^η*factor h s)
        {s} ((seat R u k h s depth N j v (y s)).2 e r):=by
  filter_upwards [WilsonPointChildWindingIncome.original R simple booked u depth o tags price funded E pos] with j full
  intro N live v y e he r
  have positive:0≤width R j:=((Primer.FamilyWindow R.family).pos _).le
  let Q:ℝ:=(R.family.path.levels.clock.hatBeta j)^η
  have each (t:Spring (h s)):let X:=WilsonPointChildPairedHistory.ledger R u depth N (N-j) j v (basisScroll _ t)
      Wig terrain y (width R j) (Q*(‖atom h s t‖*‖physical (basisScroll _ t)‖)) {s}
        ((tuftV (atom h s t) (shifted X (y s))).2 e r):=by
    intro X
    have atZero:=rooted positive ((full N live v (basisScroll _ t)).2 e he r).1
    have paid:Wig terrain y (width R j) (Q*‖physical (basisScroll _ t)‖) {s} ((shifted X (y s)).2 e r):=
      abreast _ y s (Cork.turn _ atZero) positive
    refine ⟨?_,?_⟩
    · rw [←mul_left_comm];exact mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) paid.1
    · intro x
      change ‖atom h s t _‖≤_
      calc _ ≤ ‖atom h s t‖*‖(shifted X (y s)).2 e r x‖:=(atom h s t).le_opNorm _
           _ ≤ ‖atom h s t‖*((Q*‖physical (basisScroll _ t)‖)*_):=mul_le_mul_of_nonneg_left (paid.2 x) (ContinuousLinearMap.opNorm_nonneg _)
           _ = _:=by ring
  dsimp only [seat]
  rw [Prod.snd_sum]
  simp only [Finset.sum_apply]
  simpa only [factor, Finset.mul_sum] using Wig.sum (Z:=univ) (fun t _=>each t)
end YM.Integration.WilsonPointChildNamedSalary
