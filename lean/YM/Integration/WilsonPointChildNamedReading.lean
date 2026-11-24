import YM.Integration.WilsonPointChildFoldedField
import YM.Integration.WilsonPointChildDigitReturn
import YM.Integration.WilsonPointChildDigitLedger
import YM.Integration.WilsonPointChildHalfCell
import YM.Integration.WilsonPointChildNamedBasis
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildNamedReading
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

open WilsonPointChildNamedBasis
variable (R:Run G)(u:G.ColorIndex)(k:ℕ)(h:ι → ℕ)(s:ι)(depth:k<h s)(o:Loc G 1)

include o in
theorem original (simple:G.Simple)(price:ℕ → Gear G → ℝ)(paid:FundedMarkedCoverRows.prices price R.kit)
    (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (N j:ℕ)(live:j≤N)(up:k≤R.family.path.levels.clock.J j)
    (v:Letter (R.family.labels.level k))(e r:ℕ)(x:chain (edgeL G) r)(V:Case h):
    let Y:=WilsonNeutralPointCourse.filed R (routes R) u depth (fun _=>0) N j v
    touch V {s} ((issue R u k h s depth N j v).2 e r x)=Y (extend (h s) zeroC (V s)) e r x:=by
  intro Y
  let F:=R.family.path.levels
  have enough:∀a:ℕ,j ≤ a → a<N → k≤F.clock.J (a+1):=fun a hj _=>up.trans (F.fits.mono (by omega))
  let Z(t:Spring (h s)):=WilsonPointChildPairedHistory.ledger R u depth N (N-j) j v (basisScroll _ t)
  have same(t:Spring (h s)):(Z t).2=Y (cone (h s) t.val):=by
    have first:=(WilsonPointChildPairedHistory.original R u depth tags simple o price paid N (N-j) j (by omega) v (basisScroll _ t)).2
    have out:=WilsonPointChildCoverReturn.original R u depth simple o N (N-j) j (by omega) enough v (basisScroll _ t)
    exact first.trans (out.trans (congrArg Y (basis_field _ _)))
  have court:=WilsonNeutralPointCourse.original R (routes R) u depth (fun _=>0) N j simple o live
    (up.trans (F.fits.mono (Nat.le_succ _)))
  let read:=WilsonPointChildCoveredTariff.linear Y (court.officers v).toIsLinearMap e r x
  change touch V {s} ((∑t:Spring (h s),tuftV (atom h s t) (Z t)).2 e r x)=read (extend (h s) zeroC (V s))
  rw [Prod.snd_sum]
  simp only [Finset.sum_apply,map_sum]
  change ∑t:Spring (h s),touch V {s} (atom h s t ((Z t).2 e r x))=read (extend (h s) zeroC (V s))
  rw [show extend (h s) zeroC (V s)=∑t:Spring (h s),claim (h s) (finger (paper_fits t)) zeroC (V s) • cone (h s) t.val from by simp only [WilsonPointChildTestJet.extend,_root_.sum_apply,ContinuousLinearMap.smulRight_apply]]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [tested,same, map_smul,smul_eq_mul,mul_comm]
  rfl

end YM.Integration.WilsonPointChildNamedReading
