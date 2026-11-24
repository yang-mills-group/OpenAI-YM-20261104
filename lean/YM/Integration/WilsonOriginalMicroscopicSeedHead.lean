import YM.Integration.WilsonPointChildCenteredTensor
import YM.Integration.WilsonPointChildCenteredSeat
import YM.Integration.WilsonPointChildFoldedField

/-! The complete placed microscopic letter has no finite-period discrepancy at its birth. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicSeedHead
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

open WilsonPointChildNamedBasis WilsonPointChildCenteredBasis

open WilsonCoeffUV.Bank.Carp WilsonPointChildCoverStep WilsonPointChildTestCoordinates
open WilsonPointChildDigitLedger WilsonPointChildCenteredFunctional

theorem original (R:Run G)(simple:G.Simple)(o:Loc G 1)(u:G.ColorIndex)(k:ℕ)(h:ι → ℕ)(s:ι)
    (depth:k<h s)(digit:∀i,Site (R.family.S.block i))(N:ℕ)
    (v:Letter (R.family.labels.level k))(z:Cover)(n:Side)(e r:ℕ)(x:Fin r→Bloch.Co n (Hooks G)):
    let X:=seat R u k h s depth digit N N v z
    X.1 n e r x=plume (X.2 e r) n x:=by
  classical
  intro X
  let word(t:Spring (h s)):=slide (h s) (nodes R digit N N) t
  let upper(t:Spring (h s)):=ledger R u depth digit N 0 N v (word t)
  let Z(t:Spring (h s)):=shifted (upper t) z
  let L(t:Spring (h s)):=mark h s t (samples R digit N N)
  have admitted(t:Spring (h s)):Auth k (Z t):=
    (honest R u depth digit simple o N 0 N (by omega) v (word t)).shifted z
  have lookup(t:Spring (h s)):(Z t).1 n e r x=plume ((Z t).2 e r) n x:=by
    have top:=Roof.topC o (R.family.labels.level k) (R.family.localSection k) R.family.params
      (R.makes.sections k) (Next.Foundations.valuation G k) depth
    have head:=WilsonPointChildFoldedField.print (clef_through (top.officers v) (slotsFits _ v)) (physical (word t)) n e r
    change revolve (wrap n z) ((upper t).1 n e r) x=plume (revolve z ((upper t).2 e r)) n x
    rw [plume_shift]
    change (upper t).1 n e r _=plume ((upper t).2 e r) n _
    exact congrFun head _
  have paid:=WilsonPointChildCenteredTensor.finite Z L admitted n e r x
  have cost:(∑t,‖L t‖*|(Z t).1 n e r x-plume ((Z t).2 e r) n x|)=0:=by
    exact Finset.sum_eq_zero (fun t _=>by rw [lookup,sub_self,abs_zero,mul_zero])
  have eq: (∑t,tuftV (L t) (Z t)).1 n e r x=plume ((∑t,tuftV (L t) (Z t)).2 e r) n x:=
    sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (paid.trans_eq cost) (norm_nonneg _)))
  simpa only [X,WilsonPointChildCenteredFunctional.seat,Nat.sub_self,word,upper,Z,L] using eq

end YM.Integration.WilsonOriginalMicroscopicSeedHead
end
