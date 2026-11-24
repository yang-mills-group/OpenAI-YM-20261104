import YM.Integration.WilsonCapturedPrimaryWindingVersePage
import YM.Integration.FundedMarkedPathSelection

/-! The finite unaliased ordinary reading of an independently enrolled marked
family at a genuine pin. Its old joint row, both proper means, and quiet
normalizer enter the same conditional Wick calculation. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedVerseCensus
open Function Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Mosaic FormalBulk08
open Flat Reef Orb Series Jets Shore Lava Wine Gorge Lotus Mesa
open Next.Free AnalyticNext.QuarticMatch.Sheets Stationary
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open scoped BigOperators Matrix Classical

open WilsonCoeffUV.Soil WilsonCoeffUV.Embroider.Canvas
open WilsonCapturedPrimaryWindingVersePage
open FundedMarkedPathSelection
variable {G:Gauge}{I:Type}[DecidableEq I]{D:I→ℕ}
def ordinary (K:family G D)(A:Case D)(J:Finset I):Era G ℝ :=
  tuftV (touch A J) (levelsO K J)

private theorem shared {B:Type*}[CommRing B](d z a c Z A C:B)
    (joint:Z=d*z)(left:A=d*a)(right:C=d*c):
    d^2*(z-a*c)=d*Z-A*C:=by rw [joint,left,right];ring

variable (R:Run G){N i:ℕ}(per:ℕ)
local notation "V" => R.family.path.levels
local notation "S" => step R i per
local notation "F" => repeatF S
local notation "n" => coarse R i per
local notation "f" => fine R i per
local notation "vac" => (story V R.metals.O N (i+1)).1
variable {e:ℕ}{Q:Realm G (e+1) Credit.leanC}{hm:Q.anchor ≤ i}
variable {k:I→ℕ}{T:Finset I}{price:ℝ}
variable (X:Input Q hm T k D price)(y:I → Cover)(A:Case D)
local notation "income" J:max => ordinary (X.familyAt y) A J
local notation "amount" J:max => mass k J
local notation "value" J:max => page R N i per (amount J) (income J)
local notation "printer" J:max => flash (value J)
variable (simple:G.Simple)(live:i<N)(tag:(step R i per).Choices)
local notation "wick_" => Wick (Woods G n) ((model R N i per live).covariance F tag)
local notation "quiet" => raiseE (shot S F (prediction R N i per) (ratio R) (vac f))
local notation "joint_" J:max => wick_ (quiet*loom (slice R N i per F) (flash ((income J).1 f)))

include simple live tag in
theorem original :
    (∀J:Finset I,(verseI V R.metals.O i N (amount J) (income J)).1 n =
      Blue.mix (ratioHigh V R.metals.O N i) (value J) ∧
      joint_ J = wick_ quiet * printer J) ∧
    ∀J L U:Finset I,(wick_ quiet)^2*(printer J-printer L*printer U)=
      wick_ quiet*joint_ J-joint_ L*joint_ U:=by
  have law (J:Finset I):Auth (amount J) (income J):=
    (placedO (X.familyAt y) (X.degree y) J).tuft (touch A J)
  have norm (J:Finset I):joint_ J=wick_ quiet*printer J:=
    WilsonCapturedPrimaryWindingVersePage.normalized R N i per simple live tag (amount J) (income J) (law J)
  exact ⟨fun J=>⟨WilsonCapturedPrimaryWindingVersePage.issued R N i per (amount J) (income J),norm J⟩,
    fun J L U=>shared _ _ _ _ _ _ _ (norm J) (norm L) (norm U)⟩

theorem filed (enrolled:Q.draws=V)(ratio:Q.paid=R.metals.O)(J:Finset I) (simple:G.Simple)(live:i<N):
    ordinary (fun M=>FundedMarkedPathSelection.output X M N y) A J =
      verseI V R.metals.O i N (amount J) (income J):=by
  change tuftV (touch A J) (levelsO (logO Q.draws Q.paid i N (X.familyAt y) k) J)=_
  rw [enrolled,ratio,step_S V R.metals.O i N (X.familyAt y) k live simple R.alloy.B.ratio (X.degree y)]
  exact Mer.ply_verse V live simple R.alloy.B.ratio (placedO (X.familyAt y) (X.degree y) J) (touch A J)

end YM.Integration.WilsonReceivedDepositedVerseCensus
