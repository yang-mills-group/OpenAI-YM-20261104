import YM.Integration.WilsonOriginalFoldedMarkedRightColumn
import YM.Integration.WilsonMarkedIndependentFoldedIntegral

/-! The original period's filed right column at the independently booked canonical forest. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFoldedFiledForest
open Function Finset Lattice Laurent Wilson RG RG.Supply Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open WilsonCoeffUV.Winding WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open FormalBulk08 Flat Reef Orb Series Jets Shore Lava Wine Gorge Lotus Mesa
open Next.Free AnalyticNext.QuarticMatch.Sheets Stationary
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open scoped BigOperators Matrix Classical
variable {G:Gauge}
private abbrev stepAt (P:Patch)(K:KernelChoices)(n:Side):StepData n (n*P.L):=⟨P,K,rfl⟩

private theorem transport {n f:Side}(S:StepData n f)(P:Patch)(K:KernelChoices)
    (hp:S.patch=P)(hk:S.kernel=K)(u:PoleRows S.patch)(v:PoleRows P)(row:HEq u v)
    (H:FreeResolvent.FaceRow)(O:ChartRatio G)(U T:Crude G)(q:ℕ):
    reed S (repeatF S) H (installed S.ratio u) O (U f) q (T f)=
      reed (stepAt P K n) (repeatF (stepAt P K n)) H
        (installed (stepAt P K n).ratio v) O (U (n*P.L)) q (T (n*P.L)):=by
  rcases S with ⟨p,k,hs⟩
  change p=P at hp
  change k=K at hk
  subst p
  subst k
  replace hs:f=n*P.L:=Subtype.ext hs
  subst f
  replace row:u=v:=eq_of_heq row
  subst u
  rfl

variable (R:Run G)(N i per:ℕ)
local notation "V" => R.family.path.levels
local notation "wood" => (fun k:ℕ=>Flat.routes (R.family.path.levels.clock.op k 0).patch)
local notation "b" => (fun k:ℕ=>(R.family.path.levels.blocks k 0).branches)
local notation "S" => WilsonVacuumPreResetStationaryChange.step R i per
local notation "F" => repeatF S
local notation "m" => coarse R i per
local notation "f" => fine R i per

theorem original (q:ℕ)(T:Crude G):
    WilsonOriginalFoldedMarkedRightColumn.filed R N i per F q (T f)=
      WilsonMarkedIndependentFoldedIntegral.folded R N i q T m:=by
  exact transport S (loose V i) (V).clock.kernel rfl rfl (predictionA V N i) (predictionA V N i)
    HEq.rfl (freeForms V N (i+1)) R.metals.O (emera (actionW V R.metals.O N (i+1))) T q

theorem normalized (u:G.ColorIndex)
    (tags:∀j n,(primary ((V).clock.op j 0).patch (V).clock.kernel n).Choices)
    (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (live:i<N)(q:ℕ)(T:Era G ℝ)(paid:Auth q T):
    let P:=destination V N i
    let W:=Dove.model V wood b R.metals.O u N (i+1)
    flash (WilsonOriginalFoldedMarkedRightColumn.filed R N i per F q (T.1 f))=
      Reef.tossed P R.metals.O (b i) (wood i) m (tags i m)
        (Mesa.stone W (m*P.L)) (flash (T.1 (m*P.L))):=by
  intro P W
  rw [original R N i per q T.1]
  exact WilsonMarkedIndependentFoldedIntegral.finite R u tags simple v funded live q T paid m

end YM.Integration.WilsonOriginalFoldedFiledForest
