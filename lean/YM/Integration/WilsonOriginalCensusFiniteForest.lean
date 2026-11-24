import YM.Integration.WilsonNeutralTwoPrintPathCalendar
import YM.Integration.WilsonOriginalFoldedMarkedRightColumn
import YM.Integration.WilsonMarkedIndependentFoldedIntegral

/-! The complete finite mist on the original repeated forest at the actual physical period. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusFiniteForest
open Function Finset Lattice Laurent Wilson RG RG.Supply Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open WilsonCoeffUV.Winding WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open FormalBulk08 Flat Reef Orb Series Jets Shore Lava Wine Gorge Lotus Mesa
open Next.Free AnalyticNext.QuarticMatch.Sheets Stationary
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open scoped BigOperators Matrix Classical
variable {G:Gauge}
open WilsonNeutralTwoPrintPathCalendar (spent)
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonReceivedCompactVerseEntrance (submit)
open WilsonCoeffUV.Wheel Mark WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Carp
variable {I:Type}[Fintype I][DecidableEq I]{h:I → ℕ}

omit [Fintype I] in
private theorem transport {n f:Side}(S:StepData n f)(P:Patch)(K:KernelChoices)
    (hp:S.patch=P)(hk:S.kernel=K)(u:PoleRows S.patch)(v:PoleRows P)(row:HEq u v)
    (H:FreeResolvent.FaceRow)(O:ChartRatio G)(U:Crude G)(M:family G h)
    (C:Cost)(k:I → ℕ)(J:Finset I):
    mist S (repeatF S) H (installed S.ratio u) O (U f) M C k J=
      mist (stepAt P K n) (xree P K n) H (installed (stepAt P K n).ratio v) O
        (U (n*P.L)) M C k J:=by
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

variable (R:Run G)(N i per:ℕ)(k:I→ℕ)
local notation "V" => R.family.path.levels
local notation "S" => WilsonVacuumPreResetStationaryChange.step R i per
local notation "P" => loose (V) i

omit [Fintype I] in
theorem original (M:family G h)(C:Cost)(J:Finset I):
    mist (S) (repeatF (S)) (upper R N i) (prediction R N i per) R.metals.O
      (covered R N i per) M C k J =
    mist (stepAt (P) (V).clock.kernel (coarse R i per)) (xree (P) (V).clock.kernel (coarse R i per))
      (freeForms (V) N (i+1)) (roam (V) N i (coarse R i per)) R.metals.O
      (emera (actionW (V) R.metals.O N (i+1)) (coarse R i per*(P).L)) M C k J:=by
  have co:=transport (G:=G) (I:=I) (h:=h) (n:=coarse R i per) (f:=fine R i per) (S) (P) (V).clock.kernel rfl rfl (predictionA (V) N i) (predictionA (V) N i)
    HEq.rfl (freeForms (V) N (i+1)) R.metals.O (emera (actionW (V) R.metals.O N (i+1))) M C k J
  exact co

omit [Fintype I] in
theorem filed (old:Outerm G h)(e:ℕ)(y:I → Lattice.Cover)(b:I→Site (P).L)(J:Finset I):
    mist (S) (repeatF (S)) (upper R N i) (prediction R N i per) R.metals.O (covered R N i per)
      (submit old k e (chartIn (P) y b)) (ratioHigh (V) R.metals.O N i) k J =
      spent R k N i e (coarse R i per) old y b J:=by
  exact original R N i per k (submit old k e (chartIn (P) y b)) (ratioHigh (V) R.metals.O N i) J

end YM.Integration.WilsonOriginalCensusFiniteForest
end
