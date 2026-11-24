import YM.Integration.WilsonOriginalFoldedChartPayload

/-! Normalization of one actual held marked column on the original folded Wilson inlet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFoldedMarkedRightColumn
open Function Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay WilsonVacuumPreResetDepositedGeometric
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonOriginalRelativeFoldedQuiet (relative)
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {G:Gauge}(R:Run G)(N i p:ℕ)(hi:i<N)(F:Forest (step R i p).ratio)(tag:(step R i p).Choices)
local notation "P" => covered R N i p
local notation "K" => model R N i p hi
local notation "C₁" => Woods G (coarse R i p)

local notation "Y" => upper R N i
local notation "P₀" => covered R N i p

private theorem covariance :
    ((model R N i p hi).covariance F tag)=treeInverse G (step R i p) F (upper R N i) 0:=by
  unfold Bulk.Kernel.covariance
  rw [OriginalMarkedHeatCovariance.precision R N i p hi F tag]
  simp [treeInverse,FreeResolvent.resolve]

def before (T:PChart G (fine R i p)):Ink ((Active G F)⊕Woods G (coarse R i p)) :=
  retool (shift R N i p hi F) (loom (slice R N i p F) (flash T))

def filed (q:ℕ)(T:PChart G (fine R i p)) :=
    reed (step R i p) F Y (prediction R N i p) (ratio R) P₀ q T

theorem normalized (simple:G.Simple)(q:ℕ)(T:PChart G (fine R i p))(sp:shellK q T)(pure:∀d,Pure (T d)) :
    let C₀:=(model R N i p hi).covariance F tag
    let φ:=relative R N i p hi F P₀
    Wick (Woods G (coarse R i p)) C₀ (raiseE φ*before R N i p hi F T)=
      Wick (Woods G (coarse R i p)) C₀ (raiseE φ)*flash (filed R N i p F q T):=by
  intro C₀ φ
  let S:=step R i p
  let a:=loom (slice R N i p F) (flash T)
  have moving:=WilsonOriginalFoldedChartPayload.original R N i p hi F tag simple a
  have freeze:Wick (Woods G (coarse R i p)) C₀
      (raiseE (shot S F (prediction R N i p) (ratio R) P₀)*a)=
      insideMark S F Y (prediction R N i p) (ratio R) P₀ T:=by
    change Wick _ ((model R N i p hi).covariance F tag) _=_
    rw [covariance R N i p hi F tag]
    rfl
  have action:=WilsonCoeffUV.Winding.emera_far (levels R) simple R.alloy.B.ratio hi (fine R i p)
  have price:=inside_reed S F Y (prediction R N i p) q action.1 R.alloy.B.ratio sp
    ((levels R).blocks i p).branches (age_sym (levels R) N (i+1) _) action.2 pure
  exact moving.1.symm.trans (freeze.trans (price.trans
    (congrArg (fun x=>x*flash (filed R N i p F q T)) moving.2)))

end YM.Integration.WilsonOriginalFoldedMarkedRightColumn
