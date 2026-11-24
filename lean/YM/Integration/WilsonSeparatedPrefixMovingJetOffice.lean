import YM.Integration.WilsonSeparatedPrefixMovingJetPrice
import Mathlib.LinearAlgebra.Projection
import YM.Integration.WilsonSeparatedPrefixMovingJointFarBook
import YM.Integration.WilsonSeparatedPrefixMovingPhaseProduct
import YM.Integration.WilsonSeparatedPrefixMovingFixedCapture
import YM.Integration.WilsonSeparatedPrefixMovingCenterPrint
import YM.Integration.WilsonIndependentMatchedTotalTop

/-! Every captured basis field paired with a fixed exterior has an exact
older cell-integral reading. The connected near term and all older proper
faces use the original submitted `LodeStar` at each genuine visit. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingJetOffice
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical



open WilsonSeparatedPrefixMovingJointCell (toll)

open WilsonSeparatedPrefixMovingCellFactor (constant)
open WilsonIndependentMatchedCoverProfile
variable {G:Gauge}{H:Hol G}{n e h k D b m N older:ℕ}{C W V:Credit}

open WilsonSeparatedPrefixMovingJetBall (UnitJet register sterling inspect reading)
variable {D j:ℕ}
open WilsonSeparatedPrefixMovingJetStock (argument spent stock)
open WilsonSeparatedPrefixMovingPhaseProduct (insert)
open WilsonSeparatedPrefixMovingJetBall (Bank)
open WilsonSeparatedPrefixMovingJointFarBook (domestic abroad)
open private seat from YM.Integration.WilsonSeparatedPrefixMovingPhasePupil
def roster (G:Gauge)(k:ℕ):Submodule ℝ (Era G ℝ) where
  carrier:={P|Auth k P}
  zero_mem':=by let Z:Unit→Era G ℝ:=fun _=>0;simpa using Auth.sum (P:=Z) (S:=∅) (by simp)
  add_mem':=fun hx hy=>hx.add hy
  smul_mem':=fun t X hX=>hX.μ t
def accounts (R:Realm G (e+1) C){B:Era G ℝ}(hb:Auth j B)(ear:older≤b)(top:b≤N)
    (user:Era G ℝ→ₗ[ℝ]ℝ)(k:ℕ):roster G k→ₗ[ℝ]ℝ where
  toFun:=fun A=>user (cruises R.draws R.paid N (k+j) b older (WilsonSeparatedPrefixMovingPhaseProduct.insert B A.val))
  map_add':=by
    intro X Y
    change user (cruises R.draws R.paid N (k+j) b older (WilsonSeparatedPrefixMovingPhaseProduct.insert B (X.val+Y.val)))=_
    let L:=WilsonSeparatedPrefixMovingPhaseProduct.insert B
    have ax:Auth (k+j) (L X.val):=X.property.manor hb
    have ay:Auth (k+j) (L Y.val):=Y.property.manor hb
    have sub:=cruisePlus R.draws ear R.hG R.green top (ax.add ay) ay
    rw [add_sub_cancel_right] at sub
    change user (cruises R.draws R.paid N (k+j) b older (L (X.val+Y.val)))=_
    rw [map_add,sub_eq_iff_eq_add.mp sub.symm,map_add]
  map_smul':=by
    intro t X
    let L:=WilsonSeparatedPrefixMovingPhaseProduct.insert B
    have ax:Auth (k+j) (L X.val):=X.property.manor hb
    change user (cruises R.draws R.paid N (k+j) b older (L (t • X.val)))=_
    rw [map_smul,WilsonSeparatedPrefixMovingFixedCapture.settled R ax t ear top,map_smul];rfl
theorem original (R:Realm G (e+1) C){B:Era G ℝ}(hb:Auth j B)(ear:older≤b)(top:b≤N)
    (user:Era G ℝ→ₗ[ℝ]ℝ){P:TowerS G D}(hp:Auth k P)(license:WilsonSeparatedPrefixMovingJetPrice.eligible D user):
    ∃prior:Era G ℝ→ₗ[ℝ]ℝ,(∀A:Era G ℝ,Auth k A→prior A=
      user (cruises R.draws R.paid N (k+j) b older (agateV A B))) ∧
      WilsonSeparatedPrefixMovingJointFarBook.commissioned P prior:=by
  obtain ⟨Z,other⟩:=Submodule.exists_isCompl (roster G k)
  let prior:=(accounts R hb ear top user k).comp ((roster G k).projectionOnto Z other)
  have received (A:Era G ℝ)(w:Auth k A):prior A=user (cruises R.draws R.paid N (k+j) b older (agateV A B)):=by
    change accounts R hb ear top user k ((roster G k).projectionOnto Z other A)=_
    rw [Submodule.projectionOnto_apply_of_mem_left other w]
    rfl
  refine ⟨prior,received,?_⟩
  intro s
  obtain ⟨L,hL⟩:=WilsonSeparatedPrefixMovingJetPrice.original R (hp.shifted s) hb ear top user license
  refine ⟨L,fun v=>?_⟩
  have sv:Auth k (seat P s v):=(hp.tuft (ContinuousLinearMap.apply ℝ ℝ v)).shifted s
  rw [received (seat P s v) sv,hL v]
  rfl
end YM.Integration.WilsonSeparatedPrefixMovingJetOffice
