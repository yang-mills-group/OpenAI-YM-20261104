import YM.Integration.WilsonSeparatedPrefixMovingJetStock
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
namespace YM.Integration.WilsonSeparatedPrefixMovingJetPrice
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
def ticket (P:Era G (Vote D)):Volume D→ₗ[ℝ]Era G ℝ where
  toFun:=fun v=>tuftV (ContinuousLinearMap.apply ℝ ℝ v) P
  map_add':=by
    intro x y;apply Prod.ext
    · funext n i j w;change P.1 n i j _ (x+y)=P.1 n i j _ x+P.1 n i j _ y;exact map_add _ _ _
    funext i j w;change P.2 i j _ (x+y)=P.2 i j _ x+P.2 i j _ y;exact map_add _ _ _
  map_smul':=by
    intro a x;apply Prod.ext
    · funext n i j w;change P.1 n i j _ (a • x)=a • P.1 n i j _ x;exact map_smul _ _ _
    funext i j w;change P.2 i j _ (a • x)=a • P.2 i j _ x;exact map_smul _ _ _
def writing (P:Era G (Vote D))(B:Era G ℝ):Volume D→ₗ[ℝ]Era G ℝ:=
  (WilsonSeparatedPrefixMovingPhaseProduct.insert B).comp (ticket P)
def patient (R:Realm G (e+1) C){P:Era G (Vote D)}{B:Era G ℝ}(hp:Auth k P)(hb:Auth j B)
    (ear:older≤b)(top:b≤N)(user:Era G ℝ→ₗ[ℝ]ℝ):Volume D→ₗ[ℝ]ℝ where
  toFun:=fun v=>user (cruises R.draws R.paid N (k+j) b older (writing P B v))
  map_add':=by
    intro v w
    have av:Auth (k+j) (writing P B v):=spent hp hb v
    have aw:Auth (k+j) (writing P B w):=spent hp hb w
    have sub:=cruisePlus R.draws ear R.hG R.green top (av.add aw) aw
    rw [add_sub_cancel_right] at sub
    rw [map_add,sub_eq_iff_eq_add.mp sub.symm,map_add]
  map_smul':=by
    intro a w
    have aw:Auth (k+j) (writing P B w):=spent hp hb w
    rw [map_smul,WilsonSeparatedPrefixMovingFixedCapture.settled R aw a ear top,map_smul];rfl
def eligible (D:ℕ)(user:Era G ℝ→ₗ[ℝ]ℝ):Prop:=∀Z:Era G (Bank D),
  ∃f:Bank D,∀u:UnitJet D,user (tuftV (reading u) Z)=f u
theorem period (D:ℕ)(per:Side)(i r:ℕ)(w:Fin r→Woods G per):eligible D (domestic per i r w):=
  fun Z=>⟨Z.1 per i r w,fun _=>rfl⟩
theorem cover (D:ℕ)(i r:ℕ)(w:Fin r→YForest G):eligible D (abroad i r w):=
  fun Z=>⟨Z.2 i r w,fun _=>rfl⟩
theorem original (R:Realm G (e+1) C){P:Era G (Vote D)}{B:Era G ℝ}(hp:Auth k P)(hb:Auth j B)
    (ear:older≤b)(top:b≤N)(user:Era G ℝ→ₗ[ℝ]ℝ)(licensed:eligible D user):
    ∃L:Vote D,∀v,L v=user (cruises R.draws R.paid N (k+j) b older (argument P B v)):=by
  let L:=patient R hp hb ear top user
  obtain ⟨f,account⟩:=licensed (cruises R.draws R.paid N (k+j) b older (stock P B))
  have capped (u:UnitJet D):‖L u.val‖≤‖f‖:=by
    change ‖user (cruises R.draws R.paid N (k+j) b older (argument P B u.val))‖≤‖f‖
    rw [←WilsonSeparatedPrefixMovingJetStock.original R hp hb ear top u,account u]
    exact f.norm_coe_le_norm u
  have bound (v:Volume D):‖L v‖≤‖f‖*‖v‖:=by
    by_cases h:v=0
    · simp [h]
    have pos:0<‖v‖:=norm_pos_iff.mpr h
    let u:UnitJet D:=⟨‖v‖⁻¹ • v,by
      rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr pos),
        inv_mul_cancel₀ pos.ne']⟩
    have id:‖v‖ • u.val=v:=by
      change ‖v‖ • (‖v‖⁻¹ • v)=v
      rw [smul_smul,mul_inv_cancel₀ pos.ne',one_smul]
    calc ‖L v‖ = ‖v‖*‖L u.val‖ := by conv_lhs=>rw [←id,map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos pos]
         _ ≤ ‖f‖*‖v‖ := by rw [mul_comm ‖f‖];exact mul_le_mul_of_nonneg_left (capped u) pos.le
  exact ⟨L.mkContinuous ‖f‖ bound,fun _=>rfl⟩
end YM.Integration.WilsonSeparatedPrefixMovingJetPrice
