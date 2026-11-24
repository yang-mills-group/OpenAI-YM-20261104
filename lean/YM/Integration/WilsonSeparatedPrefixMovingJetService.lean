import YM.Integration.WilsonSeparatedPrefixMovingJetChamber
import YM.Integration.WilsonSeparatedPrefixMovingJetPrice
import YM.Integration.WilsonSeparatedPrefixMovingFixedCapture
import YM.Integration.WilsonSeparatedPrefixMovingCenterPrint
import YM.Integration.WilsonIndependentMatchedTotalTop

/-! Every captured basis field paired with a fixed exterior has an exact
older cell-integral reading. The connected near term and all older proper
faces use the original submitted `LodeStar` at each genuine visit. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingJetService
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical



open WilsonSeparatedPrefixMovingJointCell (toll)

open WilsonSeparatedPrefixMovingCellFactor (constant)
open WilsonIndependentMatchedCoverProfile
variable {G:Gauge}{H:Hol G}{n e h k D b m N older:ℕ}{C W V:Credit}

open WilsonSeparatedPrefixMovingJetBall (UnitJet)
variable {D j:ℕ}
open WilsonSeparatedPrefixMovingJetChamber (Pair Store att rolled)
open WilsonSeparatedPrefixMovingJointFarBook (domestic abroad)
def size (v:Volume D):ℝ:=max 1 ‖v‖
theorem positive (v:Volume D):0<size v:=lt_of_lt_of_le zero_lt_one (le_max_left _ _)
def pilot (v:Volume D):UnitJet D:=⟨(size v)⁻¹ • v,by
  rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (positive v)),
    inv_mul_le_iff₀ (positive v),mul_one]
  exact le_max_right _ _⟩
theorem resized (v:Volume D):size v • (pilot v).val=v:=by
  change size v • ((size v)⁻¹ • v)=v
  rw [smul_smul,mul_inv_cancel₀ (positive v).ne',one_smul]
theorem smoothSize :Continuous (size (D:=D)):=continuous_const.max continuous_norm
theorem smoothPilot :Continuous (pilot (D:=D)):=Continuous.subtype_mk
  ((smoothSize.inv₀ fun v=>(positive v).ne').smul continuous_id) _
def eligible (D:ℕ)(user:Era G ℝ→ₗ[ℝ]ℝ):Prop:=∀Z:Era G (Store D),
  ∃f:Store D,∀z:Pair D,user (tuftV (att z) Z)=f z
theorem period (D:ℕ)(per:Side)(i r:ℕ)(w:Fin r→Woods G per):eligible D (domestic per i r w):=
  fun Z=>⟨Z.1 per i r w,fun _=>rfl⟩
theorem cover (D:ℕ)(i r:ℕ)(w:Fin r→YForest G):eligible D (abroad i r w):=
  fun Z=>⟨Z.2 i r w,fun _=>rfl⟩
def actual (R:Realm G (e+1) C)(N k j b older:ℕ)(P:Era G (Vote D))(B:Era G Lounge)
    (user:Era G ℝ→ₗ[ℝ]ℝ)(z:CellR×Volume D):ℝ:=
  user (cruises R.draws R.paid N (k+j) b older (WilsonSeparatedPrefixMovingJetStock.argument P (locale z.1 B) z.2))
theorem original (R:Realm G (e+1) C){P:Era G (Vote D)}{B:Era G Lounge}(hp:Auth k P)(hb:Auth j B)
    (ear:older≤b)(top:b≤N)(user:Era G ℝ→ₗ[ℝ]ℝ)(license:eligible D user):
    let pay:=actual R N k j b older P B user
    Continuous pay ∧ ∃M:ℝ,0≤M∧∀(z:CellR)(v:Volume D),‖pay (z,v)‖≤M*size v:=by
  intro pay
  obtain ⟨f,book⟩:=license (cruises R.draws R.paid N (k+j) b older (rolled P B))
  have heard (w:Pair D):pay (w.2,w.1.val)=f w:=by
    change user (cruises R.draws R.paid N (k+j) b older _)=f w
    rw [←WilsonSeparatedPrefixMovingJetChamber.original R hp hb ear top w]
    exact book w
  have eq (w:CellR×Volume D):pay w=size w.2*f (pilot w.2,w.1):=by
    let L:=WilsonSeparatedPrefixMovingJetPrice.patient R hp (hb.tuft (century w.1)) ear top user
    have who:pay w=L w.2:=rfl
    rw [who,←heard (pilot w.2,w.1)]
    change L w.2=size w.2 • L (pilot w.2).val
    rw [←L.map_smul, resized]
  have cont:Continuous fun w:CellR×Volume D=>f (pilot w.2,w.1):=
    f.continuous.comp ((smoothPilot.comp continuous_snd).prodMk continuous_fst)
  refine ⟨(smoothSize.comp continuous_snd |>.mul cont).congr (fun w=>(eq w).symm),‖f‖,norm_nonneg _,?_⟩
  intro z v
  rw [eq,norm_mul,Real.norm_eq_abs,abs_of_pos (positive v),mul_comm ‖f‖]
  exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (positive v).le
end YM.Integration.WilsonSeparatedPrefixMovingJetService
