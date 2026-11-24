import YM.Integration.WilsonSeparatedPrefixMovingJetStock
import YM.Integration.WilsonSeparatedPrefixMovingFixedCapture
import YM.Integration.WilsonSeparatedPrefixMovingCenterPrint
import YM.Integration.WilsonIndependentMatchedTotalTop

/-! Every captured basis field paired with a fixed exterior has an exact
older cell-integral reading. The connected near term and all older proper
faces use the original submitted `LodeStar` at each genuine visit. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingJetChamber
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
abbrev Pair (D:ℕ):=UnitJet D × CellR
abbrev Store (D:ℕ):=BoundedContinuousFunction (Pair D) ℝ
def current (L:Vote D):Store D:=(WilsonSeparatedPrefixMovingJetBall.note L).compContinuous ⟨Prod.fst,continuous_fst⟩
def paint (D:ℕ)(f:Lounge):Store D:=(BoundedContinuousFunction.mkOfCompact f).compContinuous ⟨Prod.snd,continuous_snd⟩
def permit (D:ℕ):Vote D→L[ℝ]Store D:=LinearMap.mkContinuous
  (⟨⟨current,fun _ _=>BoundedContinuousFunction.ext fun _=>rfl⟩,fun _ _=>BoundedContinuousFunction.ext fun _=>rfl⟩:Vote D→ₗ[ℝ]Store D) 1
  (fun L=>by
    rw [one_mul]
    apply (BoundedContinuousFunction.norm_le (norm_nonneg L)).mpr
    intro z
    change ‖L z.1.val‖≤‖L‖
    simpa only [mul_one] using (L.le_opNorm z.1.val).trans (mul_le_mul_of_nonneg_left
      (WilsonSeparatedPrefixMovingJetBall.unit z.1) (norm_nonneg L)))
def rent (D:ℕ):Lounge→L[ℝ]Store D:=LinearMap.mkContinuous
  (⟨⟨paint D,fun _ _=>BoundedContinuousFunction.ext fun _=>rfl⟩,fun _ _=>BoundedContinuousFunction.ext fun _=>rfl⟩:Lounge→ₗ[ℝ]Store D) 1
  (fun f=>by
    rw [one_mul]
    exact (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr fun z=>f.norm_coe_le_norm z.2)
def stamp (z:Pair D):Store D→ₐ[ℝ]ℝ where
  toFun:=fun f=>f z
  map_one':=rfl
  map_mul' _ _:=rfl
  map_zero':=rfl
  map_add' _ _:=rfl
  commutes' _:=rfl
def att (z:Pair D):Store D→L[ℝ]ℝ:=BoundedContinuousFunction.evalCLM ℝ z
def rolled (P:Era G (Vote D))(B:Era G Lounge):Era G (Store D):=agateV (tuftV (permit D) P) (tuftV (rent D) B)
theorem paid {P:Era G (Vote D)}{B:Era G Lounge}(hp:Auth k P)(hb:Auth j B):Auth (k+j) (rolled P B):=
  (hp.tuft _).woadB (hb.tuft _) (fun z:Pair D=>stamp z) (fun _ _ hyp=>BoundedContinuousFunction.ext hyp)
theorem visit (P:Era G (Vote D))(B:Era G Lounge)(z:Pair D):
    tuftV (att z) (rolled P B)=WilsonSeparatedPrefixMovingJetStock.argument P (locale z.2 B) z.1.val:=by
  apply Prod.ext
  · exact funext fun n=>woad_ply _ _ (stamp z)
  · exact woad_ply _ _ (stamp z)
theorem original (R:Realm G (e+1) C){P:Era G (Vote D)}{B:Era G Lounge}(hp:Auth k P)(hb:Auth j B)
    (ear:older≤b)(top:b≤N)(z:Pair D):
    tuftV (att z) (cruises R.draws R.paid N (k+j) b older (rolled P B))=
      cruises R.draws R.paid N (k+j) b older (WilsonSeparatedPrefixMovingJetStock.argument P (locale z.2 B) z.1.val):=by
  rw [←visit P B z]
  exact cruiseT (att z) R.draws ear R.hG R.green top (paid hp hb)
end YM.Integration.WilsonSeparatedPrefixMovingJetChamber
