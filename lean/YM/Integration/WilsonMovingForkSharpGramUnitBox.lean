import YM.Integration.WilsonSeparatedPrefixMovingJetChamber

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpGramUnitBox
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
variable {E:ℕ}
abbrev Pair (D E:ℕ):=UnitJet D × UnitJet E
abbrev Store (D E:ℕ):=BoundedContinuousFunction (Pair D E) ℝ
def first (L:Vote D):Store D E:=(WilsonSeparatedPrefixMovingJetBall.note L).compContinuous ⟨Prod.fst,continuous_fst⟩
def firstC (D E:ℕ):Vote D →L[ℝ] Store D E:=LinearMap.mkContinuous
  (⟨⟨first,fun _ _=>BoundedContinuousFunction.ext fun _=>rfl⟩,fun _ _=>BoundedContinuousFunction.ext fun _=>rfl⟩:Vote D→ₗ[ℝ]Store D E) 1
  (fun L=>by
    rw [one_mul]
    apply (BoundedContinuousFunction.norm_le (norm_nonneg L)).mpr
    intro z
    change ‖L z.1.val‖ ≤ ‖L‖
    simpa only [mul_one] using (L.le_opNorm z.1.val).trans (mul_le_mul_of_nonneg_left
      (WilsonSeparatedPrefixMovingJetBall.unit z.1) (norm_nonneg L)))
def second (L:Vote E):Store D E:=(WilsonSeparatedPrefixMovingJetBall.note L).compContinuous ⟨Prod.snd,continuous_snd⟩
def secondC (D E:ℕ):Vote E →L[ℝ] Store D E:=LinearMap.mkContinuous
  (⟨⟨second,fun _ _=>BoundedContinuousFunction.ext fun _=>rfl⟩,fun _ _=>BoundedContinuousFunction.ext fun _=>rfl⟩:Vote E→ₗ[ℝ]Store D E) 1
  (fun L=>by
    rw [one_mul]
    apply (BoundedContinuousFunction.norm_le (norm_nonneg L)).mpr
    intro z
    change ‖L z.2.val‖ ≤ ‖L‖
    simpa only [mul_one] using (L.le_opNorm z.2.val).trans (mul_le_mul_of_nonneg_left
      (WilsonSeparatedPrefixMovingJetBall.unit z.2) (norm_nonneg L)))
def stamp (z:Pair D E):Store D E→ₐ[ℝ]ℝ where
  toFun:=fun f=>f z
  map_one':=rfl
  map_mul' _ _:=rfl
  map_zero':=rfl
  map_add' _ _:=rfl
  commutes' _:=rfl
def att (z:Pair D E):Store D E→L[ℝ]ℝ:=BoundedContinuousFunction.evalCLM ℝ z
def bank (P:Era G (Vote D))(Q:Era G (Vote E)):Era G (Store D E):=agateV (tuftV (firstC D E) P) (tuftV (secondC D E) Q)
def tested (P:Era G (Vote D))(Q:Era G (Vote E))(a:Volume D)(b:Volume E):Era G ℝ:=
  agateV (tuftV (ContinuousLinearMap.apply ℝ ℝ a) P) (tuftV (ContinuousLinearMap.apply ℝ ℝ b) Q)
theorem paid {P:Era G (Vote D)}{Q:Era G (Vote E)}(hp:Auth k P)(hq:Auth j Q):Auth (k+j) (bank P Q):=
  (hp.tuft _).woadB (hq.tuft _) (fun z:Pair D E=>stamp z) (fun _ _ hyp=>BoundedContinuousFunction.ext hyp)
theorem visit (P:Era G (Vote D))(Q:Era G (Vote E))(z:Pair D E):
    tuftV (att z) (bank P Q)=tested P Q z.1.val z.2.val:=by
  apply Prod.ext
  · exact funext fun n=>woad_ply _ _ (stamp z)
  · exact woad_ply _ _ (stamp z)

theorem original (R:Realm G (e+1) C){P:Era G (Vote D)}{Q:Era G (Vote E)}(hp:Auth k P)(hq:Auth j Q)
    (ear:older ≤ b)(top:b ≤ N)(i r:ℕ)(leg:Fin r→YForest G):
    let K:=‖(cruises R.draws R.paid N (k+j) b older (bank P Q)).2 i r leg‖
    ∀z:Pair D E,‖(cruises R.draws R.paid N (k+j) b older (tested P Q z.1.val z.2.val)).2 i r leg‖ ≤ K:=by
  intro K z
  have live:tuftV (att z) (cruises R.draws R.paid N (k+j) b older (bank P Q))=
      cruises R.draws R.paid N (k+j) b older (tested P Q z.1.val z.2.val):=by
    rw [←visit P Q z]
    exact cruiseT (att z) R.draws ear R.hG R.green top (paid hp hq)
  rw [←live]
  exact BoundedContinuousFunction.norm_coe_le_norm _ z

end YM.Integration.WilsonMovingForkSharpGramUnitBox
