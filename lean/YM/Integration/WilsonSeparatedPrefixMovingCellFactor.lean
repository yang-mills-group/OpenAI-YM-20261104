import YM.Integration.WilsonSeparatedPrefixMovingSummedCenter

/-! Testing the actual captured tensor in the presence of a fixed field.
A continuous linear test may leave one ordinary fixed exterior unchanged
inside every normalized older transition. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingCellFactor
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical



open WilsonSeparatedPrefixMovingJointCell (toll)
variable {G:Gauge}{e h k i N older D j r:ℕ}{C:Credit}

def constant:ℝ→L[ℝ]Lounge:=ContinuousLinearMap.toSpanSingleton ℝ (1:Lounge)

theorem times (t:ℝ)(f:Lounge):constant t*f=t • f:=by
  ext z
  change (t*1)*f z=t*f z
  ring

theorem product {U:Type*}(L:Lounge→L[ℝ]ℝ)(P:Pal ℝ U)(Q:Pal Lounge U):
    ply L.toLinearMap (woad (ply constant.toLinearMap P) Q)=woad P (ply L.toLinearMap Q):=by
  ext1 i
  funext j
  change tinct L.toLinearMap ((woad _ Q) i j)=_
  unfold woad
  rw [Finset.sum_apply,Finset.sum_apply,map_sum]
  refine Finset.sum_congr rfl fun k _=>?_
  unfold knitS
  rw [cloak_swirl,map_sum]
  apply congr_arg swirl
  apply Finset.sum_congr rfl
  intro l hl
  funext x
  have ht:l.1+l.2=j:=by simpa using hl
  unfold webT
  change L (if _:_ then _ else _)=_
  rw [dif_pos ht,dif_pos ht]
  change L (constant _*_)=_*(L _)
  rw [times,map_smul]
  rfl

theorem full (L:Lounge→L[ℝ]ℝ)(A:Era G ℝ)(B:Era G Lounge):
    tuftV L (agateV (tuftV constant A) B)=agateV A (tuftV L B):=
  Prod.ext (funext fun n=>product L (A.1 n) (B.1 n)) (product L A.2 B.2)

theorem locus (z:CellR)(A:Era G ℝ):locale z (tuftV constant A)=A:=by
  apply Prod.ext
  · funext n j r w
    change ((A.1 n j r w)*1)=_
    exact mul_one _
  · funext j r w
    change ((A.2 j r w)*1)=_
    exact mul_one _

theorem original (R:Realm G (e+1) C)(A:Era G ℝ)(B:Era G Lounge)
    (ha:Auth h A)(hb:Auth k B)(ear:older ≤ i)(top:i ≤ N)
    (ψ:Phrase D)(x y:ℝ)(s:Cover)(o:CellR)(w:Fin r→YForest G):
    (cruises R.draws R.paid N (h+k) i older (agateV A (tuftV (toll ψ x y s o) B))).2 j r w=
      ∫z:CellR,(cruises R.draws R.paid N (h+k) i older (agateV A (locale z B))).2 j r w*
        ψ.val (Mer.address x y o s z.val) ∂dayMeasure:=by
  rw [←full, WilsonSeparatedPrefixMovingJointCell.original R (ha.tuft constant) hb ear top]
  simp_rw [locus]

end YM.Integration.WilsonSeparatedPrefixMovingCellFactor
