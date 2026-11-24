import YM.Integration.WilsonSeparatedPrefixMovingCenterPrint
import YM.Integration.WilsonSeparatedPrefixMovingBeforeCapture

/-! Integrating one original common center after a joint normalized transfer
is an actual measured linear map. Point evaluation retains both factors. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingJointCell
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical


variable {G:Gauge}{e i j r d h k D u N:ℕ}{C:Credit}
variable (R:Realm G (e+1) C)

def toll (ψ:Phrase D)(x y:ℝ)(site:Cover)(o:CellR):Lounge→L[ℝ]ℝ:=
  ((century o).comp (demonstrate (wheelC x y site ψ))).comp (HourFace dayMeasure D)

theorem paid (v:Lounge)(ψ:Phrase D)(x y:ℝ)(site:Cover)(o:CellR):
    toll ψ x y site o v=∫z:CellR, v z*ψ.val (Mer.address x y o site z.val) ∂dayMeasure:=by
  exact hour_at dayMeasure v (sonal x y o site ψ)

theorem atCenter {A B:Era G Lounge}(ha:Auth h A)(hb:Auth k B)
    (lower:u≤ i)(top:i≤N)(z:CellR):
    locale z (cruises R.draws R.paid N (h+k) i u (agateV A B))=
      cruises R.draws R.paid N (h+k) i u (agateV (locale z A) (locale z B)):=by
  change tuftV (century z) _=_
  rw [cruiseT (century z) _ lower R.hG R.green top (agateHome ha hb)]
  apply congr_arg (cruises R.draws R.paid N (h+k) i u)
  exact woadChart z A B

theorem original {A B:Era G Lounge}(ha:Auth h A)(hb:Auth k B)
    (lower:u≤ i)(top:i≤N)(ψ:Phrase D)(x y:ℝ)(site:Cover)(o:CellR)(w:Fin r→YForest G):
    (cruises R.draws R.paid N (h+k) i u (tuftV (toll ψ x y site o) (agateV A B))).2 j r w=
      ∫z:CellR,(cruises R.draws R.paid N (h+k) i u (agateV (locale z A) (locale z B))).2 j r w*
        ψ.val (Mer.address x y o site z.val) ∂dayMeasure:=by
  rw [←cruiseT (toll ψ x y site o) _ lower R.hG R.green top (agateHome ha hb)]
  change toll ψ x y site o _=_
  rw [paid]
  congr 1
  funext z
  congr 1
  exact congr_arg (fun X:Era G ℝ=>X.2 j r w) (atCenter R ha hb lower top z)

end YM.Integration.WilsonSeparatedPrefixMovingJointCell
