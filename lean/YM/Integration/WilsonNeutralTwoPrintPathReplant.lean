import YM.Integration.WilsonReceivedCanonicalVerseTrial
import YM.Integration.WilsonMarkedIndependentFoldedBirth
import YM.Integration.WilsonMarkedIndependentMixedSeam

/-! The actual finite socket of a dated reprint on the original folded Wilson step. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace YM.Integration.WilsonNeutralTwoPrintPathReplant
open Function Filter Finset Lattice Wilson RG Precision Laurent WilsonCoeffUV Tree Bloch Exterior
open Next.Foundations PhysicalNext.Repeat.Legato
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open WilsonReceivedDatedVerseReprint WilsonReceivedCompactVerseEntrance
open WilsonMarkedIndependentPhysicalIntake WilsonMarkedIndependentMixedGeometry
open AnalyticNext.QuarticMatch.Sheets IndependentSourcePathFamily
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{D k:I→ℕ}{e:ℕ}

omit [DecidableEq I] in
/-- The whole original path table, after the actual reprint of every proper face,
is fixed by periodic assembly, including coefficients beyond the requested grade. -/
theorem unfold_period (Y:Outerm G D)(well:Wellness k Y){s A:ℝ}(width:0<s)(budget:1≤A)
    (cash:CoverBill Y e s A)(y:I → Cover):
    repaint ((submit Y k e) y)=submit Y k e y:=by
  classical
  funext J
  by_cases live:J.Nonempty
  · obtain ⟨t,C,pos,_,_,paid⟩:=word Y well width (zero_le_one.trans budget) cash J
    have issued:Issued Y k e J live.choose y t s C (A^J.card):= (paid _ live.choose_spec y).1
    have exactPeriod:= (root_robe _ issued.1 pos (y live.choose)).2
    apply Prod.ext
    · funext n h r
      change plume (((submit Y k e) y J).2 h r) n=((submit Y k e) y J).1 n h r
      simpa only [submit,dif_pos live,printed] using (exactPeriod n h r).symm
    · rfl
  · rw [show (submit Y k e y J)=0 by simp only [submit,dif_neg live]]
    apply Prod.ext
    · funext n h r
      change plume (((submit Y k e) y J).2 h r) n=0
      simp only [submit,dif_neg live]
      exact plume_zero n
    · change ((submit Y k e) y J).2=(0:Era G (Pen D J)).2
      simp [submit,live]

/-- The selected single face, with its signed test, inside the normalized finite
conditional before the original numerical change of coupling. -/
theorem one (R:Run G)(Y:Outerm G D)(well:Wellness k Y){s A:ℝ}(width:0<s)(budget:1≤A)
    (cash:CoverBill Y e s A)(y:I → Cover)(w:I)(N j:ℕ)(n:Side)(test:Case D)(coin:Cost):
    let E:=submit Y k e y
    let T:=tuftV (touch test {w}) (E {w})
    pPly test {w} (coilH R.family.path.levels R.metals.O j N n E k coin {w})=
      Blue.mix coin (WilsonMarkedIndependentFoldedIntegral.folded R N j (mass k {w}) T.1 n):=by
  intro E T
  have law:= (WilsonReceivedCompactVerseEntrance.original Y well width budget cash).2.1
  rw [WilsonMarkedIndependentFoldedBirth.singleton R.family.path.levels R.metals.O j N n w E
    (law.level' y) (law.quiet' y) coin,show repaint E=E from unfold_period Y well width budget cash y]
  unfold pPly
  rw [ply_mixX]
  apply congr_arg _
  exact reed_maps _ _ _ _ (mass k {w}) (touch test {w}).toLinearMap

end YM.Integration.WilsonNeutralTwoPrintPathReplant
end
