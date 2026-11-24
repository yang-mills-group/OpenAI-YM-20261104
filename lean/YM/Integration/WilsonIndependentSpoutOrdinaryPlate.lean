import YM.Integration.WilsonIndependentSpoutWilsonJets

/-! The positively graded plaquettes of the genuine cover notebook,
read on every ordinary periodic board and arbitrary ordinary connection. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutOrdinaryPlate
open Lattice Exterior WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue
open RegulatorIR RegulatorIR.Prim RegulatorIR.Binding RegulatorIR.Budget
open RegulatorIR.Diagram RegulatorIR.Diagram.Formal
open PertExtension.Series.Radial PowerSeries
open scoped Classical BigOperators ContDiff
variable {G:Gauge}{n:Side}

def sample (y:TreeVars G n)(q:Foot G):ℝ :=
  ((cloth G n).symm y (wrap n q.1.1,coord q.1.2)) q.2

def base (p:Face (Per n)):Face ℤ:=(lift p.1,p.2)

theorem dilate (y:TreeVars G n)(t:ℝ):sample (t • y)=t • sample y := by
  funext q;unfold sample;rw [map_smul];rfl

theorem links (y:TreeVars G n):
    win G (sample y) = expandAt 0 (mantle y) := by
  funext i
  unfold win expandAt mantle
  rw [Work.F03.represent_link,add_zero]
  congr 1

theorem face (S:Scale)(p:Face (Per n))(y:TreeVars G n)(t:ℝ) :
    flank (Prim.plain S G (base p)) (sample y) t =
      S.beta t*G.price (faceValue (mantle (t • y)) p) := by
  unfold flank Prim.plain
  rw [←dilate,links]
  simp only [base,faceValue,travel_at,wrap_lift,add_zero]

theorem run (y:TreeVars G n):
    (∑ p:Face (Per n),tale (flank (Prim.plain Clocks.flat G (base p)) (sample y))) =
      tale (fun t:ℝ=>eWilson (t • y)) := by
  rw [←tale_sum _ _ (fun p _=>(boons G Clocks.flat (base p)).some.smooth_v _)]
  apply congrArg tale
  funext t
  rw [Finset.sum_apply]
  simp only [face,Clocks.flat,one_mul]
  rfl

theorem original {T:Face ℤ→ Orders (Foot G)}(V:Plane Clocks.flat G T)
    (y:TreeVars G n)(e:ℕ)(pos:0<e):
    (∑ p:Face (Per n),drums (T (base p) e) (e+2) (sample y)) =
      -PowerSeries.coeff (e+2) (tale (fun t:ℝ=>eWilson (t • y))) := by
  simp_rw [(V _).figures _ pos,neg_one_mul]
  rw [Finset.sum_neg_distrib,←map_sum,run]

end YM.Integration.WilsonIndependentSpoutOrdinaryPlate
