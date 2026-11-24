import YM.Integration.WilsonIndependentPublicSpoutGround

/-! All Wilson plaquette orders before the first tagged integration.
The action on the inversion orbit is one half of the same unscaled Mer
action on the equivariantly lifted connection, at every real coupling. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutWilsonAction
open Lattice WilsonCoeffUV RegulatorIR RegulatorIR.Binding RegulatorIR.Laplace
open RegulatorIR.Prim RegulatorIR.Geometry RegulatorIR.Quadratic
open scoped Classical
variable {G:Gauge}{f:Side}

def opening (x:Horizon G f):TreeVars G f:=cloth G f (canvas x)

theorem dilate (x:Horizon G f)(t:ℝ): opening (t • x)=t • opening x := by
  rw [opening,canvas_rate,map_smul]; rfl

theorem original (x:Horizon G f):
    valueO (climb x)=eWilson (opening x)/2 := by
  rw [valueO,mat_expanded]
  rfl

theorem rays (S:Scale)(x:Horizon G f) :
    inscription (priceMap (startO S)) ((0,1,x):Meadow G Empty × ℝ × Horizon G f) =
      tale (fun t:ℝ=>S.beta t*(eWilson (t • opening x)/2)) := by
  rw [←lore (startF S).smooth]
  apply congrArg tale
  funext t
  change S.beta (t*1)*valueO (climb (t • x))=_
  rw [mul_one,original,dilate]

theorem paid (S:Scale)(he:Even f.val){l P:ℝ}(hP:l*f.val=P)(x:Horizon G f):
    (∑ u:PFace f,tale (flank (Prim.plain S G (reachF u))
      (bridge (Carto G l P he hP) (paper G f x)))) =
      tale (fun t:ℝ=>S.beta t*(eWilson (t • opening x)/2)) := by
  rw [←priceStart S he hP x,rays]

end YM.Integration.WilsonIndependentSpoutWilsonAction
