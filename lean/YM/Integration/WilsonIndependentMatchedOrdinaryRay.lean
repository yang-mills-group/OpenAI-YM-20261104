import YM.Integration.WilsonIndependentRawNamedStencil
import YM.Integration.WilsonIndependentSpoutOrdinaryPlate
import YM.Integration.WilsonIndependentMatchedTopStencils

/-! The actual translated Wilson stencil and its registered cover tensor have the
same Taylor series on every periodic angular direction, before Wick integration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedOrdinaryRay
open Matrix Lattice RG Source Labels Wilson PhysicalNext.Repeat.Legato
open PowerSeries WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Soil WilsonCoeffUV.Power WilsonCoeffUV.Embroider FreeResolvent Exterior PertExtension XSpace XSpace.Rose
open PertExtension.Series.Radial RegulatorIR RegulatorIR.Geometry RegulatorIR.Halo
open RegulatorIR.Binding RegulatorIR.Prim RegulatorIR.Diagram
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentRawNamedStencil (brand)
open WilsonIndependentSpoutOrdinaryPlate (sample)
open scoped Classical ContDiff
variable {G:Gauge}(R:Run G)(W:Initialize G){d:ℕ}
local notation "F" => R.family.labels.level d

def group {n:Side}(kind:Bool)(b:(F).Index)(o:Cover)(y:TreeVars G n):ℝ:=
  ((sectionAt R W kind d).places (Pi.single b 1) (wrap n o) (mantle y)).re

theorem field {n:Side}(kind:Bool)(b:(F).Index)(o:Cover)(y:TreeVars G n)(t:ℝ):
    outing G (convey o (brand R W kind d b)) (sample y) t=
      group R W kind b o (t • y):=by
  unfold outing
  rw [←WilsonIndependentSpoutOrdinaryPlate.dilate,WilsonIndependentSpoutOrdinaryPlate.links]
  have eq:translate o (expandAt 0 (mantle (t • y)))=
      expandAt (wrap n o) (mantle (t • y)):=by
    funext i
    change (mantle (t • y)) (wrap n (i.1+o)+0,i.2)=
      (mantle (t • y)) (wrap n i.1+wrap n o,i.2)
    rw [add_zero,map_add]
  change ((sectionAt R W kind d).evaluate _ _).re=_
  rw [eq]
  rfl

theorem original {n:Side}(kind:Bool)(b:(F).Index)(o:Cover)(y:TreeVars G n):
    let h:=((F).grades b).2
    X^h*shelter h (WilsonIndependentRawNamedStencil.shifted R W kind d b o) (sample y)=
      tale (fun t:ℝ=>group R W kind b o (t • y)):=by
  dsimp only
  rw [←(WilsonIndependentRawNamedStencil.named R W kind d b o).1.pose]
  exact congrArg tale (funext (field R W kind b o y))

theorem moved {n:Side}(kind:Bool)(b:(F).Index)(o:Cover)(y:TreeVars G n):
    group R W kind b o y=Plies (sectionAt R W kind d) b n
      (spear (jog (wrap n o):Woods G n ≃ Woods G n)*ᵥy):=by
  unfold Plies group
  rw [mantle_reads,Lattice.pull_one,SectionData.places_trans,zero_add]

theorem smooth {n:Side}(kind:Bool)(b:(F).Index)(o:Cover):
    Green (group (n:=n) R W kind b o):=by
  have h:Green (Plies (sectionAt R W kind d) b n):=by
    cases kind with
    | false=>exact innu _ _ (R.makes.sections d) b n
    | true=>exact innu _ W.hol (WilsonOriginalPivotWardSurvey.issued R W d).1 b n
  rw [show group (n:=n) R W kind b o=(fun y=>Plies (sectionAt R W kind d) b n
      (spear (jog (wrap n o):Woods G n≃ Woods G n)*ᵥ y)) from funext (moved R W kind b o)]
  let M:=spear (jog (wrap n o):Woods G n ≃ Woods G n)
  have hh:ContDiffAt ℝ ω (Plies (sectionAt R W kind d) b n) (M*ᵥ0):=by simpa only [Matrix.mulVec_zero] using h
  exact hh.comp (f:=fun v:TreeVars G n=>M*ᵥv) 0 (board M)

theorem evaluate {n:Side}(f:TreeVars G n→ℝ)(h:Green f)(y:TreeVars G n):
    PowerSeries.map (MvPolynomial.eval y) (jet f)=tale (fun t:ℝ=>f (t • y)):=by
  ext1 e
  rw [coeff_map,rayon,lore (h.of_le (by simp):ContDiffAt ℝ ∞ f 0) y]
  simp only [inscription,coeff_mk]
  rfl

theorem registered {n:Side}(kind:Bool)(b:(F).Index)(o:Cover)(y:TreeVars G n):
    let h:=((F).grades b).2
    X^h*shelter h (WilsonIndependentRawNamedStencil.shifted R W kind d b o) (sample y)=
      PowerSeries.map (MvPolynomial.eval y) (jet (group R W kind b o)):=by
  rw [evaluate _ (smooth R W kind b o)]
  exact original R W kind b o y

end YM.Integration.WilsonIndependentMatchedOrdinaryRay
