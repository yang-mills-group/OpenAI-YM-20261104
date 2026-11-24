import YM.Integration.WilsonSeparatedPrefixMovingPhaseStencil
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! A coefficient of the translated exterior is an actual derivative of the
same smooth compact test. Its registered jets may be read in either order. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingProfileDerivatives
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical ContDiff
open WilsonCoeffUV.Layout
variable {D n j:ℕ}
def partials (f:Point4→ℝ)(a:Fin n→Point4):Point4→ℝ:=
  fun x=>iteratedFDeriv ℝ n f x a
def along (v:Point4)(f:Point4→ℝ):Point4→ℝ:=fun x=>fderiv ℝ f x v
private theorem smooths (f:Point4→ℝ)(hf:ContDiff ℝ ∞ f)(a:Fin n→Point4):
    ContDiff ℝ ∞ (partials f a):=
  contDiff_infty.mpr fun k=>(ContinuousMultilinearMap.apply ℝ (fun _:Fin n=>Point4) ℝ a).contDiff.comp
    ((contDiff_infty.mp hf (k+n)).iteratedFDeriv_right (by exact_mod_cast le_refl (k+n)))
private theorem smooth (f:Point4→ℝ)(hf:ContDiff ℝ ∞ f)(v:Point4):ContDiff ℝ ∞ (along v f):=
  contDiff_infty.mpr fun k=>(ContinuousLinearMap.apply ℝ ℝ v).contDiff.comp
    ((contDiff_infty.mp hf (k+1)).fderiv_right (by exact_mod_cast le_refl (k+1)))
private theorem adjacent (f:Point4→ℝ)(hf:ContDiff ℝ ∞ f)(v w:Point4):
    along v (along w f)=along w (along v f):=by
  funext x
  let A:=fun v:Point4=>ContinuousLinearMap.apply ℝ ℝ v
  have h: DifferentiableAt ℝ (fderiv ℝ f) x:=((contDiff_infty.mp hf 2).fderiv_right (m:=1) (by norm_num)).contDiffAt.differentiableAt (by simp)
  change fderiv ℝ (A w ∘ fderiv ℝ f) x v = fderiv ℝ (A v ∘ fderiv ℝ f) x w
  rw [fderiv_comp x (A w).differentiableAt h,fderiv_comp x (A v).differentiableAt h,
    ContinuousLinearMap.fderiv,ContinuousLinearMap.fderiv]
  exact (contDiff_infty.mp hf 2).contDiffAt.isSymmSndFDerivAt (by simp) v w
private theorem leading (f:Point4→ℝ)(hf:ContDiff ℝ ∞ f)(a:Fin (n+1)→Point4):
    partials f a=along (a 0) (partials f (Fin.tail a)):=by
  funext x
  let L:=ContinuousMultilinearMap.apply ℝ (fun _:Fin n=>Point4) ℝ (Fin.tail a)
  change iteratedFDeriv ℝ (n+1) f x a=fderiv ℝ (L ∘ iteratedFDeriv ℝ n f) x (a 0)
  have h:DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x:=
    ((contDiff_infty.mp hf (1+n)).iteratedFDeriv_right (i:=n) (m:=1) (by exact_mod_cast le_refl (1+n))).contDiffAt.differentiableAt (by simp)
  rw [iteratedFDeriv_succ_apply_left,fderiv_comp x L.differentiableAt h,ContinuousLinearMap.fderiv]
  rfl
private theorem through (f:Point4→ℝ)(hf:ContDiff ℝ ∞ f)(v:Point4)(a:Fin n→Point4):
    along v (partials f a)=partials (along v f) a:=by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [leading f hf a,leading (along v f) (smooth f hf v) a,
      adjacent _ (smooths f hf (Fin.tail a)), ih (Fin.tail a)]
theorem exchange (f:Point4→ℝ)(hf:ContDiff ℝ ∞ f)(a:Fin n→Point4)(b:Fin j→Point4):
    partials (partials f b) a=partials (partials f a) b:=by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [leading (partials f b) (smooths f hf b) a,ih (Fin.tail a),leading f hf a,
      through _ (smooths f hf (Fin.tail a))]
def cut (φ:Rarity D)(hf:ContDiff ℝ ∞ φ.ψ.val)(a:Fin n→Axis):Rarity D where
  ψ:=⟨crease φ.ψ a,(show ContDiff ℝ D (crease φ.ψ a) from contDiff_infty.mp (smooths φ.ψ.val hf (Embroider.dot ∘ a)) D)⟩
  radius:=φ.radius
  markG:=φ.markG
  support:=closure_minimal (fun x hx=>φ.support (crestShelter x hx)) Metric.isClosed_closedBall
theorem original (φ:Rarity D)(hf:ContDiff ℝ ∞ φ.ψ.val)(a:Fin n→Axis)(b:Fin j→Axis)(x:Point4):
    iteratedFDeriv ℝ n (crease φ.ψ b) x (Embroider.dot ∘ a)=crease (cut φ hf a).ψ b x:=
  congrFun (exchange φ.ψ.val hf (Embroider.dot ∘ a) (Embroider.dot ∘ b)) x
end YM.Integration.WilsonSeparatedPrefixMovingProfileDerivatives
