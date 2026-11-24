import YM.OPE.Compatible.Docks.Nurse
/-!
# Linear assembly across Fr basis. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Yolk
open MeasureTheory Function Filter Set
open Lattice RG Wilson Source Labels Source.Drops
open Pill Asymptotics
open Module Finset
open scoped Topology BigOperators Classical ContDiff
open Flume Flume.Page Flume.Script Silt.Float Silt
open Spells Drift Stroke
variable {I F E J:Type}{G:Gauge}{k d:ℕ}{f:Filter I}{v:I→ℝ}
-- sum pairing checkout
noncomputable def sCue (X:Labels.Frame G d): (Folio G d × Folio G d) ≃ₗ[ℝ] X.Coeff:=by
      let p : (Folio G d × Folio G d)≃ₗ[ℝ] Carton G d:={ toFun x j:=(x.1 j,x.2 j),invFun x:=(fun i=> (x i).1,fun i=>(x i).2), left_inv _:=rfl,right_inv _:=rfl,map_add' _ _:=rfl,map_smul' _ _:=rfl }; exact p.trans ((GrainΩ G d X).2.some.symm)
noncomputable def JD (v:Snap G d)(X: Labels.Frame G d): X.Coeff→L[ℂ] ℂ:= LinearMap.toContinuousLinearMap ((MvPolynomial.aeval (Next.Rank.Spindle.kp d v)).toLinearMap ∘ₗ (Next.Rank.LiftMark.Tariffs.expose X))
lemma found (X:Labels.Frame G d)(x:X.Coeff)(h:∀ v,JD v X x=0): x=0:=by
      let p:= X.coords.symm x; have he(v:Jet G): Labels.read v p.val=0:= (Next.Rank.Spindle.rewrites p v).trans (h (trunk d v)); apply X.coords.symm.injective; rw [map_zero]; exact Subtype.ext (Labels.eval_ext _ _ (fun v=>(he v).trans (map_zero (Labels.read v)).symm))
-- complex capsule structures
variable [Fintype J]
noncomputable def DuoQ : ℝ×ℝ→L[ℝ]ℂ:= (Complex.ofRealCLM.comp (.fst ..))+ Complex.I • Complex.ofRealCLM.comp (.snd ..) -- scoping
lemma echoD (x y:ℝ):DuoQ (x,y)=(x:ℂ)+Complex.I*(y:ℂ):=rfl
lemma polarZ (x:ℂ): DuoQ (x.re,x.im)=x:=by rw [echoD,mul_comm]; exact Complex.re_add_im _
lemma duetA (x:ℂ)(u): DuoQ (Az (E:=ℝ) u x)= x*DuoQ u:=by obtain ⟨a,b⟩:= u; unfold DuoQ Az; apply Complex.ext<;> simp; ring
lemma FieldSum [DecidableEq J] (P:(J→ℂ)→L[ℂ]ℂ)(x:J→ℂ):
       Arco (E:=ℝ) (fun i=>(Complex.re (P (Pi.single i 1)), Complex.im (P (Pi.single i 1)))) x=((P x).re,(P x).im):=by
           let σ z:ℝ×ℝ:=((z:ℂ).re,z.im); apply (show Injective DuoQ from fun u w h=>Prod.ext (by simpa [DuoQ] using congr_arg Complex.re h) (by simpa [DuoQ] using congr_arg Complex.im h)); rw [bWire,map_sum,polarZ]; conv_rhs=> rhs; rw [show x=∑ i:J,x i • Pi.single i 1 from _root_.funext fun i=>by rw [Finset.sum_apply];simp [Pi.single_apply]]
           rw [map_sum]; exact Finset.sum_congr rfl fun i _=>by rw[duetA,polarZ,map_smul];rfl
section mix
variable [NormedAddCommGroup E][NormedSpace ℝ E]
omit [NormedSpace ℝ E] in lemma TwinC {s:ℝ} {p q:I→E}(he:Wax v f p s)(h:Wax v f q s) : Wax v f (fun i => (p i,q i)) s:=by
      intro a ha; filter_upwards [he a ha,h a ha] with i hi hv; rw[Prod.norm_def]; exact max_le hi hv
lemma timers (p:I→J→E×E)(q:J→E×E)(h:∀ j,Tendsto (fun i=>p i j) f (𝓝 (q j))) (x:J→ℂ):Tendsto (fun i=>Arco (p i) x) f (𝓝 (Arco q x)):=by
       simp_rw[bWire]; refine tendsto_finsetSum (s:=Finset.univ) (fun i _=>?_); let v:E×E→E×E:=fun y=> Az y (x i); have hv:Continuous v:=by change Continuous (fun y:E×E=> (x i).re • y+(x i).im • (-y.2,y.1)); fun_prop
       exact hv.continuousAt.tendsto.comp (h i)
end mix
end YM.OPE.Yolk
