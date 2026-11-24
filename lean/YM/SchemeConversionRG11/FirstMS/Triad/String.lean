import YM.SchemeConversionRG11.FirstMS.DR.Annuli
import YM.SchemeConversionRG11.FirstMS.DR.Mellin
import YM.Pert.Triangle.Kernels
import YM.MSbar.Tree.Line

/-! Subprescription for the **one diagnostic**. Not a definition of full MS.
 Position-normalization units as tree.continued. Rows after transverse curl symbol.
 Color is factored out. Patch variables u in this file is HAT RADIUS square.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.Triad
open Function Set Filter MSbar MSbar.Symbol MeasureTheory Metric Complex DR Maxwell Pert.Triangle
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

/-- κ^ε = MSbar momentum measure supplement (μbar=1). At vertex use its inverse. -/
def kappa : ℝ := Real.exp Real.eulerMascheroniConstant / (4*Real.pi)
def each (s:ℂ):ℂ:= (↑kappa:ℂ)^(-s)
def vert (s:ℂ):ℂ:= (↑kappa:ℂ)^s

lemma kappa_pos : 0<kappa:= by unfold kappa; positivity
lemma vert_analytic : Differentiable ℂ vert := fun _=> differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast kappa_pos.ne'))
lemma each_analytic : Differentiable ℂ each := fun _=> differentiableAt_id.neg.const_cpow (Or.inl (by exact_mod_cast kappa_pos.ne'))

lemma line_units (s:ℂ): each s*vert s=1:= by
    unfold each vert; rw [←cpow_add _ _ (by exact_mod_cast kappa_pos.ne'),neg_add_cancel,cpow_zero]

/-- Independent d-dimensional position Green (offsite), colors multiplied later. Landau curl
 accepted position rule is tree.continued (no proof of FT in this project). Kept complex.
-/
def porter (s:ℂ) := each s * Complex.Gamma (1+s)/(4*(↑Real.pi:ℂ)^(2+s))
def bridge (s:ℂ) (v:E4)(u:ℝ):= porter s * (↑(‖v‖^2+u):ℂ)^(-1-s)

-- analytic off collisions at positive squared total radius. u=hat squared, admitting
-- extensions smooth a little to either side. Use vectors real for test evaluation only.
lemma port_diff {s:ℂ}(h:s∈neighborhood):DifferentiableAt ℂ porter s:= by
    have hs : 0<(1+s).re:= by
      have ht: ‖s‖ < 1/8:= by simpa [neighborhood] using h
      have he:= abs_re_le_norm s; rw [abs_le] at he; simp; linarith [he.1]
    have hh := (Complex.differentiableAt_Gamma (1+s) fun n e=> by rw [e] at hs; simp at hs; linarith [Nat.cast_nonneg (α:=ℝ) n]).comp s ((differentiableAt_id (x:=s)).const_add 1)
    have hp : (↑Real.pi:ℂ)≠0:= ofReal_ne_zero.mpr Real.pi_ne_zero
    exact ((each_analytic s).mul hh).div (((differentiableAt_id.const_add _).const_cpow (Or.inl hp)).const_mul _) (mul_ne_zero (by norm_num) (cpow_ne_zero_iff.mpr (Or.inl hp)))
lemma port_ok {z:ℂ}(hz:z∈neighborhood):ContDiffAt ℝ ∞ porter z:=
   (((DifferentiableOn.analyticOnNhd (fun _ hz=>(port_diff hz).differentiableWithinAt) opened) z hz).restrictScalars).contDiffAt
lemma bridge_ok {s:ℂ} (hs:s∈neighborhood) {p:Patch} (hp: 0<‖p.1‖^2+p.2) :
    ContDiffAt ℝ ∞ (uncurry fun z (p:Patch)=> bridge z p.1 p.2) (s,p) := by
    have hh : ContDiffAt ℝ ∞ (fun p : ℂ×Patch=> ‖p.2.1‖^2+p.2.2) (s,p) :=
        ((contDiff_norm_sq ℝ).contDiffAt.comp _ (contDiffAt_fst.comp _ contDiffAt_snd)).add (contDiffAt_snd.comp _ contDiffAt_snd)
    let q(v:ℂ × Patch):ℂ := -(1:ℂ)-v.1
    have he : ContDiffAt ℝ ∞ (fun v : ℂ × Patch=> (↑(‖v.2.1‖^2+v.2.2):ℂ)^(q v)) (s,p) := by
       let Z:ℂ × ℂ:= (↑(‖p.1‖^2+p.2),q (s,p)); have hz : Z.1∈ slitPlane:= ofReal_mem_slitPlane.mpr hp
       have hb : AnalyticAt ℂ (fun p : ℂ × ℂ=> p.1^p.2) Z := by
          have hc : AnalyticAt ℂ Complex.log Z.1 := DifferentiableOn.analyticAt (s:=slitPlane) (fun _ hw=> (Complex.differentiableAt_log hw).differentiableWithinAt) (isOpen_slitPlane.mem_nhds hz)
          have hy : AnalyticAt ℂ (fun p : ℂ × ℂ=> Complex.log p.1*p.2) Z:= (hc.comp (f:=Prod.fst) analyticAt_fst).mul analyticAt_snd
          apply ((Complex.differentiable_exp.analyticAt _).comp hy).congr
          filter_upwards [continuousAt_fst.eventually_ne (show Z.1≠0 from ofReal_ne_zero.mpr hp.ne')] with x hx; exact (cpow_def_of_ne_zero hx _).symm
       exact ((show AnalyticAt ℝ _ _ from hb.restrictScalars).contDiffAt).comp (f:=fun p:ℂ×Patch=> ((↑(‖p.2.1‖^2+p.2.2):ℂ),q p)) (s,p) ((ofRealCLM.contDiff.contDiffAt.comp _ hh).prodMk (contDiffAt_const.sub contDiffAt_fst)) -- check
    exact ((port_ok hs).comp _ contDiffAt_fst).mul he
lemma bridge_color {s:ℂ} (hs:s∈neighborhood) {p:Patch}(hp:0<‖p.1‖^2+p.2): DifferentiableAt ℂ (fun z=>bridge z p.1 p.2) s :=
   (port_diff hs).mul (((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl (ofReal_ne_zero.mpr hp.ne')))

lemma bridge_agrees (s:ℝ) (v:E4) (ht:v≠0) : bridge s v 0= ↑(Tree.continued 1 (-s) v) := by
    have hh := Real.pi_pos
    unfold bridge porter Tree.continued Tree.volumeFactor each kappa
    rw [show 1- -s=1+s by ring]
    simp only [sub_neg_eq_add,mul_assoc, add_zero,one_pow,mul_one]
    have hpi (a b:ℝ) (ha:0≤a): (↑(a^b):ℂ)=(↑a:ℂ)^(↑b:ℂ):= ofReal_cpow ha b
    push_cast
    rw [hpi (Real.exp Real.eulerMascheroniConstant / (4*Real.pi)) _ kappa_pos.le, hpi _ _ hh.le,hpi _ _ (pow_pos (norm_pos_iff.mpr ht) _).le, ← Gamma_ofReal]
    push_cast
    rw [show -(s:ℂ)-1=-1- (s:ℂ) by ring]; ring

variable (s : ℂ) (h : Bool) (i : Fin 3) (μ a : Axis)

-- Actual vertex A_mu(w) to F^sign insertion. The argument displacement v=w-mark,
-- first derivative opposite sign at mark. Hats u squared.

def base (s:ℂ)(b:Axis)(v:E4)(u:ℝ) : ℂ := -(grad b (fun v=>bridge s v u) v)
def lane (s:ℂ)(h:Bool)(i:Fin 3)(μ:Axis)(v:E4)(u:ℝ) : ℂ := ∑ b:Axis, (↑(fan h i b μ):ℂ) * base s b v u

def bar (s:ℂ)(h:Bool)(i:Fin 3)(a μ:Axis)(v:E4)(u:ℝ) : ℂ:= grad a (fun v=> lane s h i μ v u) v

end YM.SchemeConversionRG11.FirstMS.Triad
