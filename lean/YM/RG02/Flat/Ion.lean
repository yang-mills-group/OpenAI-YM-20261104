import YM.RG02.Flat.Collar
import YM.RG02.Wick.Program

/-!
# Same-mark numerator, unmasked analytic packet interior

Phase 1 before regrouping for masks. No sampling another B or f; no action
on the orbit regulator! Calculate the analytic projection by carrying unmarked
and disconnected values as well: in relative log chart, Haar ratio anchored 1
and unnormalized constant kept in `primary`; noise denominator kept aside to
multiply on a comparison of the unnormalized push (normalization affects even
coarse field-independent scalar).
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG02.Fk
open Filter Function MeasureTheory Set Metric Lattice Exterior Tree Wilson RG Precision Supply Bid Marker Extra.Trajectories
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Therm Asym Tangent Grade
open scoped ContDiff Topology Matrix.Norms.Frobenius BigOperators Classical Pointwise
variable {G : Gauge}{I : Type} [DecidableEq I] [Fintype I]{B : Census I}{c f : Side}{S : StepData c f}

/-- t-rescaled analytic numerator WITHOUT probability for choice i,
level scalar, or per-bond noise normalizer. Sign `-`, corporeal
loop weight lives in field. At t=actual g may be compared on flags=empty
and `Inspected`. -/
def ion (i : S.Choices)(p : Clip)(R : PathData G)(x : Dir G c)(A : Space G f→ℝ)
    (d : ℕ)(W : Space G f→ Poly B)(t : ℝ)(u : Config G f) :=
   let z := (t,u)
   (Complex.ofReal (Real.exp (- field i p R x A z/t^2))) • Poly.pass (((t:ℂ) ^ d)⁻¹ • W z)

lemma ion_volume (i : S.Choices) {p R σ C Λ}(H : R.Bounds p σ C Λ)(h : S.patch.Branches S.kernel G) (x : Dir G c) {A : Space G f→ℝ}(hA : Ambient A)
    {d : ℕ}{W : Space G f→Poly B}(hW : Ink d W) (t : ℝ) (s : B.Mode) : Volume.Fundamental (g:=S.ratio) (fun u : Config G f=> (ion i p R x A d W t u).part s) := by
   have hf k (hk: ∀ x,k (S.ratio.embed x)=1) u : field i p R x A (t,Lattice.gauge k u)=field i p R x A (t,u) := by
      simp only [field, Work.F05.mainTerm_gauge H, Work.F05.root_noise h _ _ k hk, Work.F05.loop_gauge H]
      rw [show A (t,gauge k u)=_ from hA.calm t k u]
   intro k hk u; dsimp only [ion]; rw [hf k hk, show W (t,gauge k u)=_ from hW.calm t k u]

lemma ion_meas (i : S.Choices) {p R σ C Λ}(H : R.Bounds p σ C Λ)(h : S.patch.Branches S.kernel G)(x : Dir G c){A : Space G f→ℝ}(hA : Ambient A)
    {d : ℕ}{W : Space G f→Poly B}(hW : Ink d W) (t : ℝ) (s : B.Mode) : Measurable (fun u => (ion i p R x A d W t u).part s) := by
   let Z := fun u : Config G f => (t,u)
   have he : Measurable Z := measurable_const.prodMk measurable_id
   have hg : Measurable (W ∘ Z) := by
      have hP := (measurable_pi_lambda W hW.borel).comp he
      change @Measurable _ _ _ (borel (B.Mode→ℂ)) _; rwa [← BorelSpace.measurable_eq]
   unfold ion; simp_rw [Poly.part_smul];
   refine (Complex.continuous_ofReal.measurable.comp (((field_meas i x h H hA.borel|>.comp he).neg.div_const _).exp)).mul ?_
   exact (Poly.part_cont s).measurable.comp (Poly.pass_cont.measurable.comp ((show Continuous (fun z:Poly B => (((t:ℂ)^d)⁻¹:ℂ) • z) by fun_prop).measurable.comp hg))

variable (T : Forest S.ratio)

def motion (x : Dir G c)(t : ℝ) : T.Slice G := fun i => replica S.ratio (represent (t • x)) i

lemma motion_zero (x : Dir G c) : motion T x 0=1 := by funext i; simp [motion]
lemma motion_tends (x : Dir G c) : Tendsto (motion T x) Tested.germ (𝓝 1) := by
   rw [← motion_zero T x]; apply Tendsto.mono_left _ nhdsWithin_le_nhds
   apply Continuous.tendsto
   apply continuous_pi; intro i; unfold motion replica; split
   · exact continuous_const
   exact (continuous_apply ..).comp (represent_cont.comp (continuous_id.smul (continuous_const (y:=x))))

/-- Chart dimensional cost separately. -/
def weight (T : Forest S.ratio)(η : ChartRatio G) := η.scale^(Fintype.card T.Free)

def dim (T : Forest S.ratio)(G : Gauge) := Module.finrank ℝ (AxisChart G T)

lemma dragged (x : Dir G c)(w : AxisChart G T)(t : ℝ) :
   (t,T.drape (Volume.coordinate T (motion T x t) w))=Pins.visits T x (t,w) := rfl

lemma ion_flex (i : S.Choices)(p : Clip)(R : PathData G)(x y : Dir G c) (A:Space G f→ℝ)(d : ℕ) (W : Space G f→Poly B)
    (s : B.Mode) {η : ChartRatio G} (H : LocalRatio η) (t : ℝ)(ht : 0 < t) {e : ℝ}(hE:e≤ Chart.small G η) (u : AxisChart G T) (hx:u∈disc t e) :
   Volume.penalty T η (motion T y t) (fun a : T.Slice G => (ion i p R x A d W t (T.drape a)).part s) (t • u) =
     ↑(weight T η)*lit (flex T i η p R x y A) d (Pins.ink T y W) s t u := by
   let f' := field i p R x A; let E := flex T i η p R x y A; let M := motion T y t; let v := Pins.visits T y (t,t•u)
   have hv := Volume.jacob (F:=T) η (t • u) hx H hE
   have hg : turbine E t u = axisJ T η (t • u)*Real.exp (-f' v/t^2) := by
      unfold turbine E flex; have hp := v
      rw [← Real.exp_log hv.2, ← Real.exp_add]; simp only [Real.log_exp]; congr 1
      change -(f' v-t^2*_)/t^2=_; field_simp
      ring
   dsimp only [Volume.penalty, ion]
   rw [dragged, hv.1]; unfold lit
   change (_ : ℝ) • (_ : ℂ) = ↑(weight T η)*(_ * ↑(turbine E t u))
   rw [hg,Poly.part_smul,Complex.real_smul]
   simp only [Complex.ofReal_mul, Therm.pins, Function.comp_apply,Pins.ink,weight,v,f']; ring

lemma ion_link (i : S.Choices)(p : Clip)(R : PathData G)(x : Dir G c) (A:Space G f→ℝ)(d : ℕ) (W : Space G f→Poly B)
    (s : B.Mode) {η : ChartRatio G} (H : LocalRatio η) (t : ℝ)(ht : 0 < t) {e : ℝ}(hE:e≤ Chart.small G η) (u : AxisChart G T) (hx:u∈disc t e) :
   Volume.penalty T η (motion T x t) (fun a : T.Slice G => (ion i p R x A d W t (T.drape a)).part s) (t • u) =
     ↑(weight T η)*lit (track T i η p R x A) d (Pins.ink T x W) s t u :=
    ion_flex T i p R x x A d W s H t ht hE u hx

end YM.RG02.Fk
