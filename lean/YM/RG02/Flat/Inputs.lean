import YM.RG02.Flat.Precision
import YM.RG02.Limit.Load
import YM.Work.G05.Taylor

/-!
# Local analytic input in the raw-link convention

One finite period, coarse-to-fine block geometry. Additive vacuum action
extra stipulated through internal order, represented here by a smooth
unmasked extension, beginning at fluctuation order **three**, measured on
raw-link Taylor coefficients (scaled by t² for `Ambient`). Could have, e.g.,
additional finite nonnegative coefficients in t carried along from prespecified
path lift/helicity calculations using four primitives; no off-mask estimate
assumed. This does NOT put a power or Laurent series into the hypothesis
about inherited E/k. Marked data similarly encoded, but may have arbitrary
fixed inverse powers (bounded by mark horizon valuations, test/scale data to
be kept by producer). Unmask with true paths footprint before all these
coefficient tests. Render into Bands separately (RG03).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Fk
open Filter Function Lattice Wilson RG Precision Tree Supply Bid Marker PertExtension PertExtension.Series
open scoped Topology Classical Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge}{I : Type}[DecidableEq I]{B : Census I}{n c f : Side}

abbrev Space (G : Gauge)(n : Side) := ℝ × Config G n
abbrev Raw (G : Gauge)(n : Side) := ℝ × Dir G n
def fills (z : Raw G n) : Space G n:= (z.1, represent z.2)

section vanish
variable {X Y Z : Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y]
variable [NormedAddCommGroup Z][NormedSpace ℝ Z]

/-- Real-order valuation on the rescaled action. No invisible pole at a
finite-power parameter monomial. -/
def Begins (d : ℕ)(f : X→Y) := ∀ k<d,iteratedFDeriv ℝ k f 0=0

lemma begins_zero (d : ℕ) : Begins d (fun _ : X => (0:Y)) := by
   intro k _; ext x; cases k with
   | zero => simp
   | succ k => rw [iteratedFDeriv_succ_apply_right]; simp

namespace Begins
variable {f : X→Y}{d : ℕ}
lemma after (h : Begins d f){φ : Z→X}(hv : φ 0=0)(H : ContDiffAt ℝ ∞ φ 0)(hf : ContDiffAt ℝ ∞ f 0) :
   Begins d (f ∘ φ) := by
   intro i hi
   have he := Work.G05.jets_comp (g:=f) (g':= fun _ => 0) (d:=i) (H.of_le (by exact WithTop.coe_le_coe.mpr le_top)) (H.of_le (by exact WithTop.coe_le_coe.mpr le_top)) (by rw [hv]; exact hf.of_le (by exact WithTop.coe_le_coe.mpr le_top)) contDiffAt_const rfl (fun _ _ => rfl) (fun k hk=> by rw [hv,h k (by omega)]; exact ((begins_zero d : Begins d (fun _ : X => (0:Y))) k (by omega)).symm) i le_rfl
   exact he.trans (begins_zero d i hi)
lemma follows (h : Begins d f)(ha : ContDiffAt ℝ ∞ f 0){L : Y →L[ℝ] Z} : Begins d (L ∘ f) := by
   by_cases ht : 0 < d; swap; · intro k hk; omega
   have hf : f 0=0 := by
      rw [← iteratedFDeriv_zero_apply (𝕜:=ℝ) (f:=f) (x:=0) (m:=fun _=>0),h _ ht]; rfl
   intro k hk
   have hh : ContDiffAt ℝ k f 0 := ha.of_le (by exact WithTop.coe_le_coe.mpr le_top)
   have he := Work.G05.jets_comp (f':=fun _ : X=>0) hh contDiffAt_const L.contDiff.contDiffAt L.contDiff.contDiffAt hf (fun i hi => by rw [h i (by omega),begins_zero d i (by omega)]) (fun _ _ => rfl) k le_rfl
   rw [show L ∘ (fun _ : X=>0)=(fun _=>0) by funext t; simp] at he
   exact he.trans (begins_zero d k hk)
end Begins
lemma pens (d : ℕ)(f:X→ℂ)(u:X)[FiniteDimensional ℝ X](h : Begins d f)(H : ContDiffAt ℝ ∞ f 0)(i : ℕ)(hi : i<d) :
    PowerSeries.coeff i (Asym.ribbon f u)=0 := by
   have he : Begins d (Complex.re ∘ f) := Begins.follows h H (L:=Complex.reCLM)
   have hw : Begins d (Complex.im ∘ f) := Begins.follows h H (L:=Complex.imCLM)
   rw [Asym.ribbon_coeff,Radial.jet,Radial.jet];
   simp only [show (fun i => (f i).re)=Complex.re ∘ f from rfl,show (fun i => (f i).im)=Complex.im ∘ f from rfl,he i hi,hw i hi,_root_.zero_apply,mul_zero,Complex.ofReal_zero,add_zero]
end vanish

structure Ambient (A : Space G n → ℝ) : Prop where
   borel : Measurable A
   calm : ∀ t, GaugeInvariant (fun U => A (t,U))
   smooth : ContDiffAt ℝ ∞ (A ∘ fills) 0
   born : Begins 5 (A ∘ fills)

structure Ink (m : ℕ)(W : Space G n→ Poly B) : Prop where
   silent x : (W x).part B.quiet=0
   borel s : Measurable fun x => (W x).part s
   calm : ∀ t,GaugeInvariant fun U=> W (t,U)
   smooth s : ContDiffAt ℝ ∞ (fun x => (W (fills x)).part s) 0
   prices s : Begins m (fun x => (W (fills x)).part s)

variable {S : StepData c f}

namespace Pins
open Work.F03 Tangent
variable (F : Forest S.ratio)(B : Dir G c)

/-- Relative to the ACTUAL replica. -/
def visits (z : ℝ×AxisChart G F) : Space G f := (z.1,live F (shift F B z))
def ink {I:Type}[DecidableEq I]{N:Census I}(W : Space G f→ Poly N) := W ∘ visits F B

lemma visits_home : visits F B 0=(0,1) := by unfold visits;rw [map_zero,live_zero]; rfl
@[fun_prop] lemma visit_motion : Continuous (visits F B) := continuous_fst.prodMk ((Work.F04.lifting_cont F).comp (shift F B).continuous)

private def proposed (z : ℝ × AxisChart G F) := (z.1, axisLog F (shift F B z))
private theorem gauges : fills ∘ proposed F B =ᶠ[𝓝 0] visits F B := by
    filter_upwards [(by simpa using (shift F B).continuous.tendsto 0 : Tendsto (shift F B) (𝓝 0) (𝓝 0)).eventually (Work.F03.inclusion_works F (G:=G))] with t ht; exact Prod.ext rfl ht
private lemma proposed_jet : ContDiffAt ℝ ω (proposed F B) 0 := by
    have h := show ContDiffAt ℝ ω (axisLog F) (shift F B 0) from (by rw [map_zero]; exact (inclusion_smooth F).snd)
    apply ContDiffAt.prodMk contDiffAt_fst
    exact h.comp (f:=shift F B) 0 (shift F B).contDiff.contDiffAt
private lemma proposed_zero : proposed F B 0=0 := Prod.ext rfl (show axisLog F (shift F B 0)=0 from by rw [map_zero]; exact congr_arg Prod.snd (inclusion_zero F))

lemma admission {X : Type}[NormedAddCommGroup X][NormedSpace ℝ X]{f' : Space G f → X}{d : ℕ}
    (h : ContDiffAt ℝ ∞ (f' ∘ fills) 0)(H : Begins d (f' ∘ fills)) :
    ContDiffAt ℝ ∞ (f' ∘ visits F B) 0 ∧ Begins d (f' ∘ visits F B) := by
   have he : (f' ∘ fills) ∘ proposed F B =ᶠ[𝓝 0] f' ∘ visits F B := (gauges F B).fun_comp f'
   have hg : ContDiffAt ℝ ∞ (proposed F B) 0 := (proposed_jet F B).of_le le_top
   refine ⟨((proposed_zero F B).symm ▸ h : ContDiffAt ℝ ∞ _ (proposed F B 0)).comp 0 hg|>.congr_of_eventuallyEq he.symm,?_⟩
   exact fun i hi => ((he.iteratedFDeriv ℝ i).self_of_nhds).symm.trans ((H.after (proposed_zero F B) hg h) i hi)

lemma jobs {N : Census I}{m : ℕ}{W : Space G f→ Poly N}(h : Ink m W) : Therm.Loads m (ink F B W) := by
   have hh (s:N.Mode) := admission F B (f':=fun x=> (W x).part s) (h.smooth s) (h.prices s)
   exact ⟨fun _=> h.silent _, fun i => (hh i).1,fun s x i hi => pens m _ _ (hh s).2 (hh s).1 i hi⟩
lemma design {A : Space G f→ℝ}(h : Ambient A) :
    ContDiffAt ℝ ∞ (A ∘ visits F B) 0 ∧ ∀ k ≤ 4, ∀ x, Radial.jet (A∘ visits F B) k x=0 := by
   obtain ⟨ha,hp⟩ := admission F B h.smooth h.born
   refine ⟨ha,fun k hk x => ?_⟩
   simp only [Radial.jet,hp k (by omega),_root_.zero_apply,mul_zero]

end Pins
end YM.RG02.Fk
