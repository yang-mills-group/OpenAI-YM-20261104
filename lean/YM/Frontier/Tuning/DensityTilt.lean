import YM.Frontier.Tuning.HeldBurst
import YM.Frontier.Tuning.MarginalPrice
/-! Unit contour-ratio estimate within the actual support curvature, before doing
the exact change of variables or passing derivatives through integrals. Only a Sweep on
the real part will be used for large-field events. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier.Tuning.DensityTilt
open Footage HeldBurst
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Blaze Silica Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Clutch Matter PhysicalNext.Repeat.Alabaster PhysicalNext.Repeat.Height Held ClockShift TwoMotion AngularReceipt Flux Shield Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R A : Rep G f} {X : Coat T F} {x :Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {z:E}
variable {H0 a C α Z β γ d η ε σ W s b μ r p q v : ℝ} {j n l : ℕ} {Q : ConnectedActivityE6.Target G P}
variable {o : Target.Order G W}
variable {χ:Chi}
local notation "b₁" => betaF G s L
local notation "M₀" => radiusB s
set_option maxRecDepth 8192
set_option pp.proofs false
set_option maxHeartbeats 1200000



local notation "g₀" => grow G L s
-- Notice no extra subtraction at V=x in the phase cost; the certified tilt
-- is exact real replacement / old Gaussian likelihood (old real scalp includes
-- Radon-Nikodym ratio). There is no full-complement inverse release here.
def phasePoly (τ:ℂ) (R:Rep G f)(X:Coat T F)(J:Finset (Bond f))(A:ℝ)(V:Config G c)(z:Air f G) :=
    let K:=lensS J G
    Complex.exp ((K.card:ℂ)/2*(Complex.log τ-Complex.log R.beta)+(1-τ/R.beta)*draftI X J R.beta A V z)
def scTilt (X:Coat T F) (τ:ℂ) (R:Rep G f) (J:Finset (Bond f))(A:ℝ)(V:Config G c)(z:Air f G):ℂ:= phasePoly τ R X J A V z*Complex.ofReal (scalp J X V R.beta A z)
abbrev tiltScale (j:ℕ)(e D D' :ℝ):=1+|D| +(1+j.factorial*e)*(1+4* |D'|)
abbrev airMark (G:Gauge)(J:Finset (Bond f)) := GaussContour.markup (↥(lensS J G))

variable {τ:ℂ}
lemma cast_phase (hR:R.beta=τ.re)(hβ : 0<τ.re)(v:ℝ)(J:Finset (Bond f)) :
  ‖Complex.exp ((lensS J G).card/2*(Complex.log τ-Complex.log R.beta)+(1-τ/R.beta)*(v:ℂ))‖ = GaussContour.markup (↥(lensS J G)) τ:=by
   have he : (τ/(R.beta:ℂ)).re=1:=by rw [hR, Complex.div_ofReal_re,div_self hβ.ne']
   have hZ : ‖τ‖ ≠ 0:= ((le_abs_self τ.re).trans_lt' hβ).trans_le (Complex.abs_re_le_norm τ) |>.ne'
   rw [Complex.norm_exp,GaussContour.markup,Real.log_div hZ hβ.ne',← hR]; rw [Fintype.card_coe]
   apply congr_arg Real.exp
   rw [Complex.add_re,Complex.mul_re,Complex.mul_re]
   rw [Complex.sub_re,Complex.sub_re,he,hR]; norm_num only [Complex.one_re,Complex.ofReal_im, mul_zero,sub_zero,sub_self,zero_mul,add_zero, Complex.log_re,Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ]
   rw [← show (Complex.ofReal ((lensS J G).card/2:ℝ))=(lensS J G).card/2 by push_cast;rfl]
   simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option quotPrecheck false

lemma air_phase {ε:ℝ}(τ:ℂ)(R:Rep G f) (X:Coat T F)(V:E→ Config G c)(z:Air f G)(y:E)(J:Finset (Bond f))(e : ℝ)
   (hC : 0≤ε)(hp:∀ u:ℂ, Brush j (ε*‖Complex.exp u‖) 1 Complex.exp u)(hR:R.beta=τ.re)(hβ : 0<τ.re)(h': ‖τ/R.beta‖≤3)
   (h:Brush j Z 1 (fun i=> draftI X J R.beta e (V i) z) y) :
    Brush j (airMark G J τ) ((1+j.factorial*ε)*(1+4*Z)) (fun i:E=> phasePoly τ R X J e (V i) z) y:=by
      let v := (1-τ/R.beta:ℂ); let f i:= v*Complex.ofReal (draftI X J R.beta e (V i) z); let J0:=(lensS J G).card
      have hv : ‖v‖ ≤ 4:= by apply (norm_sub_le (E:=ℂ) ..).trans; rw [norm_one]; linarith
      have hφ : ‖Complex.exp (f y)‖ ≤ 1:= by rw [Complex.norm_exp]; apply Real.exp_le_one_iff.mpr; unfold f v; rw [hR,Complex.mul_re,Complex.sub_re,Complex.one_re,Complex.div_ofReal_re, div_self hβ.ne', sub_self,zero_mul,Complex.ofReal_im,mul_zero,sub_self]
      have hZ:=h.nonneg; have ht := ComplexBrush.cast_scale v h; have hh:= (ComplexBrush.exp_lift j hp ht hφ hC).climb (le_refl _) (le_trans (c:=(1+j.factorial*ε)*(1+4*Z)) (by rw [mul_one];gcongr) le_rfl)
      let m:=(J0/2:ℂ)*(Complex.log τ-Complex.log R.beta)
      have hem: ‖Complex.exp m‖= airMark G J τ:= by unfold airMark; rw [← cast_phase hR hβ 0]; simp only [Complex.ofReal_zero,mul_zero,add_zero];rfl
      rw [← hem]; refine (ComplexBrush.smul_left (Complex.exp m) hh).shimmy (Filter.Eventually.of_forall fun i=>?I) |>.climb (by simp) le_rfl
      unfold phasePoly; dsimp only; exact Complex.exp_add ..
end YM.Frontier.Tuning.DensityTilt
