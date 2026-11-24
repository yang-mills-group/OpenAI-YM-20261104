import YM.Integration.NativeWilsonPlaquetteInvoice
import YM.Integration.WilsonPlaquetteMoments
import YM.Integration.WilsonLimitConstruction.FundedOriginalRun
import YM.IterationFour.Running

/-! Uniform transfer of the actual local Wilson Taylor remainder and its
physical directional derivatives against jointly measured original tagged fields. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.NativeWilsonTaggedRemainder
open Filter Function MeasureTheory Lattice Wilson Precision RG Work WilsonStartup OPE.Therm
open PhysicalNext.Repeat.Legato WilsonLimitConstruction Push.GridApprox
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge}

private theorem payment {C : Family G} (hC : C.Makes) (N p i : ℕ) (hi : i≤N) (k : ℕ) (s : ℝ) :
    (C.path.β N p i * (Pert.Asymptotics.regulatorRun C N p i)^k) *
      (C.path.levels.clock.hatCoupling i)^s ≤
    (4*(2:ℝ)^k) * (C.path.levels.clock.hatCoupling i)^((k:ℝ)+s-2) := by
  let x := C.path.levels.clock.hatCoupling i
  let b := C.path.levels.clock.hatBeta i
  let g := Pert.Asymptotics.regulatorRun C N p i
  have hb : 0<b := zero_lt_one.trans (C.path.levels.fits.delayed i)
  have hx : 0<x := inv_pos.mpr (Real.sqrt_pos.mpr hb)
  have hg : 0<g := IterationFour.Currency.g_pos hC N p i hi
  have hb' : C.path.β N p i ≤ 4*b := (IterationFour.Currency.actual_band hC N p i hi).2
  have hg' : g ≤ 2*x := (IterationFour.Currency.hat_g hC N p i hi).2
  have hs : x^k * x^s = x^((k:ℝ)+s) := by rw [Real.rpow_add hx,Real.rpow_natCast]
  have he : b*x^((k:ℝ)+s) = x^((k:ℝ)+s-2) :=
    IterationFour.Currency.beta_payment C.path.levels i ((k:ℝ)+s)
  calc
    _ ≤ (4*b*(2*x)^k)*x^s := mul_le_mul_of_nonneg_right
      (mul_le_mul hb' (pow_le_pow_left₀ hg.le hg' _) (pow_nonneg hg.le _) (by positivity)) (Real.rpow_nonneg hx.le _)
    _ = (4*(2:ℝ)^k)*(b*(x^k*x^s)) := by rw [mul_pow]; ring
    _ = _ := by rw [hs,he]

private theorem measurable_jet {n : Side} (J k : ℕ) (p : Cell n)
    (a : Config G n → Fin k → Directions G n) (ha : Measurable a) :
    Measurable (fun U : Config G n => leftDerivs (leftOver J p) (List.ofFn (a U)) U) := by
  let v (U : Config G n) (i : Fin k) := a U i ∘ edges p
  have hv : Measurable v := measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
    ((measurable_pi_apply _).comp ((measurable_pi_apply i).comp ha))
  have hmat : Continuous (fun U : Config G n => Quad.mat (U ∘ edges p)) :=
    continuous_pi fun j => G.continuous_mat.comp (continuous_apply (edges p j))
  have hH : Continuous (fun y : Config G n × (Fin k → Quad.Dir G) =>
      Quad.strokes J (List.ofFn y.2) (Quad.mat (y.1 ∘ edges p))) :=
    (Quad.strokes_diff J (G:=G) k).continuous.comp (continuous_snd.prodMk (hmat.comp continuous_fst))
  have h := hH.measurable.comp (f:=fun U => (U,v U)) (measurable_id.prodMk hv)
  convert h using 1
  funext U
  rw [leftOver_jet]
  exact congrArg (fun l => Quad.strokes J l (Quad.mat (U ∘ edges p)))
    (List.map_ofFn (g:=fun y => y ∘ edges p) (f:=a U))

/-- The true inverse-coupling weighted directional derivative integrand,
with engineering factor g^k and an arbitrary signed fine observable. -/
def charge {n : Side} (r k : ℕ) (z : Cell n) (β g : ℝ)
    (a : Config G n → Fin k → Directions G n) (φ : Config G n → ℂ) (U : Config G n) : ℂ :=
  (↑(β*g^k*leftDerivs (leftOver (r+2) z) (List.ofFn (a U)) U) : ℂ) * φ U

/-- The constants and scale threshold precede every volume, period, cell, original configuration,
unit variation, bounded fine observable and unit coarse Borel test. The field directions may
depend measurably on the actual fine background. -/
theorem tested {C : Family G} (hC : C.Makes) (poem : Poetry C.path.levels) (hG : G.Simple)
    (r k : ℕ) (hk : k≤r+3) {η : ℝ} (hη : 0<η) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ m : ℕ in atTop, ∀ N, m<N → ∀ p,
    ∀ (z : Cell (C.side (m+1) p)) (M : ℝ), 0≤M →
    ∀ (a : Config G (C.side (m+1) p) → Fin k → Directions G (C.side (m+1) p)), Measurable a →
      (∀ U i j, ‖a U i (edges z j)‖ ≤ 1) →
    ∀ (φ : Config G (C.side (m+1) p) → ℂ), Measurable φ → (∀ U, ‖φ U‖ ≤ M) →
    ∀ (ζ : Config G (C.side m p) → ℂ), Measurable ζ → (∀ W, ‖ζ W‖ ≤ 1) →
    ‖∫ W, actualAverage C (N:=N) (charge r k z (C.path.β N p (m+1))
      (Pert.Asymptotics.regulatorRun C N p (m+1)) a φ) W * ζ W ∂scene C.path N p m‖ ≤
        M*K*(C.path.levels.clock.hatCoupling (m+1))^((r:ℝ)+1-η) := by
  let q := r+3-k
  let s : ℝ := (q:ℝ)-η
  have hq : (k:ℝ)+s-2 = (r:ℝ)+1-η := by
    dsimp [s,q]; rw [Nat.cast_sub hk]; push_cast; ring
  have hs : s<q := sub_lt_self _ hη
  obtain ⟨A,hA,face⟩ := NativeWilsonPlaquetteInvoice.face G (r+2) k
  refine ⟨A*(1+2^q)*(4*(2:ℝ)^k),by positivity,?_⟩
  filter_upwards [WilsonPlaquetteMoments.tested hC poem hG q hs] with m h
  intro N hN p z M hM a ha hdir φ hφ hbound ζ hζ hζ'
  let β := C.path.β N p (m+1)
  let g := Pert.Asymptotics.regulatorRun C N p (m+1)
  let x := C.path.levels.clock.hatCoupling (m+1)
  have hg : 0<g := IterationFour.Currency.g_pos hC N p (m+1) hN
  have hb : 0<β := IterationFour.Currency.stripe_pos (zero_lt_one.trans (C.path.levels.fits.delayed (m+1)))
    (IterationFour.Currency.actual_band hC N p (m+1) hN)
  have hf : Measurable (charge r k z β g a φ) :=
    (Complex.continuous_ofReal.measurable.comp
      (measurable_const.mul (measurable_jet (r+2) k z a ha))).mul hφ
  have hprice (U : Config G (C.side (m+1) p)) :
      ‖charge r k z β g a φ U‖ ≤ (M*(β*g^k)*A)*(G.chord (faceValue U z))^q := by
    have step := face (C.side (m+1) p) z U (a U) (hdir U)
    simp only [charge,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ (β*g^k)*(A*(G.chord (faceValue U z))^q)*M := by
        rw [abs_of_nonneg hb.le,abs_of_nonneg (pow_nonneg hg.le _)]
        exact mul_le_mul (mul_le_mul_of_nonneg_left step (mul_nonneg hb.le (pow_nonneg hg.le _)))
          (hbound U) (norm_nonneg _) (mul_nonneg (mul_nonneg hb.le (pow_nonneg hg.le _))
            (mul_nonneg hA.le (pow_nonneg (G.chord_nonneg _) _)))
      _ = _ := by ring
  have measure := h N hN p z (M*(β*g^k)*A) (by positivity)
    (charge r k z β g a φ) hf hprice ζ hζ hζ'
  have paid := payment hC N p (m+1) hN k s
  rw [hq] at paid
  calc
    _ ≤ (M*(β*g^k)*A)*((1+2^q)*x^s) := measure
    _ = M*(A*(1+2^q))*((β*g^k)*x^s) := by ring
    _ ≤ M*(A*(1+2^q))*((4*(2:ℝ)^k)*x^((r:ℝ)+1-η)) :=
      mul_le_mul_of_nonneg_left paid (by positivity)
    _ = _ := by ring

end YM.Integration.NativeWilsonTaggedRemainder
end
