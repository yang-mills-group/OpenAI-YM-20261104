import YM.RG02.Flat.Inputs
import YM.PertExtension.BareChart
import YM.Progress.STATIONARY_SCENES.Thermal

/-!
# Identify the parameter-ray driver

Use actual analytic pieces of all primitives, with no spatial support cut on
the formal Hessian. Mesh Haar factors include `LocalRatio` at the shifted tree
chart. Negative log convention of effective action. HERE no inherited unknown
E (smooth but no parameter estimates assumed) included. Parameter `t` scales
fluctuations and coarse field before any powers are read; t becomes actual
`g_i`, not `g_{i-1}` nor a physical measuring-frame running coupling.
Kernel weights and powers of t still use the *same angle/tag*. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Fk
open Filter Function Lattice Wilson RG Precision Exterior Tree Supply Bid Marker
open MeasureTheory PertExtension PertExtension.Chart PertExtension.Series Therm Tangent Metric
open scoped Topology Classical Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge}{I : Type}[DecidableEq I]{B : Census I}{n c f : Side}{S : StepData c f}

/-- Negative cost convention outside: insert `exp (- field/t²)`; all direction
fields here physical fine links not the chart UCoord. -/
def field (i : S.Choices)(p : Clip)(R : PathData G)(x : Dir G c)(A : Space G f→ℝ)(z : Space G f) :=
   mainTerm p R z.2 + noiseTaylor S (represent (z.1 • x)) z.2 i + A z + z.1^2*(Precision.loop R z.2)

def axisJ (T : Forest S.ratio)(η : ChartRatio G)(v : AxisChart G T) := ∏ i : T.Free, η.J (v i)
/-- Chart is relative, J on that chart. -/
def track (T : Forest S.ratio)(i : S.Choices)(η : ChartRatio G)(p : Clip)(R : PathData G)(x : Dir G c)
    (A : Space G f → ℝ) : ℝ × AxisChart G T → ℝ := fun u =>
    field i p R x A (Pins.visits T x u) - u.1^2*Real.log (axisJ T η u.2)

/-- With a different chosen origin in the slice calculation (the same
replica type). Issue the pre-alignment rays in this convention, still `shift`
the fields relative to gamma. -/
def flex (T : Forest S.ratio)(i : S.Choices)(η : ChartRatio G)(p : Clip)(R : PathData G)(x y : Dir G c)
    (A : Space G f → ℝ) : ℝ × AxisChart G T → ℝ := fun u =>
    field i p R x A (Pins.visits T y u) - u.1^2*Real.log (axisJ T η u.2)

def remainder (T : Forest S.ratio)(η : ChartRatio G)(R : PathData G)(x : Dir G c)(u : ℝ × AxisChart G T) :=
   Precision.loop R (Pins.visits T x u).2 - Real.log (axisJ T η u.2)

lemma enact (T : Forest S.ratio)(i : S.Choices)(η : ChartRatio G)(p : Clip)(R : PathData G)(x : Dir G c)(A : Space G f→ℝ) :
   track T i η p R x A = ray T i p R x + (A ∘ Pins.visits T x) + fun u => u.1^2 * remainder T η R x u := by
   ext u; unfold remainder track field
   simp only [Pi.add_apply,Function.comp_apply,mul_sub]
   rw [← add_sub_assoc]; rfl

lemma represent_cont : Continuous (represent (G:=G) (n:=n)) := by apply continuous_pi; intro i; simp_rw [Work.F03.represent_link]; fun_prop

lemma readSeries {k : ℕ}(U : ℕ→Atom G k) : Measurable (fun x : Config G n => uncut U x) := by
   apply Finset.measurable_fun_sum; intro i _; exact Measurable.tsum fun j => ((U j).unmasked_cont i).measurable
lemma loop_meas (R : PathData G) : Measurable (fun x : Config G n => Precision.loop R x) := by
   unfold Precision.loop Patch.average; refine measurable_const.mul ?_
   exact Finset.measurable_fun_sum _ fun i _=> (readSeries _).comp (continuous_pull ..).measurable
lemma main_meas {p : Clip}{R : PathData G}{σ C Λ : ℝ}(h : R.Bounds p σ C Λ) : Measurable (fun x : Config G n => mainTerm p R x) := by
   have ht : Measurable (fun x : Config G n=> quadratic p R x) := by
      apply Finset.measurable_fun_sum; intro i _
      exact (measurable_const.mul (G.continuous_price.measurable.comp (continuous_travel ..).measurable)).add (((R.ell_meas _ _ _ _ _ h).norm.pow_const 2).div_const _)
   unfold mainTerm Patch.average; refine measurable_const.mul ?_
   exact Finset.measurable_fun_sum _ fun i _=> ((ht.add (readSeries R.cubic)).add (readSeries R.quartic)).comp (continuous_pull ..).measurable
lemma field_meas (i : S.Choices)(x : Dir G c)(hS : S.patch.Branches S.kernel G){p R σ C Λ}
    (h:R.Bounds p σ C Λ) {A : Space G f → ℝ}(H : Measurable A) : Measurable (field i p R x A) := by
   have hm : Measurable (fun u : Space G f=> noiseTaylor S (represent (u.1 • x)) u.2 i) := by
      unfold noiseTaylor; refine measurable_const.mul ?_
      apply Finset.measurable_fun_sum; intro j _; refine G.continuous_price.measurable.comp (Measurable.mul ?_ (((measurable_pi_apply ..).comp (S.prediction_meas hS i)).comp measurable_snd).inv)
      exact (measurable_pi_apply ..).comp (represent_cont.measurable.comp (measurable_fst.smul_const x))
   exact (((main_meas h).comp measurable_snd).add hm|>.add H).add ((measurable_fst.pow_const 2).mul ((loop_meas R).comp measurable_snd))
lemma flex_meas (T : Forest S.ratio)(i : S.Choices)(x y : Dir G c)(hS : S.patch.Branches S.kernel G){p R σ C Λ}
    (h:R.Bounds p σ C Λ){A : Space G f → ℝ}(H : Measurable A){η}(hA:LocalRatio η):
    Measurable (flex T i η p R x y A) := by
   refine ((field_meas i x hS h H).comp (Pins.visit_motion T _).measurable).sub ((measurable_fst.pow_const 2).mul (Real.measurable_log.comp ?_))
   exact Finset.measurable_fun_prod _ (fun i _ => hA.borel.comp ((measurable_pi_apply ..).comp measurable_snd))

lemma track_meas (T : Forest S.ratio)(i : S.Choices)(x : Dir G c)(hS : S.patch.Branches S.kernel G){p R σ C Λ}
    (h:R.Bounds p σ C Λ){A : Space G f → ℝ}(H : Measurable A){η}(hA:LocalRatio η):
    Measurable (track T i η p R x A) := flex_meas T i x x hS h H hA

private lemma loop_zero (P : PathData G) : Precision.loop P (1 : Config G n)=0 := by
   have hm w : pull w 0 (1:Config G n)=1 := by funext e; unfold pull Lattice.Step.read; split <;> simp
   have he (i : ℕ)(x : Site n) : (P.loop i).unmasked (1:Config G n) x=0 := by
      unfold RG.Atom.unmasked Atom.poly
      have h (v : Slot) : v.atSite (1:Config G n) x=0 := by
         unfold Slot.atSite RG.Slot.eval
         rw [show expandAt x (1:Config G n)=(1:CoverConfig G) from rfl,
           show faceValue (1:CoverConfig G) (v.offset,v.plaq)=1 from ?_,G.curvature_unit,map_zero]
         simp [faceValue,square,Lattice.Step.read,travel]
      simp [h]
   simp_rw [Precision.loop,hm,Patch.average, Precision.uncut, he]; simp

lemma remainder_home {p : Clip}{R : PathData G}{σ C Λ : ℝ}(h:R.Bounds p σ C Λ)(T : Forest S.ratio)(x : Dir G c){η : ChartRatio G}(hη : LocalRatio η) :
    remainder T η R x 0=0 ∧ ContDiffAt ℝ ω (remainder T η R x) 0 := by
   have hw (i : T.Free) : η.J ((0:AxisChart G T) i)=1 := hη.anchored
   have hu : axisJ T η 0=1 := Finset.prod_eq_one fun _ _=>hw _
   have ht : ContDiffAt ℝ ω (Precision.loop R ∘ Work.F03.live T) (shift T x 0) := by
      rw [map_zero]; exact Progress.StationaryScenes.loop_smooth h (Work.F03.live_smooth T)
   constructor
   · unfold remainder; simp only [Pins.visits_home,Prod.snd_zero,loop_zero,hu]; simp
   have H : ContDiffAt ℝ ω (axisJ T η) 0 := contDiffAt_prod fun i _=>
      (hη.germ 0 (Metric.mem_ball_self hη.patch)).comp (f:=fun v : AxisChart G T=>v i) _ (contDiffAt_apply ..)
   exact (ht.comp _ (shift T x).contDiff.contDiffAt).sub ((H.log (hu ▸ one_ne_zero)).comp (f:=Prod.snd) (0:ℝ×AxisChart G T) contDiffAt_snd)

private lemma add_terms {E : Type}[NormedAddCommGroup E][NormedSpace ℝ E](F G:E→ℝ) (h:ContDiffAt ℝ ∞ F 0) (H:ContDiffAt ℝ ∞ G 0)(x:E)(i:ℕ) :
    Radial.jet (F+G) i x=Radial.jet F i x+Radial.jet G i x := by
   have he : (i:WithTop ℕ∞)≤∞ := WithTop.coe_le_coe.mpr le_top
   simp only [Radial.jet,iteratedFDeriv_add_apply (h.of_le he) (H.of_le he),_root_.add_apply,mul_add]

private lemma near_higher {E : Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
    (F : ℝ× E→ℝ)(h : ContDiffAt ℝ ∞ F 0)(hh : F 0=0) :
    let f := fun x : ℝ× E => x.1^2*F x
    ContDiffAt ℝ ∞ f 0 ∧ ∀ i≤2, ∀ x : ℝ×E, Radial.jet f i x=0 := by
   intro f
   have H : ContDiffAt ℝ ∞ f 0 := (contDiffAt_fst.pow 2).mul h
   refine ⟨H,fun i hi x=>?_⟩
   open PowerSeries in
   have he x : Asym.layer f x= X^2*(C (x.1^2:ℂ)* Asym.layer F x) := by
      refine Asym.Near.unique' (Asym.layer_ray H x) ?_
      have hu := Asym.Near.promote (Asym.Near.scaled (Asym.layer_ray h x) (↑x.1^2)) 2
      convert! hu using 1
      funext t; simp only [f, Prod.smul_fst,Complex.ofReal_mul,Complex.ofReal_pow,Pi.smul_apply, Complex.real_smul,smul_eq_mul]; ring
   open PowerSeries in
   have hg (x) : PowerSeries.coeff i (Asym.layer f x)=0 := by
      rw [he x, PowerSeries.coeff_X_pow_mul']; split
      next hv => rw [Nat.sub_eq_zero_of_le hi, PowerSeries.coeff_C_mul]; simp [Asym.layer,hh]
      rfl
   have hx := hg x; simpa [Asym.layer] using hx

def arcRay (T : Forest S.ratio) (i : S.Choices)(p : Clip)(R : PathData G)(x y : Dir G c)(u : ℝ×AxisChart G T) :=
   mainTerm p R (Pins.visits T y u).2 + noiseTaylor S (represent (u.1 • x)) (Pins.visits T y u).2 i

lemma flex_enact (T : Forest S.ratio)(i : S.Choices)(η : ChartRatio G)(p : Clip)(R : PathData G)(x y : Dir G c)(A : Space G f→ℝ) :
   flex T i η p R x y A= arcRay T i p R x y + (A ∘ Pins.visits T y) + fun u => u.1^2 * remainder T η R y u := by
   ext u; unfold remainder flex field arcRay
   simp only [Pi.add_apply,Function.comp_apply,mul_sub]
   rw [← add_sub_assoc]; rfl

theorem flightFrom (T : Forest S.ratio)(s : S.Choices){p R} (x y : Dir G c)
    {ψ : PertExtension.GaussianScore.Law (AxisChart G T)}{r : ℝ}{t : AxisChart G T}(hb : Steer ψ (arcRay T s p R x y) r t)
    {σ C Λ : ℝ}(hw : R.Bounds p σ C Λ) {η : ChartRatio G}(ht : LocalRatio η){A : Space G f→ℝ}(H : Ambient A) :
    Steer ψ (flex T s η p R x y A) r t := by
   obtain ⟨hb,Hb⟩ := hb
   obtain ⟨hg,hG⟩ := Pins.design T y H
   obtain ⟨hi,hR⟩ := remainder_home hw T y ht
   obtain ⟨he,hU⟩ := near_higher _ (hR.of_le le_top) hi
   have hh k (hy:k≤2) (u) : Radial.jet (flex T s η p R x y A) k u=Radial.jet (arcRay T s p R x y) k u := by
      rw [flex_enact, add_terms (arcRay T s p R x y + A ∘ Pins.visits T y) _ (hb.smooth.add hg) he, hU _ hy, add_zero]
      rw [add_terms _ _ hb.smooth hg, hG k (by omega),add_zero]
   refine ⟨⟨?_,?_,fun y=> (hh 1 (by omega) y).trans (hb.base1 y)⟩,fun i y =>?_⟩
   · rw [flex_enact]; exact (hb.smooth.add hg).add he
   · simpa only [Radial.jet_zero,hb.base0] using hh 0 (by omega) (0:ℝ×AxisChart G T)
   rw [hh 2 le_rfl,Hb]

theorem flight (T : Forest S.ratio)(s : S.Choices){p R w}{ρ : Dir G c→ AxisChart G T}{Q : Bed}
    (hp : 0<w)(hr:PriceGap T p R w)(h : Critical T p R ρ)(hc : Comptroller T Q p R) (x : Dir G c)
    {σ C Λ : ℝ}(hw : R.Bounds p σ C Λ) {η : ChartRatio G}(ht : LocalRatio η){A : Space G f→ℝ}(H : Ambient A) :
    Steer (Γ s hp hr h) (track T s η p R x A) (due T s p R x (crest T ρ x)) (crest T ρ x) :=
   flightFrom T _ x x (launch s hp hr h hc x) hw ht H

end YM.RG02.Fk
