import YM.PertExtension.Interior
import YM.RG02.Limit.Vital
import YM.RG02.Wick.Board

/-!
Texture of unintegrated jets: radial finite-part polynomials on real field
space. No outside assumption on analytic extension or gauge choice.
Pointwise scaled on positive side sufficient, even when f(t)/t² isn't a
value at t=0. Physical orders read with factors t^k divided *only after*
accounting coefficient shift.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Asym
open PertExtension PertExtension.Series PertExtension.Series.Tested Finset Filter MeasureTheory Metric Function
open PowerSeries
open scoped BigOperators Classical Topology ContDiff
variable {X F : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup F][NormedSpace ℝ F]

/-- Read finite Taylor pricing at one unbounded field value. -/
lemma read_point {u : Type}{Z : Zone u}{V : u → ℝ}{F : Type}[NormedAddCommGroup F][NormedSpace ℝ F]
    {f : ℝ→u→ F}{x : ℕ→u→ F}(h : Z.Built V f x)(i : u) : Aspiration (fun t => f t i) fun n => x n i := by
   intro n
   have hz := Z.high i
   obtain ⟨δ,C,s,hδ,hC,H⟩ := (h.fits n).cost
   have hu := (h.fits n).envelope i
   refine ⟨C*Z.w i^s*V i,by positivity,?_⟩
   filter_upwards [Tested.eventually_small (div_pos hδ (by linarith : 0<Z.w i))] with t ht
   exact H i t ht.1 ((le_div_iff₀ (by linarith)).mp ht.2.le)

-- Split complex polynomials. For real f only real component.
def layer (f:X→ℝ)(x : X) := PowerSeries.mk fun i=> Complex.ofReal (Radial.jet f i x)
def ribbon (F:X→ℂ)(x : X) := layer (fun i => (F i).re) x + PowerSeries.C Complex.I * layer (fun i => (F i).im) x

theorem ribbon_coeff (F : X→ℂ)(x : X)(n : ℕ) :
    coeff n (ribbon F x) = ↑(Radial.jet (fun i => (F i).re) n x)+ Complex.I * ↑(Radial.jet (fun i => (F i).im) n x) := by
   simp [ribbon,layer]

variable [FiniteDimensional ℝ X]

lemma layer_ray {f:X→ℝ}(h : ContDiffAt ℝ ∞ f 0)(x : X) : Near (fun t => (f (t • x):ℂ)) (layer f x) := by
   unfold Near layer; simp_rw [PowerSeries.coeff_mk]
   exact convert_x (read_point (Radial.ordinary f h) x)

theorem ribbon_test {F:X→ℂ}(h : ContDiffAt ℝ ∞ F 0)(x : X) : Near (fun t => F (t • x)) (ribbon F x) := by
   let f := fun y => (F y).re; let g := fun y => (F y).im
   have hf := layer_ray (f:=f) (Complex.reCLM.contDiff.contDiffAt.comp 0 h) x
   have hg := Near.scaled (layer_ray (f:=g) (Complex.imCLM.contDiff.contDiffAt.comp 0 h) x) Complex.I
   convert! Near.incline hf hg using 1; funext t; simp only [f,g,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_comm Complex.I,Complex.re_add_im]

-- All entries include their indicated Taylor symmetry factor. Apply scalar parameter layer changes after exponentiation.
def driven (f : X→ℝ)(x : X) := PowerSeries.mk fun i=> Complex.ofReal (Radial.layers f i x)
lemma driver_vac (f : X→ℝ)(u : X) : coeff 0 (driven f u)=0 := by simp [driven,Radial.Stationary.layers_zero]

lemma driven_price {f : X→ℝ}(H : Radial.Stationary f)(u : X) : Near (fun t=> (Radial.higher f t u:ℂ)) (driven f u) := by
  unfold Near driven; simp_rw [PowerSeries.coeff_mk]
  exact convert_x (read_point H.expansion u)
lemma fueled {f K : X→ℝ}(h : ContDiffAt ℝ ∞ K 0)(H : Radial.Stationary f)(u:X) :
    Near (fun t => Complex.ofReal (Radial.insertion f K t u)) (layer K u * ex (driven f u)) := by
    have ht := Near.mult (layer_ray h u) (exponential_ray (driven_price H u) (driver_vac ..))
    convert ht using 1; funext t; simp only [Radial.insertion,Complex.ofReal_mul,Complex.ofReal_exp]; rfl

theorem grades {f K : X→ℝ}(h : ContDiffAt ℝ ∞ K 0)(H : Radial.Stationary f)(u:X)(n : ℕ) :
    ↑(Radial.integrandSeries f K n u) = coeff n (layer K u * ex (driven f u)) := by
    have ht := convert_x (read_point (Radial.integrand h H (c:=1) zero_lt_one) u)
    exact congr_fun (Aspiration.unique ht (fueled h H u)) n

/-- Actual complex chart coefficients via the analytic jet then exp. -/
def visibly (f : X→ℝ)(K:X→ℂ)(k : ℕ)(u:X) := coeff k (ribbon K u * ex (driven f u)) * ↑(Radial.kernel f u)

lemma seen {f:X→ℝ}{K:X→ℂ}(h : ContDiffAt ℝ ∞ K 0)(H : Radial.Stationary f)(u:X)(n : ℕ) :
    visibly f K n u = ↑(Radial.normTerm (fun i => (K i).re) f n u) + Complex.I * ↑(Radial.normTerm (fun i => (K i).im) f n u) := by
    let g := fun y => (K y).re; let G := fun y => (K y).im
    simp only [Radial.normTerm,Complex.ofReal_mul];
    rw [grades (K:=g) (by exact Complex.reCLM.contDiff.contDiffAt.comp 0 h) H u n,
        grades (K:=G) (by exact Complex.imCLM.contDiff.contDiffAt.comp 0 h) H u n]
    unfold visibly ribbon; rw [add_mul,map_add,mul_assoc (PowerSeries.C Complex.I),PowerSeries.coeff_C_mul, add_mul,mul_assoc]
end YM.RG02.Asym
