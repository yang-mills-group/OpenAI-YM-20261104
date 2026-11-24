import YM.PertExtension.OrbCovariance
import YM.FormalOPE.RG10.Powers

/-!
# The WilsonX tree prescription on the finite inversion quotient

The `FlatFeed` specialization here is NOT the actual finite-volume RG/regulator. It is one
necessary object for `RG_09/10`, the **other**, formal-calculation regulator for orbital perturbation theory
at its finite TOP. We choose the accepted `PertExtension.Orb` TREE gauge, all non-tree edge
orbit variables, Haar product, equivariant fields (even gauge transformations), no mass term.
Side `n` even, intended at least four. In this specialization there is no stochastic predictor
tag; use `Unit`. No identification with any other orbit prescription or gauge fixing here nor
with `History.step`. In particular this is NOT unconditioning within a proof about increasing
volumes. We compare to the accepted independent top Wilson `diagonalWith` there with its Hessian
inverse Gaussian, measure & factorials & bare-g conventions. This works including at coincident
lattice placements (stencils on the torus), no assertion about taking any separated or contact
limit.

This is before measuring-frame conversions. For `fiscal` the gauge-fixed tree chart Wilson
ACTION, the order 2 jet (in the color normalization and already dividing by 2!) is exactly the
quadratic action, used only in the saddle (see `second_jet`). Higher jets in `vertices.V` have
MINUS sign and are advanced by 2 places (action prefactor inverse g²). Jacobian includes the
normalized germ of `Orb.tray`'s density in those same non-tree links (retaining all measure
vertices), dividing by its positive flat value, so the leading expectation is precisely the free
normalized Gaussian on this regulator. Both the common determinant (with Haar tangent mass) and
g^dim cancel in the Wilson coefficient prescription; if consuming this in a multiscale
comparison on the orb, still need a proof that the conditional blocking germs & measures give
these same top diagrams. We do not fit any actual coefficients.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.InversionTop
open Gauge Lattice PertExtension PertExtension.Chart PertExtension.Orb
open YM.PertExtension.Series YM.PertExtension.Series.Radial YM.PertExtension.Series.Tested
open Precision PowerSeries MeasureTheory Filter
open scoped ContDiff Topology BigOperators Classical

-- explicit ring map (markers complex, orbit integrals real on the real basis)
def into : PowerSeries ℝ →+* RG10.Series := PowerSeries.map Complex.ofRealHom
@[simp] lemma into_coeff (a : PowerSeries ℝ) (n : ℕ) : coeff n (into a) = (coeff n a : ℝ) := by
  rw [into, PowerSeries.coeff_map]; rfl

variable {G : Gauge} {n : Side} (hn : Even n.val)
local notation "E" => Dir G n
local notation "μ" => tangent G (Cotree n)
local notation "P" => tray G

/-- Our terminal `FlatFeed` uses exactly the normalized Gaussian of `OrbCovariance`. -/
def feed : FlatFeed Unit (Dir G n) where
  chance _ := 1
  chance_nonneg _ := zero_le_one
  chance_one := by simp
  base _ := μ
  density _ := Radial.kernel fiscal
  density_nonneg _ := Eventually.of_forall fun _ => Radial.kernel_pos.le
  density_integrable _ := ker_integrable hn
  mass_pos _ := integral_exp_pos (ker_integrable hn)

lemma feed_real_mean (f : Dir G n → ℝ) :
    (feed hn).mean (fun x => (f x.2 : ℂ)) = gaussian hn f := by
  simp only [FlatFeed.mean, feed, Finset.univ_unique, Finset.sum_singleton, Complex.ofReal_one,
    one_mul, gaussian, GaussianScore.Law.average, ← saddleLaw hn]
  simp only [Pi.mul_apply, ← Complex.ofReal_mul]
  rw [integral_complex_ofReal]; push_cast; congr 2; exact integral_congr_ae (Eventually.of_forall fun x => mul_comm ..)

private def initialJac (G : Gauge) (n : Side) := jacobian (U:=Cotree n) (tray G) 0
private lemma initial_pos : 0 < initialJac G n := by
  apply Finset.prod_pos
  intro i _
  apply lt_max_of_lt_left
  rw [Pi.zero_apply, (traySpec G).anchored, mul_one]; exact (traySpec G).scale

/-- Real-to-complex jet kernel before any nominal coupling shift. -/
def lift (f : Dir G n → ℝ) : Kernel (Unit × Dir G n) := fun x => into (PowerSeries.mk fun i =>
  jet f i x.2)

@[simp] lemma row_lift (f : Dir G n → ℝ) (i : ℕ) (a : Unit × Dir G n) :
    row i (lift f) a = (jet f i a.2 : ℝ) := by simp [row, lift]

private lemma jet_mul {f g : Dir G n → ℝ} (hf : ContDiffAt ℝ ∞ f 0) (hg : ContDiffAt ℝ ∞ g 0)
    (x : Dir G n) : PowerSeries.mk (fun i => jet (f*g) i x) =
    PowerSeries.mk (fun i => jet f i x) * PowerSeries.mk (fun i => jet g i x) := by
  have he : (fun i => jet (f*g) i x) = conv (fun i => jet f i x) (fun i => jet g i x) :=
    (directions (hf.mul hg) x).unique ((directions hf x).prod (directions hg x))
  ext k : 1; rw [coeff_mk]; exact congr_fun he k

lemma lift_mul {f g : Dir G n → ℝ} (hf : ContDiffAt ℝ ∞ f 0) (hg : ContDiffAt ℝ ∞ g 0) :
    lift (f*g) = lift f * lift g := by
  funext x; unfold lift; rw [jet_mul hf hg, map_mul]; rfl

lemma lift_one : lift (1 : Dir G n → ℝ) = 1 := by
  funext x; apply PowerSeries.ext; intro k
  change row k (lift _) x = coeff k 1
  rw [row_lift, coeff_one]
  rcases k with _|k
  · simp
  simp [show (1 : Dir G n → ℝ) = fun _ => 1 from rfl, jet, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero _)]

/-- Include all the formal Wilson and measure vertices at this saddle. -/
def vertices (G : Gauge) (n : Side) : Vertices (Unit × Dir G n) where
  V x := into (PowerSeries.mk fun j => layers fiscal j x.2)
  J x := PowerSeries.C ((initialJac G n : ℂ)⁻¹) * lift (jacobian (tray G)) x
  V0 := by funext x; simp [row]
  J0 := by
    funext x; simp only [row, lift, coeff_C_mul, into_coeff, coeff_mk, jet_zero, Pi.one_apply];
    apply inv_mul_cancel₀ (show ((initialJac G n:ℝ):ℂ) ≠ 0 by exact_mod_cast (initial_pos (G:=G) (n:=n)).ne')

@[simp] lemma vertex_J (x : Unit × Dir G n) (i : ℕ) : row i (vertices G n).J x =
    ↑((jacobian P (U:=Cotree n) 0)⁻¹ * jet (jacobian P) i x.2) := by
  simp [row, vertices, lift, initialJac]

@[simp] lemma vertex_V (x : Unit × Dir G n) (i : ℕ) : row (i+1) (vertices G n).V x =
    ↑(-jet fiscal (i+1+2) x.2) := by
  simp [row, vertices, Radial.layers]

/-- Raw Taylor rule at the saddle, prior to field engineering restoration. -/
def raw (O : Observable G n) : Kernel (Unit × Dir G n) := lift (O ∘ expLinks G (Cotree n))

@[simp] lemma raw_one : raw (1 : Observable G n) = 1 := lift_one

lemma raw_mul {O Q : Observable G n} (h : LocalTest O) (k : LocalTest Q) :
    raw (O*Q) = raw O * raw Q := lift_mul h.germ k.germ

private lemma exp_vertex (x : Unit × Dir G n) : expTaylor ((vertices G n).V x) =
    into (PowerSeries.mk fun j => expsum (layers fiscal) j j x.2) := by
  let V := PowerSeries.mk fun j => layers fiscal j x.2
  have h (k j) : coeff j (V ^ k) = Zone.TaylorPow (layers fiscal) k j x.2 := by
    induction k generalizing j with
    | zero => simp [Zone.TaylorPow]
    | succ k ih => simp [pow_succ, coeff_mul, Zone.TaylorPow, Zone.mul, ih, V]
  ext j : 1
  change coeff j (expTaylor (into V)) = _
  simp only [expTaylor, coeff_mk, into_coeff, expsum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [← map_pow, into_coeff, h]; push_cast; rfl

private lemma integrand_eq {O : Observable G n} (h : LocalTest O) (i : ℕ) (x : Unit × Dir G n) :
    row i ((vertices G n).weight * raw O) x =
    ((initialJac G n:ℝ):ℂ)⁻¹ * (integrandSeries fiscal (accountingWith P O) i x.2 : ℝ) := by
  let v : RG10.Series := into (PowerSeries.mk fun j => expsum (layers fiscal) j j x.2)
  have hp : (accountingWith P O) = jacobian P * (O ∘ expLinks G (Cotree n)) := rfl
  have he : ((vertices G n).weight * raw O) x =
      PowerSeries.C ((initialJac G n:ℂ)⁻¹) * (lift (accountingWith P O) x * v) := by
    rw [hp, lift_mul ((Ratio.jacobian_smooth (traySpec G) (U:=Cotree n)).of_le le_top) h.germ]
    change expTaylor ((vertices G n).V x) * (PowerSeries.C ((initialJac G n:ℂ)⁻¹) * lift (jacobian P) x) * raw O x = _
    rw [exp_vertex]
    unfold v raw; rw [Pi.mul_apply]; ring
  change coeff i (((vertices G n).weight * raw O) x) = _
  rw [he, coeff_C_mul]; unfold v integrandSeries
  simp [lift, ← map_mul, into_coeff, coeff_mul, Zone.mul]

private lemma integrand_law {O : Observable G n} (h : LocalTest O) (i : ℕ) :
    (fun x : Dir G n => (Radial.kernel fiscal x : ℂ) * row i ((vertices G n).weight * raw O) ((),x)) =
      fun x => ((initialJac G n:ℝ):ℂ)⁻¹ * (normTerm (accountingWith P O) fiscal i x : ℝ) := by
  funext x
  rw [integrand_eq h]; unfold normTerm; push_cast; ac_rfl

lemma funded {O : Observable G n} (h : LocalTest O) :
    (feed hn).Funded ((vertices G n).weight * raw O) := by
  rintro i ⟨⟩
  change Integrable (fun x : Dir G n => (Radial.kernel fiscal x : ℂ) * row i _ ((),x)) μ
  rw [integrand_law h]
  exact (((fiscal_stationary (G:=G) (n:=n)).integrableTerm (k:=i) μ (chart_integrand (traySpec G) h)
    (coercion hn)).ofReal).const_mul _

private def treeMass (G : Gauge) (n : Side) : ℝ := ∫ x : Dir G n, Radial.kernel fiscal x ∂tangent G (Cotree n)

private lemma tree_numerator {O : Observable G n} (h : LocalTest O) :
    (feed hn).average ((vertices G n).weight * raw O) =
    PowerSeries.C ((initialJac G n * treeMass G n : ℝ) : ℂ)⁻¹ * into (PowerSeries.mk (rows O)) := by
  ext i : 1
  rw [FlatFeed.average_coeff]
  simp only [FlatFeed.mean, feed, Finset.univ_unique, Finset.sum_singleton, Complex.ofReal_one,
    one_mul]
  -- keep the common mass
  rw [show (fun x : Dir G n => (kernel fiscal x : ℂ) * row i _ (default, x)) = _ from integrand_law h i,
    integral_const_mul, integral_complex_ofReal, coeff_C_mul, into_coeff, coeff_mk]
  unfold treeMass rows rowsWith Radial.moment; push_cast; ring

/-- Agreement with the accepted independent orbit Taylor/Hessian prescription on bare Wilson. -/
lemma tree_agreement {O : Observable G n} (h : LocalTest O) :
    (feed hn).step (vertices G n) (raw O) = into (PowerSeries.mk (diag O)) := by
  let D := (feed hn).den (vertices G n)
  have hD : D = PowerSeries.C (((initialJac G n * treeMass G n : ℝ) : ℂ)⁻¹) *
      into (PowerSeries.mk (rows (1 : Observable G n))) := by
    have H := tree_numerator hn (n:=n) (O:=1) (G:=G) one_test
    rw [raw_one, mul_one] at H; exact H
  have hr : PowerSeries.mk (rows (1 : Observable G n)) * PowerSeries.mk (diag O) =
      PowerSeries.mk (rows O) := by
    rw [mul_comm]; ext i : 1; rw [coeff_mk]; exact congr_fun (rows_with_head (traySpec G) hn O) i
  have hd : D ≠ 0 := by
    intro he
    have hd := congr_arg (coeff 0) he
    rw [show D = _ from rfl, (feed hn).den0, map_zero] at hd
    exact one_ne_zero hd
  apply mul_left_cancel₀ hd
  change (feed hn).den _ * _ = D * _
  rw [(feed hn).step_den, hD, tree_numerator hn h, mul_assoc, ← map_mul, hr]

lemma mean_recursion {I : Type} [Fintype I] [DecidableEq I]
    (ℓ : I → Orb.Source G n) (s : Finset I) {j : I} (hj : j ∈ s) :
    (feed hn).mean (fun x => ((∏ i ∈ s, ℓ i x.2 : ℝ) : ℂ)) =
    ∑ i ∈ s.erase j,
      (feed hn).mean (fun x => ((∏ r ∈ (s.erase j).erase i, ℓ r x.2 : ℝ) : ℂ)) *
        ((ℓ i ((saddle hn).inverse (ℓ j)):ℝ) : ℂ) := by
  rw [show (feed hn).mean _ = _ from feed_real_mean hn (fun x => ∏ i ∈ s, ℓ i x),
    gaussian_recursion hn ℓ s hj, Complex.ofReal_sum]; apply Finset.sum_congr rfl; intro i _
  rw [Complex.ofReal_mul]
  rw [show (feed hn).mean _ = _ from feed_real_mean hn (fun x => ∏ r ∈ (s.erase j).erase i, ℓ r x)]
end YM.FormalOPE.RG10.InversionTop
