import YM.Integration.MSCutoffGerms
import YM.Integration.MSGradedReceiverRigidity

/-! A common-regulator measured array with a nondegenerate free
limit is a formal matrix unit over the controlled cutoff-germ ring. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.MSMeasuredGermSeries

open Filter Finset Matrix MSCutoffGerms MS.Tide
open scoped BigOperators Topology Classical

variable {I J : Type*} {l : Filter I} {t : I → ℝ}

def transpose : (I → PowerSeries ℂ) →+* PowerSeries (I → ℂ) where
  toFun f := PowerSeries.mk fun k i => PowerSeries.coeff k (f i)
  map_zero' := by ext k i; simp
  map_one' := by ext k i; by_cases e : k = 0 <;> simp [PowerSeries.coeff_one, e]
  map_add' f g := by ext k i; simp
  map_mul' f g := by
    ext k i
    simp only [PowerSeries.coeff_mk, Pi.mul_apply, PowerSeries.coeff_mul,
      Finset.sum_apply, PowerSeries.coeff_mk]

def diagram (l : Filter I) : (I → PowerSeries ℂ) →+* PowerSeries (Germ l ℂ) :=
  (PowerSeries.map (hom l)).comp transpose

theorem coefficient (f : I → PowerSeries ℂ) (k : ℕ) :
    PowerSeries.coeff k (diagram l f) = hom l (fun i => PowerSeries.coeff k (f i)) := by
  rw [diagram, RingHom.comp_apply, PowerSeries.coeff_map]
  change hom l (PowerSeries.coeff k (PowerSeries.mk fun n i => PowerSeries.coeff n (f i))) = _
  rw [PowerSeries.coeff_mk]

def stored (ht : Tendsto t l atTop) (F : I → PowerSeries ℂ)
    (hf : ∀ k, Moderate l t (fun i => PowerSeries.coeff k (F i))) :
    PowerSeries (ring ht) :=
  PowerSeries.mk fun k => ⟨hom l (fun i => PowerSeries.coeff k (F i)), (member ht _).mpr (hf k)⟩

theorem exposed (ht : Tendsto t l atTop) (F : I → PowerSeries ℂ)
    (hf : ∀ k, Moderate l t (fun i => PowerSeries.coeff k (F i))) :
    PowerSeries.map (ring ht).subtype (stored ht F hf) = diagram l F := by
  ext k
  rw [PowerSeries.coeff_map, coefficient, stored, PowerSeries.coeff_mk]
  rfl

variable [Fintype J] [DecidableEq J]

def bank (ht : Tendsto t l atTop) (F : I → Matrix J J (PowerSeries ℂ))
    (z : Matrix J J (PowerSeries ℂ))
    (hf : ∀ a b k, Tendsto (fun i => PowerSeries.coeff k (F i a b)) l
      (𝓝 (PowerSeries.coeff k (z a b)))) : Matrix J J (PowerSeries (ring ht)) :=
  fun a b => stored ht (fun i => F i a b) (fun k => convergent ht (hf a b k))

theorem determinant (F : I → Matrix J J ℂ) :
    hom l (fun i => (F i).det) = (Matrix.of (fun a b => hom l (fun i => F i a b))).det := by
  let X : Matrix J J (I → ℂ) := fun a b i => F i a b
  have h (i : I) : X.det i = (F i).det :=
    (Pi.evalRingHom (fun _ : I => ℂ) i).map_det X
  rw [← show X.det = fun i => (F i).det from funext h]
  exact (hom l).map_det X

theorem measured (ht : Tendsto t l atTop) (F : I → Matrix J J (PowerSeries ℂ))
    (z : Matrix J J (PowerSeries ℂ))
    (hf : ∀ a b k, Tendsto (fun i => PowerSeries.coeff k (F i a b)) l
      (𝓝 (PowerSeries.coeff k (z a b))))
    (hz : IsUnit ((PowerSeries.constantCoeff (R := ℂ)).mapMatrix z)) :
    IsUnit (bank ht F z hf).det := by
  let X : I → Matrix J J ℂ := fun i => (PowerSeries.constantCoeff (R := ℂ)).mapMatrix (F i)
  let Z : Matrix J J ℂ := (PowerSeries.constantCoeff (R := ℂ)).mapMatrix z
  have hX : Tendsto X l (𝓝 Z) := by
    apply tendsto_pi_nhds.mpr
    intro a
    apply tendsto_pi_nhds.mpr
    intro b
    change Tendsto (fun i => PowerSeries.constantCoeff (F i a b)) l
      (𝓝 (PowerSeries.constantCoeff (z a b)))
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hf a b 0
  have hD : Tendsto (fun i => (X i).det) l (𝓝 Z.det) := continuous_id.matrix_det.continuousAt.tendsto.comp hX
  have nz : Z.det ≠ 0 := isUnit_iff_ne_zero.mp (Z.isUnit_iff_isUnit_det.mp hz)
  let D : ring ht := ⟨hom l (fun i => (X i).det), (member ht _).mpr (convergent ht hD)⟩
  have principal : IsUnit D := reciprocal ht hD nz
  have hh : ((PowerSeries.constantCoeff (R := ring ht)).mapMatrix (bank ht F z hf)).det = D := by
    let S := (PowerSeries.constantCoeff (R := ring ht)).mapMatrix (bank ht F z hf)
    let U : Matrix J J (Germ l ℂ) := Matrix.of fun a b => hom l (fun i => X i a b)
    have entries : (ring ht).subtype.mapMatrix S = U := by
      ext a b
      change ((PowerSeries.constantCoeff (bank ht F z hf a b) : ring ht) : Germ l ℂ) =
        hom l (fun i => PowerSeries.constantCoeff (F i a b))
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, bank, stored, PowerSeries.coeff_mk]
      simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    apply Subtype.ext
    exact ((ring ht).subtype.map_det S).trans ((congrArg Matrix.det entries).trans
      ((determinant (l := l) X).symm))
  apply MSGradedReceiverRigidity.formal
  rw [hh]
  exact principal

theorem error {A : Type} {l : Filter A} {P : MS.Rake.Geo A} (e : ℝ) (he : 0 < e) (w f : A → ℂ)
    (hw : Moderate l P.θ w) (hf : PeakT l P e f) :
    Tendsto (fun i => w i * f i) l (𝓝 0) := by
  obtain ⟨c, hc, h⟩ := hf
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have bound : ∀ᶠ i in l, ‖w i * f i‖ ≤ c * ‖weight P.θ e i * w i‖ := by
    filter_upwards [h] with i hi
    rw [norm_mul]
    calc
      ‖w i‖ * ‖f i‖ ≤ ‖w i‖ * (c * lake P e i) := mul_le_mul_of_nonneg_left hi (norm_nonneg _)
      _ = c * ‖weight P.θ e i * w i‖ := by
        rw [norm_mul, weight, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
        unfold lake
        ring
  apply squeeze_zero' (.of_forall fun _ => norm_nonneg _) bound
  simpa only [mul_zero, norm_zero] using (hw e he).norm.const_mul c

end YM.Integration.MSMeasuredGermSeries
