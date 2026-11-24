import YM.FVA2.OrbitWick
import YM.PertExtension.Tails
import YM.PertExtension.Aspiration
import YM.XSpace.FPS

/-!
# Taylor / Wick unnormalized correspondence

From log-chart stationary comparison (including the precise divided Hessian order conventions)
to ordinary diagram coefficients. Basis not required; inputs can be any presentation using
linear slots. Here `H` is Haar relative power series times the rescaled insertion before Wick;
`A` is the log-weight higher interaction (in the convention of `Route.Bulk`); `Advance` and
`Num` use the full joint product. We work before the normalization to be able to compare systems
of arbitrary source products and later conditional denom as well as terminal. Instantiations to
actual inputs in other files. This part uses an explicit leading quadratic kernel identity
NOT the desired comparison or any assumption on higher Wick coefficients.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.TaylorWick
open Function Set Filter MeasureTheory Module PowerSeries
open PertExtension PertExtension.Series PertExtension.GaussianScore
open Next.Rank.Normal
open scoped Topology ContDiff BigOperators Classical ENNReal
variable {E I : Type*}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable (Γ : Law E) (S : I → Module.Dual ℝ E)
variable (A H:PowerSeries (poly I)) (q f:E→ℝ)

-- This uses factorial scalar multiplication, for our algebra of complex polynomials.
def Advance (A:PowerSeries (poly I)):PowerSeries (poly I):= PowerSeries.mk fun n=>
   ∑ j∈Finset.range (n+1),(j.factorial:ℂ)⁻¹ • coeff n (A^j)
@[simp] theorem advance_origin : coeff 0 (Advance A)=1:=by simp [Advance]

def Num (Q:Symmetric I)(A H:PowerSeries (poly I)):PowerSeries ℂ:=
    PowerSeries.mk fun n=> blend Q 0 (coeff n (Advance A * H))

@[simp] theorem num_origin (he:coeff 0 H=1)(Q:Symmetric I): constantCoeff (Num Q A H) = 1:=by
   rw [← coeff_zero_eq_constantCoeff_apply]; simp only [Num,coeff_mk,coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, he, advance_origin,mul_one,fresh]

open Radial
def Reads (A:PowerSeries (Next.Rank.Normal.poly I))(S:I→Dual ℝ E)(t:ℕ→E→ℝ):Prop:=
    ∀ i x,MvPolynomial.aeval (R:=ℂ) (fun j=> ((S j x:ℝ):ℂ)) (coeff i A)= (t i x:ℂ)
variable {A H S q f}{K V:ℕ→E→ℝ}
namespace Reads
omit [FiniteDimensional ℝ E] in
lemma prod (h:Reads A S K)(he:Reads H S V): Reads (A*H) S (Zone.mul K V):=by
   intro i x; rw [coeff_mul,map_sum,Zone.mul,Complex.ofReal_sum]; refine Finset.sum_congr rfl fun j hj=>?_ ; rw [map_mul,h,he,Complex.ofReal_mul]
omit [FiniteDimensional ℝ E] in
lemma pow (h:Reads A S V)(k:ℕ): Reads (A^k) S (Zone.TaylorPow V k):=by
   induction k with
   | zero=> intro i x; rw [pow_zero,coeff_one]; unfold Zone.TaylorPow; split_ifs <;> simp
   | succ k ih=> rw [pow_succ]; exact ih.prod h
omit [FiniteDimensional ℝ E] in
lemma advance (h: Reads A S V): Reads (Advance A) S (fun i=>expsum V i i):= by
   intro i x; dsimp only; rw [Advance,coeff_mk,map_sum,expsum,Complex.ofReal_sum]; refine Finset.sum_congr rfl fun j _=>?_
   rw [map_smul,smul_eq_mul,(h.pow j) i x]; push_cast; rfl
end Reads

variable [MeasurableSpace E][BorelSpace E]
variable (μ:Measure E)[μ.HasTemperateGrowth][μ.IsAddRightInvariant][NeZero μ]
def mass : ℝ:= ∫ x, Γ.kern x ∂μ
omit [μ.IsAddRightInvariant] in
lemma mass_pos : 0 < mass Γ μ:= by
  have ht := Γ.integrable_entry (A:=(1:E→ℝ)) μ (Zone.Invoice.const (1:ℝ)) continuous_const
  rw [one_mul] at ht; exact integral_exp_pos ht

/-- Exact coefficient formula relating the repository's (unshifted) radial stationary algorithm
`moment` to polynomial Wick. `f` includes the measure vertex and the full insertion, with an
option to factor a constant: its radial Taylor jets are `c` times the jets H used by `Num`.
(Laplace chart convention uses `c = jacobian Z 0`.) -/
theorem moment_wick (hV:Reads A S (layers q)){c:ℝ}(hH: ∀ i x,
    ((jet f i x:ℝ):ℂ)=c * MvPolynomial.aeval (R:=ℂ) (fun j=> ((S j x:ℝ):ℂ)) (coeff i H))
    (he:∀ x,kernel q x=Γ.kern x)(i:ℕ):
    (moment μ f q i : ℂ) = c * (mass Γ μ:ℂ) * coeff i (Num (Wick.color Γ S) A H):=by
   let T:= coeff i (Advance A * H)
   let M(x:E):= Wick.evaluation Γ S x T
   have hw (x:E) : (normTerm f q i x:ℂ)=c*M x:=by
      let h (p:Next.Rank.Normal.poly _) := MvPolynomial.aeval (R:=ℂ) (fun j=> ((S j x:ℝ):ℂ)) p
      have hp : ((integrandSeries q f i x:ℝ):ℂ)= c*h T:=by
          dsimp only [h,T]; rw [mul_comm (Advance A),coeff_mul,map_sum,Finset.mul_sum,integrandSeries,Zone.mul,Complex.ofReal_sum];
          refine Finset.sum_congr rfl fun j _=> ?_
          rw [Complex.ofReal_mul,map_mul,(Reads.advance hV) j.2 x,hH]; ring
      rw [normTerm,Complex.ofReal_mul,he,hp]; unfold M Wick.evaluation h; ring
   rw [Num,coeff_mk,← Wick.report_eq Γ S μ]; unfold Wick.report moment; rw [← integral_complex_ofReal]; simp_rw [hw]; rw [MeasureTheory.integral_const_mul];
   have ht: (↑(mass Γ μ):ℂ)≠0:=by exact_mod_cast (mass_pos Γ μ).ne'
   change ↑c * (∫ x, M x ∂μ)= ↑c*(↑(mass Γ μ):ℂ)*((∫ x, M x ∂μ)/(↑(mass Γ μ):ℂ))
   field_simp

open Series.Tested

def into : PowerSeries ℝ →+* PowerSeries ℂ:= PowerSeries.map Complex.ofRealHom
@[simp] theorem into_coeff (A:PowerSeries ℝ) (i:ℕ): coeff i (into A)=(coeff i A:ℝ):= coeff_map ..
/-- Remove *one common constant* from a whole normalized system, provided both systems use unit
normalization; no boundedness/uniformity in the value of the constant is needed. -/
lemma ratio (N D:ℕ→ℝ) (U V:PowerSeries ℂ)(s:ℂ)(h:s≠0)
    (hn:into (PowerSeries.mk N)= C s *U)(hd:into (PowerSeries.mk D)=C s * V)
    (hv:constantCoeff V=1):
    into (PowerSeries.mk (divide N D)) = V⁻¹ * U:=by
   have h0: D 0≠0:=by intro ht; have h:=congr_arg (coeff 0) hd; rw [into_coeff,coeff_mk,ht, Complex.ofReal_zero,coeff_C_mul,coeff_zero_eq_constantCoeff_apply,hv,mul_one] at h; exact ‹s≠0› h.symm
   rw [show PowerSeries.mk (divide N D)= PowerSeries.mk N * (PowerSeries.mk D)⁻¹ from ?_, map_mul,hn]; rotate_left
   · apply PowerSeries.ext; intro i; exact coeff_mk ..
   let Φ:=PowerSeries.mk D; have hp: IsUnit (C s * V):= by rw [PowerSeries.isUnit_iff_constantCoeff,map_mul,hv,constantCoeff_C,mul_one]; exact h.isUnit
   apply hp.mul_right_cancel; rw [← hd]; change C s * U * into (Φ⁻¹) * into Φ= _;
   calc
    _ = C s * U := by rw [mul_assoc,← map_mul,PowerSeries.inv_mul_cancel, map_one, mul_one]; dsimp only [Φ]; rw [← coeff_zero_eq_constantCoeff_apply,coeff_mk]; exact h0
    _ = _ := by rw [hd]; have he:V⁻¹*V=1:= PowerSeries.inv_mul_cancel V (hv.symm ▸ one_ne_zero); calc
                              _ = C s * U * (V⁻¹*V):=by rw [he,mul_one]
                              _ = _:=by ring

/-- Ratio form. The two `fact`s relate Taylor presentations of the exact K*f and K terms (same
quadratic and divisor on both sides); no hypothesis on the unknown divided coefficients. -/
theorem divided_wick {H₀:PowerSeries (Next.Rank.Normal.poly I)}{f₀:E→ℝ}
    (hV:Reads A S (layers q)){c:ℝ}(hc:c≠0)(hK:coeff 0 H₀=1)
    (fact: ∀ i x, ((jet f i x:ℝ):ℂ)=c * MvPolynomial.aeval (R:=ℂ) (fun j=> ((S j x:ℝ):ℂ)) (coeff i H))
    (fact₀: ∀ i x, ((jet f₀ i x:ℝ):ℂ)=c * MvPolynomial.aeval (R:=ℂ) (fun j=> ((S j x:ℝ):ℂ)) (coeff i H₀))
    (he:∀ x,kernel q x=Γ.kern x):
    into (PowerSeries.mk (divide (moment μ f q) (moment μ f₀ q))) = (Num (Wick.color Γ S) A H₀)⁻¹ * (Num (Wick.color Γ S) A H):=by
  let s:ℂ:= c * (mass Γ μ:ℂ)
  have hs:s≠0:= mul_ne_zero (Complex.ofReal_ne_zero.mpr hc) (Complex.ofReal_ne_zero.mpr (mass_pos Γ μ|>.ne'))
  refine ratio _ _ _ _ s hs (PowerSeries.ext fun i=>?_) (PowerSeries.ext fun i=>?_) (num_origin _ _ hK _)
  all_goals rw [into_coeff,coeff_mk,coeff_C_mul]
  · exact moment_wick Γ μ hV fact he i
  exact moment_wick Γ μ hV fact₀ he i
end YM.FVA2.TaylorWick
