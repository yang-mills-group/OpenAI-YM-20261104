import YM.FVA2.Lambda.Amber
/-!
# x jets commute through the heat integral

See `red` and `redjet`. Integrating in **a** here from 0 to 1 at fixed momentum.
See `Fields` about interchange. For the WW/CU application see `Rate`/`Scrap`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda.Lathe
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Color MS.Native
open Canvas (quad high line4 triple upperquad trigger)
open MS.City MS.Plane.Flux
open Area Shells Pages
open Complex (I)
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}
local notation "g"=>triple G
local notation "Z"=>Momentum.sq (A:=Axis)
variable (q:QP)(x a h y z:ℝ)(i:G.ColorIndex)
-- inf param ∫ high from 0. compound gaussian eta normalized
abbrev γ (a:ℝ)(q:QP):ℝ := Real.exp (-(1+a)* Momentum.sq q )
def existW (f:ℝ→ℝ)(q:QP)(x:ℝ):ℝ:= hot 0 (Z q)*melt 0 (Z (q+north x))* f x
def gem (a h x:ℝ) :ℝ:= exp (-a*(2*x*h+x^2))
def pastel (f:ℝ→ℝ)(q:QP)(a x:ℝ):ℝ:= ((γ a q*a/2)*gem a (q 0) x)*f x
abbrev unitμ : Measure ℝ:= volume.restrict (Set.Icc (0:ℝ) 1)
instance finU : IsFiniteMeasure unitμ:= ⟨by rw [unitμ,Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top⟩
lemma red (f:ℝ→ℝ) : (∫ a, pastel f q a x ∂ unitμ)= existW f q x:= by
    unfold existW hot melt pond; rw [ Real.exp_zero ]; unfold unitμ; rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1) ]; simp only [one_pow,one_mul,neg_one_mul ]; rw [ ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_mul_const ]; apply intervalIntegral.integral_congr; intro a _; unfold pastel steam γ gem; rw [zipper]; have he : - Z q + (-a)*( Z q+2*x*(q 0)+x^2 ) = -(1+a)*Z q+-a*(2*x*(q 0)+x^2):= by ring
    obtain hv:= congr_arg Real.exp he; rw [exp_add,exp_add] at hv; linear_combination (a/2) * f x * (-hv)
lemma tone (f:ℝ→ℝ)(hf:ContDiff ℝ ∞ f): Majorant unitμ (pastel f q):= by
    let L(x:ℝ×ℝ):= pastel f q x.1 x.2; have hL:ContDiff ℝ ∞ L:= by unfold L pastel γ gem; fun_prop
    exact Heat.Lot _ ⟨_,isCompact_Icc,ae_restrict_mem measurableSet_Icc⟩ hL
lemma ting (f:ℝ→ℝ)(hf:ContDiff ℝ ∞ f): ContDiff ℝ ∞ (existW f q):= by have he:= Majorant.contDiff (tone q f hf); simp_rw [red] at he; exact he
def read (n:ℕ)(f:ℝ→ℝ):ℝ:= (Nat.factorial n:ℝ)⁻¹ * iteratedDeriv n f 0
def cast (f:ℝ→ℝ): ℝ→ℂ:= fun x=>(f x:ℂ)
lemma cast_read (n:ℕ)(f:ℝ→ℝ)(hf:ContDiff ℝ ∞ f): reading n ( Lathe.cast f )= ↑(Lathe.read n f):= by
   rw [ show Lathe.cast f=(fun x=> (f x:ℝ) • (1:ℂ)) from funext (fun x=> by rw [Complex.real_smul, mul_one]; rfl) ]
   unfold reading Lathe.read; rw [iteratedDeriv_smul_const (.of_le hf.contDiffAt (by exact_mod_cast le_top)) ]; simp [Complex.real_smul]
lemma read_mul (n:ℕ)(f l:ℝ→ℝ)(hf:ContDiff ℝ ∞ f)(hl:ContDiff ℝ ∞ l) : Lathe.read n (fun x=>f x*l x)=∑ i∈Finset.range (n+1),Lathe.read i f* Lathe.read (n-i) l:= by
    apply Complex.ofReal_injective; simp only [Complex.ofReal_sum, Complex.ofReal_mul]; rw [← cast_read _ _ ( hf.mul hl ) ]; simp_rw [← cast_read _ f hf, ← cast_read _ l hl ]; unfold Lathe.cast; simp_rw [Complex.ofReal_mul]; exact Plane.read_mul (Complex.ofRealCLM.contDiff.comp hf) (Complex.ofRealCLM.contDiff.comp hl)
lemma redjet (n:ℕ)(f:ℝ→ℝ)(hf:ContDiff ℝ ∞ f): Lathe.read n ( existW f q )= ∫ a, (γ a q*a/2)*Lathe.read n (fun x=>gem a (q 0) x * f x) ∂unitμ := by
    rw [ (show existW f q= (fun x=>∫ a, pastel f q a x ∂unitμ) from funext (fun x=>(red q x _).symm) ) ]; unfold Lathe.read; rw [show ((Nat.factorial n:ℝ)⁻¹*iteratedDeriv n _ (0:ℝ))=_ from Pages.sponge _ (tone q f hf) n ]; apply integral_congr_ae; filter_upwards with a; unfold pastel; rw [ show (fun x=> ( γ a q*a/2 * gem a (q 0) x )*f x)=(fun x=> (γ a q*a/2)*(gem a (q 0) x*f x)) from funext (fun t=> by rw [mul_assoc]), iteratedDeriv_const_mul_field ]; simp only [smul_eq_mul]; ring
lemma gem_D : HasDerivAt (gem a h) ((-2*a*(h+x))*gem a h x) x:= by
    unfold gem; have he:= ( ( ( hasDerivAt_id' x ).const_mul (2:ℝ)|>.mul_const h ).fun_add ((hasDerivAt_id' x).pow 2 ) ); convert! ((he.const_mul (-a)).exp ) using 1; simp [ Pi.pow_apply ]; ring
lemma gem_Ω : ContDiff ℝ ∞ (gem a h):= by unfold gem; fun_prop
@[simp] lemma read₀ (f:ℝ→ℝ): Lathe.read 0 f=f 0:= by simp [Lathe.read]
@[simp] lemma gem_l : gem a h 0=1:= by simp [gem]
lemma gem_1 : Lathe.read 1 (gem a h)= -2*a*h:= by rw [Lathe.read, iteratedDeriv_one, (gem_D 0 a h).deriv]; simp
lemma gem_2 : Lathe.read 2 (gem a h)= 2*a^2*h^2 -a:= by
    have he:= ( ( ( ( hasDerivAt_id' (0:ℝ)).const_add h).const_mul (-2*a) ).fun_mul (gem_D 0 a h)); unfold Lathe.read; rw [ iteratedDeriv_succ,iteratedDeriv_one, show deriv (gem a h)=( fun x=> -2*a*(h+x)*gem a h x ) from funext (fun x=> (gem_D x a h).deriv), he.deriv ]; norm_num; ring
end YM.FVA2.Lambda.Lathe
