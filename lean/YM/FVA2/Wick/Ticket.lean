import YM.FVA2.Wick.Average
/-!
# Reading RG10 MultiGauge tickets in the MS algebra

using the **real** coefficients of the joint series. Enough for log-Haar, unmarked and stamps.
Real->complex is not an invocation of reality of a continuum diagram prescription. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Wick
open Function Set Finset Filter MeasureTheory
open MS MS.Koszul MS.Plane MS.Orbit MS.Orbit.Cog MS.Swirl MS.Book Convolve MS.Cylinder Taylor
open MS.Puff MS.Puff.Mom MS.Puff.Engine MS.Puff.Actors Gem
open YM.FormalOPE.RG10.MultiGauge PowerSeries

open Formal (overlay)
open PertExtension.Series.Radial PertExtension.GaussianScore
open FormalOPE.RG10
open scoped BigOperators Topology ContDiff Matrix
variable {E A B J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
local notation "A₀" => (Index A J)
local notation "p" => sector (A:=A) (J:=J)
local infixl:70 " ⋆ " => product p
local infixl:70 " ★ " => overlay p
local notation "P" => Permit E
local notation "T" => Splice.Ticket E
namespace Boson
variable (e : A → E)
local notation "σ" => Poly.encode (J:=J) e

/-- Retain leg ranks for the body, only vacuum/g powers split. -/
def bills : T →ₗ[ℝ] Formal.Table A₀ := LinearMap.pi (fun i:ℕ => Poly.encode (J:=J) e ∘ₗ ((coeff i (R:=Permit E)).restrictScalars ℝ)) -- power series Module ℝ issue

local notation "Λ" => bills (J:=J) e

lemma at_bill (x:T) (n:ℕ) : Λ x n = σ (coeff n x) := rfl
lemma tab_const (x:P): Λ (C x)=Formal.tab (σ x):= by funext i; rw [at_bill,coeff_C, Formal.tab_value]; split; rfl; exact map_zero _
lemma tab_one : Λ 1= (PermV p).unit := by rw [← map_one (C (R:=Permit E)), tab_const,Poly.encode_unit]; rfl
lemma tab_mul (x y:T) : Λ (x*y)= Λ x ★ Λ y := by
  funext n; rw [Formal.coeff_prod,at_bill, PowerSeries.coeff_mul,map_sum]; exact Finset.sum_congr rfl fun i _=> Poly.encode_product e _ _
lemma tab_pow (x:T) (n:ℕ): Λ (x^n)=(PermV p).power (Λ x) n:= by induction n with | zero=>rw [pow_zero,tab_one]; rfl| succ n ih=> rw [pow_succ',tab_mul,ih,power]
lemma tab_exp (x:T) : Λ (MultiGauge.Stack.exponential x)= exp0 p (Λ x):= by
  funext i; unfold MultiGauge.Stack.exponential exp0 Cheer cheers; rw [at_bill,PowerSeries.coeff_mk, map_sum,map_sum,Finset.sum_apply]
  apply Finset.sum_congr rfl; intro n _
  rw [MultiGauge.Stack.roll,coeff_C_mul, ← Algebra.smul_def, map_smul]; unfold Actors.wages; rw [Pi.smul_apply, ← tab_pow, at_bill ]; change ((↑(((n.factorial:ℝ))⁻¹):ℂ) • σ (PowerSeries.coeff i (x^n))) = _; push_cast; rfl
lemma analytic (f:E→ℝ) (h:germ f) : Λ (MultiGauge.Stack.rise f)= Gem.letter (eased (J:=J) e) f := by
  funext n; unfold MultiGauge.Stack.rise; rw [at_bill, PowerSeries.coeff_mk]; exact (ranked _ _ _ h).symm
lemma bills_alone (x:T) : Λ x∈ allIndex (Alone p) ℕ:= fun _ _=> Poly.encode_alone e _
lemma bills_funded (x:T) : Λ x ∈ Formal.OK p := fun _ _=> Poly.fee e _
lemma bills_even (x:T) : Λ x∈ Formal.even p:= Formal.ev.mpr fun i=> alone_pure (bills_alone (J:=J) e x i (mem_univ _))

variable (B : Module.Basis A ℝ E) [Fintype A][DecidableEq A][Fintype J][DecidableEq J]
variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E)[Measure.IsAddHaarMeasure μ]
variable (b : Law E)
omit e
omit [DecidableEq A] [DecidableEq J] in
lemma read_body (x:T) (n:ℕ): View (Fermion.bev (bosonMatrix b B) J) (bills B x n)= ( (coeff n (Splice.input b μ x) : ℝ):ℂ) := by
  unfold Splice.input Splice.throughPrice; rw [AddMonoidHom.coe_mk,ZeroHom.coe_mk,coeff_mk]; exact every ..
end Boson

namespace Gem
-- log Jacobian analytic power identity
variable {f:E→ℝ} (e:A→E) {b:Sector A}(hb:∀ i,b i=true→e i=0)
local notation "θ" => Swirl.clock useN (Raw A ℂ)
omit [FiniteDimensional ℝ E] in
lemma Eexp (h:germ f): Euler (Real.exp ∘ f) =ᶠ[𝓝 0] Euler f * (Real.exp ∘ f):= by
  filter_upwards [h.eventually (by simp)] with x hx
  unfold Euler layer
  obtain H : fderiv ℝ (Real.exp ∘ f) x = Real.exp (f x) • fderiv ℝ f x := ((hx.differentiableAt (by simp)).hasFDerivAt.exp).fderiv
  rw [H]; exact mul_comm ..
include hb
omit [FiniteDimensional ℝ E] in
lemma inkExp (h:germ f)(hf:f 0=0): exp0 b (Gem.letter e f)= Gem.letter e (Real.exp ∘ f):= by
  let t := Gem.letter e f; let h' : germ (Real.exp ∘ f):= Real.contDiff_exp.contDiffAt.comp _ h
  have he : t 0=0:= by unfold t; rw [Gem.first,hf]; funext l; cases l <;> rfl
  refine tick_agree useN (actor b) (u:=θ t) (tick0 useN t) ?_ ( (turn_clock useN (actor b)).idea (Gem.even e hb f) he ) ?_
  · change exp0 b t 0=Gem.letter _ _ 0; rw [Formal.exp_zero b he, Gem.first,comp_apply,hf,Real.exp_zero, Complex.ofReal_one]
  rw [← clock e h', nearby e (Eexp h), times e hb (Euler_s h) h',clock e h]; rfl
end Gem
end YM.FVA2.Wick
