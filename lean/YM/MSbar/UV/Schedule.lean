import YM.MSbar.Image.Logs
import YM.Planned.ATOM_REGULAR_ESTIMATE.Parametric
/-!
# Variable spaces & polynomial admissible costs

No common thresholds between PT orders. Book stores parameter sweep, balance uses all vector chart
values in that chart, and a scale-dependent exponential damping (`exp (P.cash i)`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.High
open Function Filter Set Metric Asymptotics
open scoped Topology BigOperators Classical ContDiff
variable {ι α E F : Type}
structure Book (ι: Type) where
   using_ : Set ι
   fee : ι → ℝ
   right (i:ι) : 1 ≤ fee i
-- damping not necessarily positive *exponent*
abbrev Damping (ι:Type) := ι → ℝ
variable [NormedAddCommGroup E][NormedAddCommGroup F]
variable {B:Book ι}{P Q:Damping ι} {f g k:ι → E → ℝ}
abbrev Credit (B:Book ι) (x:ι)(e:E) : ℝ := B.fee x*(1+‖e‖)
abbrev price (B:Book ι) (P:Damping ι)(c:ℝ)(r:ℕ)(x:ι)(e:E):=Real.exp (P x)*c*Credit B x e^r
lemma Funding (B:Book ι)(x:ι)(e:E) : 1≤Credit B x e:= one_le_mul_of_one_le_of_one_le (B.right _) (by simp)
def Allows (B:Book ι)(P:Damping ι)(f:ι→ E→ℝ):Prop:=∃ (C:ℝ) (n:ℕ), 0≤ C ∧ ∀ i∈B.using_, ∀ x, f i x ≤ price B P C n i x
namespace Book
lemma inflation (B:Book ι)(P:Damping ι){c d:ℝ}{r l:ℕ}(h:0≤ c)(hc:c≤d)(hr:r≤l)(x:ι)(e:E): price B P c r x e≤ price B P d l x e:= mul_le_mul (by gcongr) (pow_le_pow_right₀ (Funding B x e) hr) (pow_nonneg (by linarith [Funding B x e]) _) (by have:= h.trans hc; positivity)
end Book
namespace Allows
variable (hp:Allows B P f) (hf:Allows B P g)
include hp
lemma adjust (he:∀ i∈ B.using_,∀ x,g i x≤ f i x): Allows B P g:= by obtain ⟨c,m,h,hQ⟩:=hp; exact ⟨c,m,h,fun x hx y=>(he x hx y).trans (hQ x hx y)⟩
lemma weaken (he:∀ i∈B.using_,P i≤Q i): Allows B Q f:= by
    obtain ⟨c,m,h,H⟩:=hp; refine ⟨c,m,h,fun i hi x=> le_trans (H i hi x) ?_⟩; unfold price; have hx:=Funding B i x; gcongr; exact he i hi
lemma scale (c:ℝ)(hc:0≤c): Allows B P (fun i x=> c*f i x):=by
    obtain ⟨q,m,h,H⟩:=hp; refine ⟨c*q,m,mul_nonneg hc h, fun i hi x=>le_trans (mul_le_mul_of_nonneg_left (H i hi x) hc) (le_of_eq ?_)⟩; unfold price; ring
include hf
lemma combine {g₁:ι→E→ℝ} (he:∀ i∈B.using_,∀ x,g₁ i x≤ f i x+g i x): Allows B P g₁:=by
    obtain ⟨r,n,h,H⟩:= hp; obtain ⟨a,m,b,J⟩:= hf; refine ⟨r+a,max n m,add_nonneg h b,fun i hi x=>?_⟩; apply le_trans (he i hi x); refine le_trans (b:=price B P r (max n m) i x+price B P a (max n m) i x) ?_ (le_of_eq ?_)
    exact add_le_add ((H i hi x).trans (B.inflation P h le_rfl (le_max_left n m) _ _)) ((J i hi x).trans (B.inflation P b le_rfl (le_max_right n m) _ _)); unfold price; ring
omit hf
lemma times (h:Allows B Q g) (H:∀ i∈ B.using_,∀ x,0 ≤ g i x)(he:∀ i∈B.using_,∀ x,k i x≤f i x*g i x): Allows B (P+Q) k:=by
    obtain ⟨r,m,h0,h1⟩:= hp; obtain ⟨s,t,hs,hg⟩:=h; refine ⟨r*s,m+t,mul_nonneg h0 hs,fun i hi x=> le_trans (he i hi x) ?_⟩; refine le_trans (mul_le_mul (h1 i hi x) (hg i hi x) (H i hi x) ?_) (le_of_eq ?_); have hx:=Funding B i x; unfold price; positivity
    unfold price; rw [Pi.add_apply, Real.exp_add,pow_add]; ring
omit hp
lemma zero (B:Book ι)(P:Damping ι): Allows B P (0:ι→E→ℝ):=⟨0,0,le_rfl,by simp [price]⟩
lemma supply (B:Book ι)(c:ℝ): Allows B 0 (fun _=>fun _: E => c):= by refine ⟨|c|,0,abs_nonneg _,fun i _ _=>?_⟩; simpa [price] using le_abs_self c
lemma sum {Ω:Type*}(I:Finset Ω)(f:Ω→ι→E→ℝ)(hf:∀ i∈I, Allows B P (f i)): Allows B P (∑ i∈I,f i):=by induction I using Finset.induction_on with | empty=>rw [Finset.sum_empty];exact zero ..|insert i s he ih=> rw [Finset.sum_insert he]; exact (hf i (Finset.mem_insert_self ..)).combine (ih fun j hj=> hf _ (Finset.mem_insert_of_mem hj)) fun _ _ _=> le_rfl
end Allows
end YM.MSbar.High
