import YM.QuadraticLocal.Rebirth.Reprints
import YM.QuadraticLocal.Rebirth.Tax
/-!
# Residual repair clones (not analytic, just signed) anchored as before

No mask policy in the output region is changed when changing coupling unit
 of the marks. Sends **the whole real** test packet before recomposing, retaining
 Supports (using `Region before` & unchanged weight certificates). A repair from
 uncertain propagation still requires estimates separately; this file is only the
 genuine pose-growth adjustment from the birth of the new model.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Rebirth.Mutation
open Function Filter Finset Lattice RG Wilson Marker Earn
open Comparison.RG02 Comparison.RG02.Adjacent
open Pressure ConnectedActivityE6 AllOrder AllOrder.Catch
open AllOrder.Wheel AllOrder.Floe Next.Scheduling Next.Foundations
open PositionX.Jet AllOrder.Response PositionX.Gauss
open AllOrder.Laplace AllOrder.Laplace.SigmaP
open Ac Push Push.AbsoluteSums Paths Animals
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open Chart Sunrise
variable {V ι W:Type}[DecidableEq V]{R:Census V}
variable {G:Gauge}{n:Side} {P:Passport n V}
variable (X:ι→Row P R G W) (B:BudgetPoint)
variable (Q:Pace.Coin)(h:Q 0=0)(L j:ℕ) (g d : ℝ)
local notation "Y"=> (Mutation.stamp X Q h L j)
local notation "Z"=> (rendered X B g)
local notation "C"=> (rendered Y B d)
abbrev defect (i:ι):ℝ:= Balance.balance Q h L (X i).lamp.lag g d (j-(X i).lamp.e)
local notation "κ"=> (Mutation.defect X Q h L j g d)

/-- Retains ALL old labels including frame, e_Q not analyzed by recalibration. -/
def mend : Lamps W ι G B P.origin R where
   mode i:= (X i).mode
   live := (Z).live
   address := (Z).address
   roots := (Z).roots
   nominal x i:= ( κ i : ℂ) • (X i).nominal g x
   legal x i:= regular_smul _ ((X i).legal B g x)
   clear := (Z).clear
   pure x i U h:= congr_arg ( ( κ i : ℂ ) • · ) ((Z).pure _ _ U h)
local notation "D"=> (Mutation.mend X B Q h L j g d)
variable (g0:g≠0)(hd:d≠0)
-- weighted size.Purchasing whole currency; no free trunc.
variable (w:V→ℝ)(t:V→ℕ){k u:ℕ}{a c U ν z x r b τ ε θ θ':ℝ}
variable (H: Recharged Q h g d L j u a ν z)
variable (A: Earn.Scene.Armada X w t x c j k u)
variable (hU:Invoice.Supports B U b g x τ) (hz :0≤ν)
local notation "T"=> (Invoice.price B U (j+u+1) k b τ G)
include H A hU hz
lemma wage : (Mutation.mend X B Q h L j g d).Paid w B.B b (ν*T*c):=by
    let f i:= |κ i| * (X i).charge B g; have he i:0≤f i:= mul_nonneg (abs_nonneg _) (show 0 ≤ (X i).charge B g from (mul_nonneg (mul_nonneg (by positivity) ((X i).real_quote B g).1) (X i).sound.le)); refine ⟨f,he,?_, ?_⟩
    · intro i t y hy; have ht:= bound_smul (κ i:ℂ) ((X i).supported B g t y (A.honor i) hy); rw [Complex.norm_real, Real.norm_eq_abs] at ht; exact ht
    intro v; have hs := Mutation.valid X Q h L j w t H A; let b' i:= (X i).lamp; have hg i: 0≤g^( b' i ).e:= pow_nonneg hU.1.le _;
    have hc i:|κ i| *g^(X i).lamp.e≤ ν:=by
       have ht:=H.earns _ (A.purchases.usable i).1 (hs i).1; rw [abs_mul,abs_of_nonneg (hg i),mul_comm] at ht; exact ht
    let f0 i := if v∈ (X i).ground B then |κ i| * Invoice.income B X w g i * Real.exp (b* coverNumber B.B ((X i).ground B) ) else 0; have hx0 : SumBudget f0 (ν*T*c) := by simpa only [Nat.zero_le, ↓reduceIte, pow_zero, mul_one] using Invoice.taxes B U X w A.positive _ k hU A.suggests A.purchases.spend (fun i=> (hs i).2.2) (fun i=>A.quota _) (κ) ν hz hc 0 v;
    convert hx0 using 1; ext i; unfold f0; rw [show (D).ground i=(X i).ground B from rfl]; split
    ·  change Poly.toll w (X i).mode * (|κ i| * ((X i).charge B g))* _= _; unfold Invoice.income; ring
    · rfl
omit H A hU hz
-- point renewal at ALL fields. Note U may violate masks; keep emissions on BOTH sides identical
include g0 hd
lemma letters (i:ι)(p:W)(U: Config G n) : (X i).nominal g p U = (∑ j':ways X j i, ( Mutation.stamp X Q h L j ⟨i,j'⟩ ).nominal d p U ) + (Mutation.mend X B Q h L j g d).nominal p i U:=by
    let a':= (X i).lamp.lag; let x':= (X i).atom.unmasked U (X i).center
    let m:= j-( X i ).lamp.e; let H'(r:ℕ):= (tariff Q h L a' r :ℝ) * d^(a'+(r:ℤ)); have hx': g^a'= (∑ i∈range (m+1),H' i)+ κ i*g^a':= Balance.renewed Q h L a' g d m g0 hd
    let t':=(X i).paint p; let α := (fun k:ways X j i=> (Mutation.stamp X Q h L j ⟨i,k⟩).nominal d p U); have he (k:ways X j i): α k=t'* ((H' k.val*x':ℝ):ℂ):= by unfold α; unfold Row.nominal Row.grain; rw [Mutation.billed]; unfold H'; push_cast; change (↑(tariff Q h L a' k.val) * t') * ( ↑d ^ (a'+(k.val:ℤ)) * (x':ℂ) ) = _; ring
    change t'* ((g^a'*x':ℝ):ℂ) = (∑ j', α j') + (κ i:ℂ)* (t'* ((g^a'*x':ℝ):ℂ)); simp_rw [he]; rw [ Fin.sum_univ_eq_sum_range (fun i:ℕ=>t' * ((H' i*x':ℝ):ℂ)) (m+1), ← Finset.mul_sum, ← Complex.ofReal_sum, ← Finset.sum_mul, show (∑ j∈_, H' j)= g^a'- κ i *g^a' from eq_sub_of_add_eq hx'.symm ]; push_cast; ring
-- Gather each masked for just its own frame.
lemma price (i:ι) (p:W) (U:Config G n) : ( rendered X B g ).light p i U= (∑ u:ways X j i, ( rendered (Mutation.stamp X Q h L j) B d ).light p ⟨i,u⟩ U)+ (Mutation.mend X B Q h L j g d).light p i U:=by
    have hs:= letters X B Q h L j g d g0 hd i p U;
    unfold Lamps.light; by_cases he: (X i).clear; · simpa only [rendered, mend, Mutation.stamp, he,dite_true, ↓reduceIte,Pi.smul_apply] using hs
    change (if (X i).clear then _ else masked B.threshold ((X i).ground B) _ U) = (∑ j:Mutation.ways X j i, if (X i).clear then _ else masked B.threshold ((X i).ground B) _ U)+(if (X i).clear then _ else masked B.threshold ((X i).ground B) _ U) -- shadow! implicit metavars
    simp_rw [if_neg he]
    by_cases hv:Healthy B.threshold ((X i).ground B) U
    · simp_rw [masked_eq _ _ _ _ hv]; exact hs
    simp_rw [masked_ne _ _ _ _ hv]; simp
lemma frame (i:ι)(p:W)(U:Config G n): ( rendered X B g ).frame i p U = (∑ k:ways X j i, ( rendered (Mutation.stamp X Q h L j) B d ).frame (⟨i,k⟩: Mutation.Names X j) p U) + (Mutation.mend X B Q h L j g d).frame i p U:=by
    ext1 k; simp only [Lamps.frame,Poly.part_plus,Poly.part_send, Poly.part_sum] -- check
    change ( if k=(X i).mode then _ else 0)=(∑ s:ways X j i, if k=(X i).mode then (C).light p ⟨i,s⟩ U else 0) +(if k=(X i).mode then _ else 0); by_cases he:k=(X i).mode; · simp_rw [if_pos he]; exact Mutation.price X B Q h L j g d g0 hd i p U
    simp_rw [if_neg he, sum_const_zero,add_zero]
end YM.QuadraticLocal.Rebirth.Mutation
