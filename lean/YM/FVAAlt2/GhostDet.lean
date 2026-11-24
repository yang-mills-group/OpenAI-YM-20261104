import YM.FVAAlt2.Pauli

/-!
# Integrate the Grassmann part of the physical MS covariance by exact Wick calculations.

For each `Silent` external multiplicative argument (`∂ψ` zero for
that specific row, may still depend on θ or on other rows) multiplying by
`θᵢ ψᵢ` gives equality under the **Wick** functional with the whole bosonic
and odd covariance. This permits us to install the unit in all missing rows
prior to rearranging (and remove the pure saturated unit afterwards).
Quantified coefficientwise on the full algebra includes nonzero external
moments and common vacuum denominator. `Ticket` applies to canonical data later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Glue
open Finset Function MeasureTheory
open MS MS.Koszul MS.Native MS.Plane MS.Book MS.Cylinder MS.Puff MS.Puff.Actors MS.Swirl MS.Puff.Mom MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal
open scoped PowerSeries ContDiff
open Lattice Pert.Orb SchemeRG11.Sway
variable {G:Gauge}{n:Side}{ι κ:Type}[Fintype ι][DecidableEq ι][Fintype κ][DecidableEq κ]
variable (A:Module.Basis ι ℝ (Land G n))
set_option linter.unusedSectionVars false
local notation "S" => Alpha ι κ
local notation "p" => isOdd (ι:=ι) (κ:=κ)
local infix:70 " ⋄ " => product p
local notation "K" => propagator (κ:=κ) A
local notation "Γ'" => landLaw G n
local notation "E" => Com p
local notation "T" => PowerSeries (Com p)

lemma prop_entries(i j : Alpha ι κ): Chill (propagator A) i j=Rcov A i j := by unfold propagator Chill; simp
lemma chrClear: Clear p K:= by
 rintro (i|i|i) (j|j|j) h <;> first|rfl| (exfalso; apply h; simp [propagator,Rcov,Rgh])
lemma chrSym : Cog.Sym p K := by
 have he (i j:ι): (Γ').wick (A.coord i) (A.coord j) = (Γ').wick (A.coord j) (A.coord i):= by
    rw [show (Γ').wick (A.coord i) (A.coord j)=(Γ').P ((Γ').inverse (A.coord j)) ((Γ').inverse (A.coord i)) from by rw [PertExtension.GaussianScore.Law.applies]; rfl, PertExtension.GaussianScore.Law.turns, PertExtension.GaussianScore.Law.applies];rfl
 rintro (i|i|i) (j|j|j) <;> simp [propagator, Matrix.smul_apply, Rcov,Rgh,isOdd,cross]
 · rw [he]
 all_goals by_cases hx:i=j <;> simp [hx,eq_comm]

lemma saturation (x:Com p)(i:κ)(h:Stops i x):
    View K (pairG ι i i*x).val= View K x.val:= by
 rw [Com.mul_val,spelled, Koszul.times_assoc]
 rw [theta, ibpV (F:=psi ι i ⋄ x.val) («p»:=p) _ (chrClear A) (chrSym A) ((speaks_s _).times (Com.sym x)) (miPair (minH (letterN _)) (Com.small x)),Fintype.sum_sum_type,Fintype.sum_sum_type]
 simp_rw [prop_entries]
 -- calculate exactly ∑ odd. Δ sign
 simp [Rcov,Rgh]; rw [D_product,hear, show D _ _=0 from h,map_zero,add_zero,coin_product,one_smul] -- define ψhear

def Silent (i:κ)(x:T): Prop:=∀ j, Stops i (PowerSeries.coeff j x)
namespace Silent
variable {B:Type} {x y:PowerSeries (Com (isOdd (ι:=ι) (κ:=κ)))}{i:κ}
lemma coeffConst {x:E} (h:Stops i x): Silent i (PowerSeries.C x) := by intro n; rw [PowerSeries.coeff_C]; split; exact h; exact stop_zero _
lemma zero (i:κ) : Silent i (0:T) := by intro n; rw [map_zero]; exact stop_zero _
lemma one : Silent i (1:T) := by rw [← map_one PowerSeries.C]; exact coeffConst (stop_one i)
lemma add (hx: Silent i x)(hy: Silent i y): Silent i (x+y) := by intro n; rw [map_add]; exact stop_add (hx n) (hy n)
lemma mul (hx: Silent i x)(hy: Silent i y): Silent i (x*y) := by intro n; rw [PowerSeries.coeff_mul]; exact stop_sum _ _ (fun _ _=> stop_mul (hx _) (hy _))
lemma smul (hx: Silent i x)(z:ℂ): Silent i (z • x) := by intro n; rw [PowerSeries.coeff_smul]; exact stop_smul (hx n) z
lemma pow (hx: Silent i x)(n:ℕ):Silent i (x^n):= by induction n with| zero=> rw [pow_zero]; exact one| succ n ih=> rw [pow_succ]; exact ih.mul hx
lemma exp (hx: Silent i x): Silent i (formExp x):= by intro n; rw [formExp_coeff]; exact stop_sum _ _ (fun l _=>stop_smul (hx.pow l n) _)
lemma sum (s:Finset B){f:B→PowerSeries (Com p)}(h:∀ j∈s,Silent i (f j)): Silent i (∑ j∈s,f j):= by intro n;rw [map_sum]; exact stop_sum _ _ (fun k hk=> h k hk _)
lemma prod (s:Finset B){f:B→PowerSeries (Com p)}(h:∀ j∈s,Silent i (f j)): Silent i (∏ j∈s,f j):= by
 classical
 induction s using Finset.induction with| empty=> rw [Finset.prod_empty]; exact one| insert i s hi ih=> rw [Finset.prod_insert hi]; exact mul (h _ (mem_insert_self ..)) (ih fun i hi=> h i (mem_insert_of_mem hi))
end Silent

def wick : PowerSeries (Com p) →ₗ[ℂ] (ℕ→ℂ) := (ℶV K).comp (Com.forget p)
def Ω (i j:κ):T:= PowerSeries.C (pairG _ i j)
lemma wick_at (x:T)(j:ℕ) : wick A x j= View K (PowerSeries.coeff j x).val:=rfl
lemma saturates (i:κ) (x:T)(h: Silent i x): wick A (Ω i i*x)= wick A x:= by
 funext j; rw [wick_at,wick_at,Ω,PowerSeries.coeff_C_mul,saturation A _ i (h j)]


lemma bar2 (i j k:κ) : Ω (ι:=ι) i j * Ω i k=0:= by rw [Ω,Ω,← map_mul,same_bar,map_zero]
lemma ghost2 (i j k:κ) : Ω (ι:=ι) j i * Ω k i=0:= by rw [Ω,Ω,← map_mul,same_ghost,map_zero]
lemma flipΓ (i j k l:κ): Ω (ι:=ι) i j * Ω k l= -(Ω i l*Ω k j):= by simp only [Ω,←map_mul,←map_neg]; rw [swap_ghost i j k l]

variable (b:Matrix κ κ (PowerSeries (Com (isOdd (ι:=ι) (κ:=κ))))) -- b from exponent without free part
local notation "ℱ" => PowerSeries.coeff (R:=E)

def debit (i:κ): T:= ∑ j:κ, Ω i j*b i j
lemma nilRow(i:κ): debit b i * debit b i=0:= by
  unfold debit; simp_rw [Finset.sum_mul,Finset.mul_sum]; exact sum_eq_zero fun j _=> sum_eq_zero fun k _=> by rw [mul_mul_mul_comm,bar2]; simp
lemma row_shape (i:κ): Ω i i + debit b i=∑ j,Ω i j* (1+b) i j:= by
  unfold debit; simp [mul_add,sum_add_distrib,Matrix.one_apply] -- idem
lemma elect : ∏ i:κ,(Ω i i + debit b i)=(∏ i:κ,Ω i i)* (1+b).det:= by
  simp_rw [row_shape]; exact determinant (fun i j=> Ω i j) (fun i j k=> ghost2 k i j) (fun i j k l=> flipΓ i k j l) _
lemma clean_one {i j:κ}(k:κ)(h:i≠j): Silent i (Ω (ι:=ι) j k):= Silent.coeffConst (stop_other k h)
variable (H:∀ i j k, Silent i (b j k))
include H in
lemma clean_row {i j:κ}(h:i≠j): Silent i (debit b j):= Silent.sum _ (fun _ _=> Silent.mul (clean_one _ h) (H _ _ _))

private lemma render (f g:κ→T)(s:Finset κ)(hp:∀ i j,i≠j→ Silent i (f j))(he:∀ i j,i≠j→ Silent i (g j))
    (ht:∀ i (x:T), Silent i x → wick A (f i*x)=wick A (g i*x))(x:T)(hx:∀ i∈s,Silent i x):
    wick A ((∏ i∈s,f i)*x) = wick A ((∏ i∈s,g i)*x):= by
  induction s using Finset.induction generalizing x with
  | empty=> rw [prod_empty,prod_empty]
  | insert a s ha ih=>
    rw [prod_insert ha,prod_insert ha]; have hy:=fun i hi=> hx i (mem_insert_of_mem hi)
    have hn:∀ i∈s,a≠i:=fun i hi h=>ha (h ▸ hi)
    rw [mul_assoc,ht a _ (Silent.mul (Silent.prod _ fun i hi=> hp a i (hn i hi)) (hx a (mem_insert_self ..))),← mul_assoc,mul_comm (g a),mul_assoc,ih (x:=g a*x) (fun i hi=> (he i a (hn i hi).symm).mul (hy i hi)),mul_left_comm, ← mul_assoc]

lemma row_stamp {i:κ}{x:T}(h: Silent i x): wick A ((1+debit b i)*x)=wick A ((Ω i i+debit b i)*x):= by rw [add_mul,add_mul,map_add,map_add,one_mul,saturates _ _ x h]

variable (hc:∀ i j, PowerSeries.constantCoeff (b i j)=0)
include hc in
lemma debit0 (i:κ): ℱ 0 (debit b i)=0:= by simp [debit,hc]

include hc H in
/-- This integrates the determinant of the full matrix after a common formal
change. Applies after multiplying by other bosonic exponentials/products.
No cancellation or rectangular projection outside its own `b` matrix. -/
theorem determinant_rule (x:T)(hx:∀ i, Silent i x): wick A (formExp (∑ i:κ,debit b i)*x) = wick A ((1+b).det*x):= by
  rw [Com.exp_sum («p»:=p) _ (fun i _=>debit0 _ hc i)]; simp_rw [ show ∀ i:κ,formExp (debit b i)= _ from fun i=>formExp_sq (debit0 b hc i) (nilRow b i) ]
  rw [render A (fun i=>1+debit b i) (fun i=> Ω i i+debit b i) _ (fun i j h=>Silent.one.add (clean_row b H h)) (fun i j h=> (clean_one _ h).add (clean_row b H h)) (fun i x hi=>row_stamp A b hi) x (fun i _=>hx i), elect, mul_assoc]; -- erase unit rows
  have hh(i:κ): Silent i ((1+b).det*x):= by
    have hg(j k:κ): Silent i ((1+b) j k):= by simp only [Matrix.add_apply,Matrix.one_apply]; refine Silent.add ?_ (H _ _ _); split; exact Silent.one; exact Silent.zero _ -- notation stuck
    apply Silent.mul _ (hx i); rw [Matrix.det_apply']; -- inspect
    apply Silent.sum; intro p₀ _; refine Silent.mul ?_ (Silent.prod _ (fun j _=> hg _ _)); rcases Int.units_eq_one_or (Equiv.Perm.sign p₀) with he|he <;> simp [he]; exact Silent.one; -- need neg
    exact fun n=> by rw [map_neg]; change D _ (-_) = _; rw [map_neg,show D _ _=0 from Silent.one n,neg_zero]
  have he:= render A (fun i:κ=>Ω i i) (fun _=>1) univ (fun _ i h=> clean_one i h) (fun _ _ _=> Silent.one) (fun i t hi=> (saturates A i t hi).trans (by rw [one_mul])) _ (fun i _=> hh i)
  simpa using he
end YM.FVAAlt2.Glue
