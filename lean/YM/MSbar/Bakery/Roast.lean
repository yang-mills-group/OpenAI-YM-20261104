import YM.MSbar.Cacao.Coda
import YM.MSbar.Bakery.Power
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bakery
open Function Filter Finset Cacao MeasureTheory Whisk PowerSeries
open scoped Topology BigOperators Classical ContDiff
variable {σ ι :Type}[Fintype σ] [DecidableEq σ]
open Lattice MvPolynomial Analysis Set Metric
local notation "P"=>Pot σ
local notation "V"=>View σ
local notation "µ"=>PowerSeries.coeff
variable {x y :View σ}{f F : PowerSeries (Pot σ)}{X:Set (View σ)}{p m k q j :ℕ}{u t a r b:ℝ} {n:Side}{l:σ→ Site n}{Y W:Finset (Site n)}
variable (K: σ→σ→ℝ)
-- constant difference on outputs
lemma lease_h (A B :PowerSeries P)(h:Kind A)(hx:Kind B)(v:PowerSeries ℝ)(he:∀ i,µ i A=µ i B + MvPolynomial.C (µ i v)) (j n:ℕ):
     Ride A K n j = Ride B K n j + if j=0 then MvPolynomial.C (µ n v) else 0:=by
    suffices H :∀ k i n:ℕ,i≤k → Ride A K n i=Ride B K n i+ if i=0 then MvPolynomial.C (µ n v) else 0 by exact H j j n le_rfl
    intro k'; induction k' with
    | zero=> intro i m hi; rw [Nat.eq_zero_of_le_zero hi,Ride,Ride,Cacao.began h,Cacao.began hx];simpa using he m
    | succ k' ih=>
        intro i m hi; by_cases he:i ≤ k'; exact ih i m he
        rw [show i=k'+1 by omega,Whisk.lamp m _ _ h,Whisk.lamp m _ _ hx]; rw [if_neg (by omega), add_zero, ih k' _ (le_refl _),_root_.map_add,show (stove K) (if k'=0 then MvPolynomial.C (µ m v) else 0)=0 from ?_, add_zero]; swap;· split <;> first|exact _root_.map_zero _|exact dry K (by simp)
        have hp (i:ℕ)(h:i ≤ k')(m:ℕ)(j:σ): (pderiv j) (Ride A K m i)= pderiv j (Ride B K m i):=by rw [ih i m h,map_add]; split <;> simp
        have hv:tolly A K m k'=tolly B K m k' := by
           unfold tolly; apply sum_congr rfl; intro d _; apply sum_congr rfl; rintro ⟨i₁,i₂⟩ he; have ht:i₁+i₂=k':=mem_antidiagonal.mp he; dsimp only; unfold juncture; simp_rw [hp i₁ (by omega), hp i₂ (by omega)]
        rw [hv]
lemma dots (A B :PowerSeries P)(h:Kind A)(hx:Kind B)(v:PowerSeries ℝ)(he:∀ i,µ i A=µ i B + MvPolynomial.C (µ i v)) (n:ℕ):
     µ n (confect K A)=µ n (confect K B)+ MvPolynomial.C (µ n v) :=by
    let Ca:= µ n (normalized K A); let D:=µ n (normalized K B)
    have ht:Ca=D+ Polynomial.C (MvPolynomial.C (µ n v)) :=by apply Polynomial.ext; intro i; rw [Polynomial.coeff_add,Polynomial.coeff_C]; exact lease_h K A B h hx v he i n
    unfold confect; rw [PowerSeries.coeff_map,PowerSeries.coeff_map, show µ n (normalized K A)= _ from ht, _root_.map_add,show ePeak.toRingHom (Polynomial.C _)=_ from ?_]; rw [show ∀ p:Ball σ,ePeak.toRingHom p=Polynomial.eval 1 p from fun p=>rfl]; rw [Polynomial.eval_C]
lemma absorbed (F G Y :PowerSeries P)(h:Kind F)(hp:Kind G) (v: PowerSeries ℝ)(he:∀ i,µ i F=µ i G + MvPolynomial.C (µ i v))(r:ℕ)(hr:0<r): growP F Y K r=growP G Y K r:=by
    let f:=F+PowerSeries.X^r*Y;let g:=G+PowerSeries.X^r*Y; have hF:= ripple h Y r hr; have hG:=ripple hp Y r hr
    have hz :∀ i,µ i f=µ i g+ MvPolynomial.C (µ i v):=fun i=>by unfold f g;rw [_root_.map_add,_root_.map_add,he i];abel
    apply PowerSeries.ext; intro i; simp only [growP,Scan,PowerSeries.coeff_mk,_root_.map_sub]; rw [dots K F G h hp v he,dots K f g hF hG v hz]; abel
-- subtract reference. No volume scalar claims on f.
def rewind (f:PowerSeries P)(x:View σ):= (fun n=>µ n f - MvPolynomial.C (MvPolynomial.eval x (µ n f)))
def Rewind (f:PowerSeries P)(x:View σ):= PowerSeries.mk (rewind f x)
lemma hush (hf:Kind f) : Kind (Rewind f x):=by rw [Kind,Rewind,PowerSeries.coeff_mk,rewind,hf,_root_.map_zero,_root_.map_zero,sub_zero]
lemma slow (F Y:PowerSeries P)(h:Kind F)(r:ℕ)(hr:0<r)(x:View σ): growP F Y K r= growP (Rewind F x) Y K r := absorbed K F (Rewind F x) Y h (hush h) (PowerSeries.mk (fun j=>MvPolynomial.eval x (µ j F))) (fun i=> by rw [Rewind,PowerSeries.coeff_mk,PowerSeries.coeff_mk,rewind,sub_add_cancel]) r hr
end YM.MSbar.Bakery
