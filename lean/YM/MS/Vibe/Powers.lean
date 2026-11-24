import YM.MS.Vibe.Link
/-!
# Separating ℓ by y; no real Re ordering demanded (weights complex)
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Emit
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock
open Signal Book Convolve Garment.Wave Garment.Wick
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{X Y F:T ( Flats G )}{V:Flats G}{t r:ℤ}{a h n m k ℓ:ℕ}{i:ℂ}{s y:ℝ}{b:Bool}
private def shines (S:Finset ℕ)(i:ℂ)(v:ℕ→ℂ): Prop:=∀ y, ∑ j∈ S, (Pearl.weight i j y) * v j=0
lemma fits (z:ℂ)(x y:ℕ)(he:toll z x=toll z y)(hz:z≠0): x=y:= by apply Nat.cast_injective (R:=ℂ); exact mul_left_cancel₀ (mul_ne_zero (by norm_num) hz) he
lemma squash (i:ℂ)(hp:i≠0)(S:Finset ℕ)(v:ℕ→ℂ)(hx:shines S i v): ∀ p∈ S,v p=0:= by
    induction S using Finset.induction generalizing v with
    | empty=> simp
    | insert j S h ih=>
       let u n:= (toll i n - toll i j)*v n; let T:= insert j S; have he: shines S i u:= by
         intro y; have hv := HasDerivAt.fun_sum (u:=T) (x:=y) (fun n _=>(amountD (toll i n) y).mul_const (v n)); -- names
         rw [show (fun y=> ∑ n∈ T, amount ( toll i n ) y * v n)=(fun _:ℝ=>0) from funext hx] at hv; have ht:= hv.unique ( hasDerivAt_const y 0);
         have hu:= calc
           ∑ n∈T, (Pearl.weight i n y)*u n = (∑ n∈ T, (toll i n)*amount (toll i n) y*v n) - (toll i j)*(∑ n∈T, (Pearl.weight i n y)*v n) := by rw [Finset.mul_sum,← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro n hn; unfold u Pearl.weight; ring
           _= 0 := by unfold T; rw [ht, hx y]; simp
         unfold T at hu; rw [Finset.sum_insert h, show Pearl.weight i j y * u j=0 by simp [u], zero_add] at hu; exact hu
       obtain ht:=ih u he; have hS : ∀ p∈ S,v p=0:= by
            intro p hp'; by_contra hc; exact h ((fits i p j (sub_eq_zero.mp ((mul_eq_zero.mp (ht p hp')).resolve_right hc)) hp) ▸ hp')
       intro p hp; rcases Finset.mem_insert.mp hp with rfl|hx'; · obtain hx:= hx 0; rw [Finset.sum_insert h,Finset.sum_eq_zero] at hx; simpa [Pearl.weight, amount] using hx; intro b hb; simp [hS b hb]
       exact hS _ hx'
-- resolve equality across same ℓ = not two sums variable. shrink rank support known.
lemma settle (V:Flats G)(hp:i≠0)(w:Legs (Shore G m))(T:ℝ)(hS:∀ y, Parade V h y T i m w= Parade V h y 0 i m w): ∀ ℓ, plow (vamp i h ℓ) T (V ℓ i) m w= V ℓ i m w:= by
    let f (ℓ):= plow (vamp i h ℓ) T (V ℓ i) m w- V ℓ i m w; have he: shines V.support i f:= by intro y; unfold Parade Finsupp.sum at hS; simp only [Finset.sum_apply,hikeP, posing, Pi.smul_apply, smul_eq_mul] at hS; simp_rw [f,mul_sub,Finset.sum_sub_distrib]; rw [hS y, sub_self]
    intro j; by_cases ht:j∈V.support; · exact sub_eq_zero.mp ( squash i hp _ f he j ht )
    simp [Finsupp.notMem_support_iff.mp ht, ← cert]
end YM.MS.Emit
