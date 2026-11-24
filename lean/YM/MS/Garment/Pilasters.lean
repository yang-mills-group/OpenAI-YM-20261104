import YM.MS.Garment.Suave
/-!
# Full typeset of actual Wick symbol supports

Lemma horizon_D, D0 scaled limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Garment.Wick
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps
open Momentum Metric City Color
open scoped Topology ContDiff
open Complex (I)
variable {G:Gauge}{A C:Type}[Fintype A][DecidableEq A] [Fintype C][DecidableEq C]{m n:ℕ}
variable (X: Spin A)
lemma realW (t:ℝ) : TestPass X ( line t):= by
    have h (p: Momentum A)(a b:Atom A): line t a b p=(t:ℂ)*L0 t a b p:= ( brushed ..).symm
    intro p i j; simp_rw [h,mul_assoc (t:ℂ),mul_left_comm _ (t:ℂ),← Finset.mul_sum]; apply congr_arg; have hb : City.brush t (X.turn p)=City.brush t p:= by unfold City.brush; rw [X.fare]
    rcases i with ⟨_|i,_|_⟩ <;> rcases j with ⟨_|j,_|_⟩ <;> simp [Fintype.sum_option,Fintype.sum_prod_type,shadow,rayS,L0,hb,X.fare]
    · simp_rw [mul_assoc,← Finset.mul_sum,← Complex.ofReal_mul,← Complex.ofReal_sum,X.orth]; push_cast; rfl
    · simp_rw [mul_assoc (a:=((City.brush t p):ℂ)),← Finset.mul_sum,← Complex.ofReal_mul,← Complex.ofReal_sum, carry]; rw [← Complex.ofReal_mul, Finset.mul_sum]; exact congr_arg Complex.ofReal (Finset.sum_congr rfl fun i hi=> mul_left_comm ..)
    simp_rw [mul_left_comm (X.profile i _:ℂ) Complex.I, mul_left_comm (X.profile i _:ℂ) ↑(City.brush t p), mul_left_comm (X.profile i _:ℂ) ↑p.sq, ← Finset.mul_sum,← Complex.ofReal_mul, ← Complex.ofReal_sum,X.dual i,mul_comm (X.back.profile _ i) (X.turn p _), X.back.orth, rear]; simp
lemma cur_r (c:ℝ→ℝ): TestPass X (laplace (fun p=> c p.sq)):=by
   intro p i j; rcases i with ⟨_|i,_|_⟩ <;> rcases j with ⟨_|j,_|_⟩ <;> simp [Fintype.sum_option,Fintype.sum_prod_type,shadow,rayS,laplace, X.fare,delta,apply_ite,ite_mul, div_eq_mul_inv] <;> ring

lemma Cert0 (G:Gauge) : CountsD true (Q G) where
   spin n X hx i j p:=by -- parameters order?
       exact regular_copy X (trial_q X) i j p
   wall h i j p:= by -- prefix
       unfold Q Landau.send; unfold choir; rcases i with ⟨⟨_|i,_|_⟩,k⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,c⟩ <;> first| rfl| (simp [embA,Landau.bare,precision,sq_up,delta, Left,lasts])
end YM.MS.Garment.Wick
