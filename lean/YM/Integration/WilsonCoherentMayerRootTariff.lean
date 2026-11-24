import YM.WilsonCoeffUV.Reclosure.Revenue
import YM.WilsonCoeffUV.Thermo.Tariff

/-! Absolute prices of the Taylor coefficients of a single rooted old action atom. -/

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section
namespace YM.Integration.WilsonCoherentMayerRootTariff
open Filter Finset Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Work.F08
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic.Near
open scoped BigOperators
variable {G:Gauge}{f:Side}{h:ℕ}{σ:ℝ}

def price (G:Gauge)(σ:ℝ)(h:ℕ): ℕ→ℝ
  | 0=>flour G σ h 0
  | j+1=>flour G (σ/2) h (j+1)*(boardPay (Hooks G) ((σ/2)/(j+1)))^(j+1)

private theorem fair (a:Atom G h)(hs:0<σ)(x:Site f)(j:ℕ)(w:Fin (j+1)→Woods G f):
    ‖rye (meter a x) (j+1) w‖≤
      (a.budget σ*flour G (σ/2) h (j+1))*sail ((σ/2)/(j+1)) (tor f) x w:=by
  have hw:0≤a.budget σ:=by unfold Atom.budget Atom.magnitude;positivity
  have hf:=flour_nn G (σ/2) h (j+1)
  by_cases ne:rye (meter a x) (j+1) w=0
  · rw [ne,norm_zero];exact mul_nonneg (mul_nonneg hw hf) (sail_nn x w)
  have ss:0<σ/2:=by positivity
  have cut:=sail_cut (d:=tor f) (σ:=σ/2) (η:=0) (v:=0) (l:=a.length) (Nat.zero_le _) (le_refl _) ss (Nat.zero_lt_succ j) x w (belonging a x w ne)
  simp only [neg_zero,zero_mul,Real.exp_zero,one_mul,sub_zero,Nat.cast_succ] at cut
  calc
    _ ≤ a.budget (σ/2)*flour G (σ/2) h (j+1):=flourished a x ss w
    _ = (a.budget σ*flour G (σ/2) h (j+1))*Real.exp (-(σ/2)*(a.length:ℝ)):=by
      have split:Real.exp (σ/2*(a.length:ℝ))=Real.exp (σ*(a.length:ℝ))*Real.exp (-(σ/2)*(a.length:ℝ)):=by
        rw [←Real.exp_add];congr 1;ring
      unfold Atom.budget;rw [split];ring
    _ ≤ _:=mul_le_mul_of_nonneg_left cut (mul_nonneg hw hf)

theorem coefficients (a:Atom G h)(hs:0<σ)(x:Site f)(j:ℕ):
    ∑ w:Fin j→Woods G f,‖rye (meter a x) j w‖≤a.budget σ*price G σ h j:=by
  cases j with
  | zero=>
    let w:Fin 0→Woods G f:=fun i=>i.elim0
    rw [Finset.sum_eq_single w (fun b _ hb=>(hb (Subsingleton.elim b w)).elim) (fun hb=>(hb (mem_univ w)).elim),price]
    exact flourished a x hs w
  | succ j=>
    have hw:0≤a.budget σ:=by unfold Atom.budget Atom.magnitude;positivity
    have hs':0<(σ/2)/(j+1):=by positivity
    calc
      _ ≤ ∑ w:Fin (j+1)→Woods G f,(a.budget σ*flour G (σ/2) h (j+1))*sail ((σ/2)/(j+1)) (tor f) x w:=
        sum_le_sum (fun w _=>fair a hs x j w)
      _ = _:=Finset.mul_sum .. |>.symm
      _ ≤ a.budget σ*flour G (σ/2) h (j+1)*(boardPay (Hooks G) ((σ/2)/(j+1)))^(j+1):=
        mul_le_mul_of_nonneg_left (train_native hs' x (j+1)) (mul_nonneg hw (flour_nn ..))
      _ = _:=by rw [price,mul_assoc]

end YM.Integration.WilsonCoherentMayerRootTariff

