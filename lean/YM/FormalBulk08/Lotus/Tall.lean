import YM.FormalBulk08.Lotus.Plot

/-! Dominated limits. Use individual coefficients uniformly in period. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Lotus
open Lava Gorge Lattice Laurent Bloch Filter Set Function Wick
open scoped BigOperators Classical ENNReal Topology
variable {I J : Type*} {η C : ℝ} {r : ℕ}
lemma half_norm (x : ℝ) : ‖halve x‖=1/2*‖x‖:= by unfold halve; rw [norm_mul]; norm_num
lemma palmed {n : Side} {T : Tile (Tor n I) r} (h : Bail (lake n I) η T C) (w : chain (Tor n I) r) (i : Fin r) : Real.exp (η*wide (lake n I) w)*‖T w‖≤ C := by
   have e := h.seen w i
   unfold glitter shine at e; rw [←ofReal_norm,←ENNReal.ofReal_mul (Real.exp_pos _).le] at e;exact (ENNReal.ofReal_le_ofReal_iff h.1).mp e
lemma grove {n : Side} {M : Tor n I→Tor n I→ℝ} (h : Grate (lake n I) η M C) (x y) : Real.exp (η*skit n (x.1-y.1)) * ‖M x y‖≤ C := by
   have e:=(ENNReal.le_tsum (f:=fun v=>shine η ((lake n I).d x v)*‖M x v‖ₑ) y).trans (h.2 x); unfold shine at e; rw [←ofReal_norm,← ENNReal.ofReal_mul (Real.exp_pos _).le] at e; exact (ENNReal.ofReal_le_ofReal_iff h.1).mp e

def coast (η : ℝ) (v : Biglot I):= Real.exp (-η*size v.1)
lemma coast_sum [Fintype I] (hp : 0<η) : Summable (coast (I:=I) η) := by
   apply from_evil (C:=(Fintype.card I)*((2*((1+η)/η))^(Fintype.card Axis))) (by positivity) (fun i=> (Real.exp_pos _).le) ?_ |>.1
   rw [ENNReal.tsum_prod',ENNReal.tsum_comm,←dust_cost I]; refine ENNReal.tsum_le_tsum fun i=>?_; have e:=Width.compactPay (α:=Axis) η hp
   dsimp only; rw [← ENNReal.ofReal_tsum_of_nonneg e.1 e.2.1]; exact ENNReal.ofReal_le_ofReal e.2.2
lemma coast_pair [Fintype I] [Fintype J] (hp : 0<η) : Summable (fun i : Biglot I × Biglot J=> coast η i.1 * coast η i.2) := by
   apply Summable.mul_of_nonneg (coast_sum hp) (coast_sum hp) (fun i=> (Real.exp_pos _).le) (fun i=> (Real.exp_pos _).le)

lemma sloped (K B : ℕ) (n : Side) (x y : Tor n I) (u : ℝ) (h : skit n x.1 + skit n y.1 ≤ 2*B+2*K) (e : Real.exp (η*B)*‖u‖ ≤ C) (hs : 0≤η):
     ‖u‖ ≤ Real.exp (η*K)*C* (coast (η/2) (boil n x)*coast (η/2) (boil n y)) := by
   have hp : Real.exp (-(η*B)) ≤ Real.exp (η*K) * (coast (η/2) (boil n x)*coast (η/2) (boil n y)) := by
      unfold coast;rw [←Real.exp_add,←Real.exp_add]; apply Real.exp_monotone;change -(η*B)≤ η*K+(-(η/2)*(skit n x.1)+-(η/2)*(skit n y.1)); have hy : (skit n x.1:ℝ)+skit n y.1 ≤ 2*B+2*K:= by exact_mod_cast h
      nlinarith
   have hc: 0≤C:= (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)).trans e
   calc
     _ = Real.exp (-(η*B))*(Real.exp (η*B)*‖u‖):= by rw [←mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul]
     _ ≤ Real.exp (-(η*B))*C := mul_le_mul_of_nonneg_left e (Real.exp_pos _).le
     _ ≤ _ := by rw [mul_right_comm (Real.exp (η*K))]; exact mul_le_mul_of_nonneg_right hp hc

lemma height_pair {T : Tile (Biglot I) (r+1+1)} {P : (n:Side) → Tile (Tor n I) (r+1+1)}
   {q : Biglot I → Biglot I→ℝ} {M : (n:Side)→ Tor n I → Tor n I → ℝ}
   (ht : Light T P) (e : Wind q M) (v : chain (Biglot I) r) (x : Biglot I × Biglot I) :
      Tendsto (fun n=> telescopeTerm (M n) (P n) (drip n ∘ v) (drip n x.1,drip n x.2)) atTop (𝓝 (telescopeTerm q T v x)) := by
   have hv (n:Side) := Fin.comp_cons (drip (I:=I) n) x.1 v; let w : chain (Biglot I) _:= Fin.cons x.2 (Fin.cons x.1 v)
   unfold telescopeTerm shed halve; refine Tendsto.mul (((tendsto_const_nhds.mul (e x.1 x.2)).mul_const _).mul_const _) ?_
   specialize ht w; simpa only [w,Fin.comp_cons] using ht
end YM.FormalBulk08.Lotus
