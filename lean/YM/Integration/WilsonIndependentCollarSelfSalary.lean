import YM.Integration.WilsonIndependentCollarBinarySalary

/-! A Wick self-pair spends its actual rooted incoming salary. Both eliminated
angular endpoints are summed before the volume is varied. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarSelfSalary
open Finset Function Lattice Laurent Bloch Metric Precision RG Work.F08 Wilson FormalBulk08
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Winding
open WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {U E : Type} [Fintype U] [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem first (r : ℕ) (f : (Fin (r+1)→U)→ℝ) :
    ∑ y,f y = ∑ a,∑ x:Fin r→U,f (Fin.cons a x) := by
  rw [←(Fin.consEquiv (fun _:Fin (r+1)=>U)).sum_comp f,Fintype.sum_prod_type]
  rfl

def coefficient (r : ℕ) (z : ℝ) :=
  (((r+1:ℕ):ℝ)*((r+2:ℕ):ℝ)/2)*z

theorem complete (C : Matrix U U ℝ) (z : ℝ) (r : ℕ) (P : Gen E U)
    (cash : ∀a b,|C a b|≤z) (w : (Fin r→U)→ℝ) (v : (Fin (r+2)→U)→ℝ)
    (good : ∀x,0≤w x) (keep : ∀ a b x,w x≤v (Fin.cons b (Fin.cons a x))) :
    ∑ x,w x*‖ripple C P r x‖ ≤ coefficient r z * ∑ y,v y*‖P (r+2) y‖ := by
  let f (y : Fin (r+2)→U) := v y * ‖P (r+2) y‖
  have cost (a b:U) : |C a b/2| * ↑(r+1)*↑(r+2) ≤ coefficient r z := by
    rw [abs_div,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    change _≤(((r+1:ℕ):ℝ)*((r+2:ℕ):ℝ)/2)*z
    calc
      _ ≤ (z/2)*↑(r+1)*↑(r+2) := by gcongr; exact cash a b
      _ = _ := by ring
  have point (x:Fin r→U) : w x*‖ripple C P r x‖ ≤
      coefficient r z * ∑ a,∑ b,f (Fin.cons b (Fin.cons a x)) := by
    simp only [ripple,Finset.sum_apply,Pi.smul_apply]
    apply le_trans (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans
      (sum_le_sum fun _ _=>norm_sum_le ..)) (good x))
    simp only [mul_sum]
    apply sum_le_sum; intro a _
    apply sum_le_sum; intro b _
    have pr : (0:ℝ)≤((r+1:ℕ):ℝ) := Nat.cast_nonneg _
    have pr' : (0:ℝ)≤((r+2:ℕ):ℝ) := Nat.cast_nonneg _
    simp only [Pi.smul_apply,sever,prune,←Nat.cast_smul_eq_nsmul ℝ,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg pr,abs_of_nonneg pr']
    let c := |C a b/2| * ↑(r+1)*↑(r+2)
    have cn : 0≤c := by dsimp [c]; positivity
    let u : Fin (r+2)→U := Fin.cons b (Fin.cons a x)
    calc
      _ = c*(w x*‖P (r+2) u‖) := by dsimp [c,u]; ring
      _ ≤ c * f u := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (keep a b x) (norm_nonneg _)) cn
      _ ≤ _ := mul_le_mul_of_nonneg_right (cost a b)
        (mul_nonneg ((good x).trans (keep a b x)) (norm_nonneg _))
  have rel : ∑ x:Fin r→U, ∑ a, ∑ b,f (Fin.cons b (Fin.cons a x)) = ∑ y,f y := by
    rw [first (r+1) f]
    simp_rw [first r (fun (y:Fin (r+1)→U)=>f (Fin.cons _ y))]
    calc
      _ = ∑ x:Fin r→U,∑ b,∑ a,f (Fin.cons b (Fin.cons a x)) := by
        apply sum_congr rfl; intro x _; rw [sum_comm]
      _ = ∑ b,∑ x:Fin r→U,∑ a,f (Fin.cons b (Fin.cons a x)) := sum_comm
      _ = _ := by
        apply sum_congr rfl; intro a _; rw [sum_comm]
  calc
    _ ≤ ∑ x, coefficient r z * ∑ a, ∑ b,f (Fin.cons b (Fin.cons a x)) := sum_le_sum fun x _=>point x
    _ = _ := by rw [←mul_sum,rel]

variable {G : Gauge} {ι : Type} [DecidableEq ι] {S Z : Finset ι} {D k : ι→ℕ}
omit [Fintype U] [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem posted {I : Arch G} {e : ℕ} (p : PackOne Z D k e I) (o : Site p.V.n)
    (t q r : ℕ) :
    ∑ x,Real.exp (I.s*tread (tor p.V.n) o x)*‖ripple p.N (p.surfU S t q) r x‖ ≤
      coefficient r I.mass * ∑ y,Real.exp (I.s*tread (tor p.V.n) o y)*‖p.surfU S t q (r+2) y‖ := by
  have ramp := (p.V.rateRamp.mono I.h.le).bow
  apply complete p.N I.mass r (p.surfU S t q) (fun a b=>by simpa using ramp.2 a b)
    _ _ (fun _=>(Real.exp_pos _).le)
  intro a b x
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ I.h.le
  exact_mod_cast (show tread (tor p.V.n) o x ≤ tread (tor p.V.n) o (Fin.cons b (Fin.cons a x)) by
    apply league_le
    intro i j
    let f : Fin (r+1)→Fin (r+3) := Fin.cons 0 (fun u=>u.succ.succ.succ)
    have leg (u : Fin (r+1)) :
        stud o (Fin.cons b (Fin.cons a x)) (f u) = stud o x u := by
      refine Fin.cases ?_ (fun u=>?_) u <;> rfl
    rw [←leg i,←leg j]
    exact leg_le _ _ _ _)

end YM.Integration.WilsonIndependentCollarSelfSalary
