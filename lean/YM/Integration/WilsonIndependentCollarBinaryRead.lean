import YM.Integration.WilsonIndependentCollarFirstRung

/-! The full contracted binary term of the original finite Wick equation.
Both eliminated endpoint sums and the average over all free-leg
permutations are included. The residual angular rank can be zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarBinaryRead
open Finset Function Lattice Laurent Bloch Metric Precision RG Work.F08 Wilson FormalBulk08
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Winding
open WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G : Gauge} {ι α : Type} [DecidableEq ι] [Fintype α]
variable {D : ι→ℕ} {S J : Finset ι} {n : Side}

theorem complete (C : ropes (Site n) α α) (z : ℝ) (positive : 0≤z)
    (issued : ∀ u v, |C u v|≤z) (sub : J⊆S)
    (X : Gen (Pen D J) (Site n×α)) (Y : Gen (Pen D (S\J)) (Site n×α)) (i j : ℕ)
    (A B : ℝ) (left : ∀ u:Fin i→Site n×α, ∑ a,‖X (i+1) (Fin.cons a u)‖≤A)
    (right : ∀ v:Fin j→Site n×α, ∑ b,‖Y (j+1) (Fin.cons b v)‖≤B)
    (x : Fin (i+j)→Site n×α) :
    ‖refuge (swivel (lakeL C sub X Y (i+j) i j)) x‖ ≤ sealM i j*z*(A*B) := by
  classical
  let K := lakeL C sub X Y (i+j) i j
  let Z := sealM i j*z
  have z0 : 0 ≤ Z := by dsimp [Z,sealM]; positivity
  have hC : dragCup (tor n) 0 z C := ⟨positive,by simpa using issued⟩
  have subtotal (t : Fin (i+j)→Site n×α) : ∑ y, ‖K t y‖ ≤ Z*(A*B) := by
    let u := t ∘ Fin.castAdd j
    let v := t ∘ Fin.natAdd i
    let a (q : Site n×α) := ‖X (i+1) (Fin.cons q u)‖
    let b (q : Site n×α) := ‖Y (j+1) (Fin.cons q v)‖
    have hb : 0≤∑ l, b l := sum_nonneg fun _ _=>norm_nonneg _
    have ha : 0≤A := (sum_nonneg fun _ _=>norm_nonneg _).trans (left u)
    rw [pair_apply]
    calc
      _ ≤ ∑ k,∑ l, Z*(a k*b l) := by
        apply sum_le_sum; intro k _
        apply sum_le_sum; intro l _
        simpa [K,Z,a,b,u,v] using WilsonIndependentCollarFirstJoinIncome.lamp
          (tor n) C hC sub X Y i j t ![k,l]
      _ = Z*((∑ k,a k)*∑ l,b l) := by
        simp only [mul_sum,sum_mul]
        rw [sum_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul (left u) (right v) hb ha) z0
  let k := (Fintype.card (Equiv.Perm (Fin (i+j))):ℝ)
  have kp : 0<k := by dsimp [k]; positivity
  have exact_read : refuge (swivel K) x =
      k⁻¹ • ∑ π:Equiv.Perm (Fin (i+j)), ∑ y,K (x∘π) y := by
    simp only [refuge,swivel,k,Pi.smul_apply,Finset.sum_apply,smul_sum]
    rw [sum_comm]
  change ‖refuge (swivel K) x‖ ≤ Z*(A*B)
  rw [exact_read,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr kp)]
  calc
    _ ≤ k⁻¹ * ∑ _π:Equiv.Perm (Fin (i+j)), Z*(A*B) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr kp.le)
      apply (norm_sum_le ..).trans
      apply sum_le_sum; intro π _
      exact (norm_sum_le ..).trans (subtotal (x∘π))
    _ = _ := by
      rw [sum_const,nsmul_eq_mul,card_univ]
      change k⁻¹*(k*(Z*(A*B)))=_
      field_simp

omit [Fintype α] in
/-- Specialization to the deposited split on the genuine nonbare packet.
The first-rung identity inserts exactly this term with t=q=u=e'=0. -/
theorem original {I : Arch G} {Z : Finset ι} {k : ι→ℕ} {e : ℕ}
    (p : PackOne Z D k e I) (sub : J⊆S) (t q u e' i j : ℕ) (A B : ℝ)
    (left : ∀ y:Fin i→Site p.V.n×I.dial,
      ∑ a,‖p.surfU J t q (i+1) (Fin.cons a y)‖≤A)
    (right : ∀ y:Fin j→Site p.V.n×I.dial,
      ∑ b,‖p.surfU (S\J) u e' (j+1) (Fin.cons b y)‖≤B)
    (x : Fin (i+j)→Site p.V.n×I.dial) :
    ‖refuge (swivel (lakeL p.N sub (p.surfU J t q) (p.surfU (S\J) u e')
      (i+j) i j)) x‖ ≤ sealM i j*I.mass*(A*B) := by
  have range := (p.V.rateRamp.mono I.h.le).bow
  exact complete p.N I.mass range.1 (fun a b=>by simpa using range.2 a b)
    sub _ _ i j A B left right x

end YM.Integration.WilsonIndependentCollarBinaryRead
