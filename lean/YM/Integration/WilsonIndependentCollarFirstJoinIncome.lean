import YM.Integration.WilsonIndependentCollarWickIncome

/-! The connected birth from two already deposited nonempty sources.
Both input tensors retain their own rooted prices. The cross contraction
is the one in the finite marked heat equation, at the admitted width. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarFirstJoinIncome
open Filter Finset Function Lattice Laurent Bloch Metric Precision RG Next.Free Work.F08 Wilson FormalBulk08 Flat
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G : Gauge} {ι U α : Type} [DecidableEq ι] {S J : Finset ι} {D : ι → ℕ}

theorem lamp (d : Distance U) (C : ropes U α α) {σ z : ℝ} (c : dragCup d σ z C) (sub : J⊆S)
    (X : Gen (Pen D J) (U×α)) (Y : Gen (Pen D (S\J)) (U×α)) (i j : ℕ)
    (x : Fin (i+j) → U×α) (y : Fin 2 → U×α) :
    Real.exp (σ*d.gap (y 0).1 (y 1).1) * ‖lakeL C sub X Y (i+j) i j x y‖ ≤
      sealM i j*z * (‖X (i+1) (Fin.cons (y 0) (x ∘ Fin.castAdd j))‖ *
                       ‖Y (j+1) (Fin.cons (y 1) (x ∘ Fin.natAdd i))‖) := by
  have seal_pos : 0 ≤ sealM i j := by unfold sealM; positivity
  have coeff := c.2 (y 0) (y 1)
  let a := σ*d.gap (y 0).1 (y 1).1
  have wick : Real.exp a * |C (y 0) (y 1)|≤z := by
    calc
      _ ≤ Real.exp a * (z*Real.exp (-σ*d.gap (y 0).1 (y 1).1)) :=
        mul_le_mul_of_nonneg_left coeff (Real.exp_pos _).le
      _ = _ := by dsimp [a]; rw [mul_left_comm,←Real.exp_add]; simp
  rw [lakeV,norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg seal_pos,waveJoy]
  let u := X (i+1) (Fin.cons (y 0) (x ∘ Fin.castAdd j))
  let v := Y (j+1) (Fin.cons (y 1) (x ∘ Fin.natAdd i))
  change Real.exp a * (sealM i j * |C (y 0) (y 1)| * ‖joy sub u v‖)≤_
  calc
    _ = (sealM i j * (Real.exp a * |C (y 0) (y 1)|)) * ‖joy sub u v‖ := by ring
    _ ≤ (sealM i j*z) * (‖u‖*‖v‖) :=
      mul_le_mul (mul_le_mul_of_nonneg_left wick seal_pos) (joy_norm sub u v)
        (norm_nonneg _) (mul_nonneg seal_pos c.1)

/-- Absolute summation keeps one root wallet per input. The finite subtotal
form also works directly for the two countable tensors on the cover. -/
theorem subtotal {A B : Type} (d : Distance U) (C : ropes U α α) {σ z : ℝ} (c : dragCup d σ z C)
    (sub : J⊆S) (X : Gen (Pen D J) (U×α)) (Y : Gen (Pen D (S\J)) (U×α)) (i j : ℕ)
    (sa : Finset A) (sb : Finset B) (a : A → U×α) (b : B → U×α)
    (u : A → Fin i → U×α) (v : B → Fin j → U×α)
    (f : A → ℝ) (g : B → ℝ) (hf : ∀ k,0≤f k) (hg : ∀ l,0≤g l) :
    (∑ k∈sa,∑ l∈sb, f k*g l *
      (Real.exp (σ*d.gap (a k).1 (b l).1) *
        ‖lakeL C sub X Y (i+j) i j (Fin.append (u k) (v l)) ![a k,b l]‖)) ≤
    sealM i j*z * ((∑ k∈sa, f k*‖X (i+1) (Fin.cons (a k) (u k))‖) *
                    ∑ l∈sb, g l*‖Y (j+1) (Fin.cons (b l) (v l))‖) := by
  simp only [sum_mul,mul_sum]
  conv_rhs => rw [sum_comm]
  apply sum_le_sum; intro k _
  apply sum_le_sum; intro l _
  have h := lamp d C c sub X Y i j (Fin.append (u k) (v l)) ![a k,b l]
  have left : (Fin.append (u k) (v l)) ∘ Fin.castAdd j = u k := by funext m; simp
  have right : (Fin.append (u k) (v l)) ∘ Fin.natAdd i = v l := by funext m; simp
  rw [left,right] at h
  calc
    _ ≤ f k*g l * (sealM i j*z * (‖X (i+1) (Fin.cons (a k) (u k))‖ *
                                     ‖Y (j+1) (Fin.cons (b l) (v l))‖)) :=
      mul_le_mul_of_nonneg_left (by simpa using h) (mul_nonneg (hf k) (hg l))
    _ = _ := by ring

omit [DecidableEq ι] in
/-- These are the literal two covariance rows of one named finite Wick
packet. Its cover companion retains the same rate on all period lifts. -/
theorem original {I : Arch G} {e : ℕ} {Z : Finset ι} {k : ι→ℕ} (p : PackOne Z D k e I) :
    dragCup (tor p.V.n) I.s I.mass p.N ∧ dragCup Bank.terrain I.s I.mass p.M :=
  ⟨p.V.rateRamp.bow,p.V.rateRamp.berth⟩

end YM.Integration.WilsonIndependentCollarFirstJoinIncome
