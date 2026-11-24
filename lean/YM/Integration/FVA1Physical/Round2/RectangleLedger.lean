import YM.Integration.FVA1Physical.Round2.Rectangle

/-! One price list for mixed finite changes and held regular derivatives on
the same representation. Changes may be chosen separately at every tuple;
the count of tuples is already included in each anchored weighted row. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Lattice Push Push.Uniform MSbar MSbar.Lis MSbar.Whisk
open scoped BigOperators Classical Topology
variable {σ : Type} [Fintype σ] {n : Side}

def mixedRectangle (F : Positions σ → ℝ) (l : List σ) (r : ℕ) (h : σ → ℝ) (x : Positions σ) : ℝ :=
  rectangle h (l.take r).reverse (fun y=>buoy F y (l.drop r)) x

structure RectangleLedger (site : σ → Site n) (a : ℝ) (s : ℕ) (w : ℝ) (S : Set (Positions σ))
    (F : Positions σ → ℝ) (m : ℕ) (B : ℝ) : Prop where
  covers : ∃ price : List σ → ℝ,
    (∀ l : List σ, l.length=m+1 → 0 ≤ price l ∧
      ∀ (r : ℕ) (h : σ → ℝ) (x : Positions σ), (∀ i, |h i| ≤ w) →
        rectangleInside h S (l.take r).reverse x →
        |mixedRectangle F l r h x| * w^(l.drop r).length ≤ price l) ∧
    ∀ i, Yarn m (fun t=>price (i::t)*Measuring.swipe site a s (i::t)) ≤ B

omit [Fintype σ] in
private theorem product_price (h : σ → ℝ) (w : ℝ) (hw : 0≤w) (bounds : ∀ i, |h i|≤w) (l : List σ) :
    (l.map (fun i=>|h i|)).prod ≤ w^l.length := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ']
    apply mul_le_mul (bounds i) ih _ hw
    exact List.prod_nonneg (by simp)

theorem rectangle_ledger {site : σ → Site n} {a w B : ℝ} {s m k : ℕ}
    {S : Set (Positions σ)} {F : Positions σ → ℝ}
    (J : JetTab site a s w S F m B) (hw : 0<w)
    (hf : ∀ y∈S, ContDiffAt ℝ k F y) (room : m+1≤k) :
    RectangleLedger site a s w S F m B := by
  obtain ⟨price,paid,row⟩ := J.sold
  refine ⟨price,?_,row⟩
  intro l length
  obtain ⟨pos,bound⟩ := paid l length
  refine ⟨pos,?_⟩
  intro r h x cap inside
  have Eq : (l.take r).length + (l.drop r).length = m+1 := by
    rw [← List.length_append,List.take_append_drop,length]
  have wp := pow_pos hw (m+1)
  have fit : w^(l.take r).length * w^(l.drop r).length = w^(m+1) := by rw [← pow_add,Eq]
  have pay := rectangle_price hf h (l.take r).reverse (l.drop r) x inside
    (by simpa only [List.length_reverse,Eq] using room) (price l / w^(m+1))
    (fun y hy=> by rw [List.reverse_reverse,List.take_append_drop]; exact (le_div_iff₀ wp).2 (bound y hy))
  have P : |mixedRectangle F l r h x| ≤ w^(l.take r).length*(price l/w^(m+1)) := by
    apply pay.trans
    apply mul_le_mul_of_nonneg_right _ (div_nonneg pos wp.le)
    simpa only [List.length_reverse] using product_price h w hw.le cap (l.take r).reverse
  calc
    _ ≤ (w^(l.take r).length*(price l/w^(m+1)))*w^(l.drop r).length :=
      mul_le_mul_of_nonneg_right P (pow_nonneg hw.le _)
    _ = (w^(l.take r).length*w^(l.drop r).length)*(price l/w^(m+1)) := by ring
    _ = _ := by rw [fit]; field_simp

end YM.Integration.FVA1Physical.Round2
