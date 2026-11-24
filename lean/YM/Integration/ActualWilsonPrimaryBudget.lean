import YM.Integration.ActualWilsonAxisSpectator
import YM.RG3.Primary.Emboss
import YM.Integration.LocalComparisonNativeRows
import YM.Push.LOCAL_SPLITTING.Funding

/-! The exact price of extracting one marked regular Taylor direction from
the retained physical layout. The field, distance and cover reserves are
compared on the same regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonPrimaryBudget
open Function Set Finset Lattice Wilson RG Marker Source Labels RG3.Script.Picnic
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open Comparison.RG02 PhysicalNext.Repeat.Legato Overlay Push.Local Push.AbsoluteSums
open RG3.Forms RG3.Primary Next.Foundations
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}

/-- Pass from the original factorial Taylor bill to the native derivative
norm through the order actually requested by the physical recipient. -/
theorem native_derivatives {p q : BudgetPoint} {X : Support n} {o : Site n}
    {f : Config G n → ℂ} {b : ℝ} (h : Mix.grain p X f o b)
    (ht : q.threshold = p.threshold) (ho : q.order ≤ p.order)
    (hp : q.power ≤ p.power) : q.supBounds o X f ((q.order.factorial : ℝ)*b) := by
  obtain ⟨a,ha,hprice,hderiv⟩ := h
  have hs (k : ℕ) (hk : k ≤ q.order) : a k / (k.factorial : ℝ) ≤ b := by
    apply le_trans _ hprice
    exact single_le_sum (f := fun j : ℕ => a j / (j.factorial : ℝ))
      (s := range (p.order+1)) (fun j _ => div_nonneg (ha j) (by positivity))
      (mem_range.2 (Nat.lt_succ_of_le (hk.trans ho)))
  have hb : 0 ≤ b := (div_nonneg (ha 0) (by positivity)).trans (hs 0 (Nat.zero_le _))
  refine ⟨mul_nonneg (by positivity) hb, ?_⟩
  intro U hU l hl hdir
  have hl' (A) (hA : A ∈ l) : p.dirBound o A := by
    intro e
    apply le_trans (hdir A hA e)
    rw [ht]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (le_add_of_nonneg_right (Nat.cast_nonneg _) : (1:ℝ) ≤ 1+(separation e.1 o : ℝ)) hp)
      p.threshold_pos.le
  have hval := hderiv l (hl.trans ho) hl' U (ht ▸ hU)
  calc
    _ ≤ a l.length := hval
    _ ≤ b*(l.length.factorial : ℝ) := (div_le_iff₀ (by positivity)).1 (hs l.length hl)
    _ ≤ b*(q.order.factorial : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.factorial_le hl) hb
    _ = _ := mul_comm _ _

private theorem joined {d : ℕ} {F : Frame G d} {A : Hol G} {T : SectionData F}
    {p q : BudgetPoint} {o : Site n} {X : Support n} {w b : ℝ}
    (he : Readable A T q n w) (hx : o∈X) (hb : 0≤b) (hB : q.B=p.B)
    (hs : q.supportExponent+2 ≤ p.supportExponent) :
    Real.exp ((q.supportExponent+1)*coverNumber q.B (joint T o X)) *
      (atomPrice A F w *((q.order.factorial : ℝ)*b)) ≤
        (factor A T q.supportExponent w*(q.order.factorial : ℝ))*p.mass X b := by
  have hd : 0 ≤ (q.order.factorial : ℝ) := by positivity
  have ht := mul_nonneg hd hb
  have ha := zero_le_one.trans (atomPrice_ge_one A F he.nonneg)
  have hf : 0 ≤ factor A T q.supportExponent w := mul_nonneg (Real.exp_pos _).le ha
  calc
    _ ≤ reservedMass q (joint T o X) (atomPrice A F w * ((q.order.factorial : ℝ)*b)) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))) (mul_nonneg ha ht)
    _ ≤ factor A T q.supportExponent w * reservedMass q X ((q.order.factorial : ℝ)*b) :=
      price_join T A o hx he.sound he.nonneg ht
    _ ≤ factor A T q.supportExponent w * ((q.order.factorial : ℝ)*p.mass X b) := by
      apply mul_le_mul_of_nonneg_left _ hf
      unfold reservedMass BudgetPoint.mass
      rw [hB]
      calc
        _ ≤ Real.exp (p.supportExponent * coverNumber p.B X)*((q.order.factorial : ℝ)*b) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2
            (mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg _))) ht
        _ = _ := by ring
    _ = _ := by ring

variable {V Ξ : Type} [DecidableEq V] {B : Census V} {o : V → Site n}
    {P : Rep G n} {T : Taste Ξ o P B} {p : BudgetPoint}
    {θ : V → ℝ} {κ reg fro : ℝ} {d : ℕ} {F : Frame G d}

/-- A single common white-row envelope pays the enlarged physical stencil
for every test, with the numerical factors and the exact headroom exposed. -/
theorem regular (H : FullBudget p T θ κ reg fro) (A : Hol G) (sec : SectionData F) {w : ℝ}
    (he : Readable A sec P.p n w) (ht : P.p.threshold=p.threshold)
    (hB : P.p.B=p.B) (ho : P.p.order≤p.order) (hp : P.p.power≤p.power)
    (hs : P.p.supportExponent+2 ≤ p.supportExponent) (x : Ξ) (v : V) :
    let m j := (P.p.order.factorial : ℝ)*H.white j
    let L := factor A sec P.p.supportExponent w*(P.p.order.factorial : ℝ)
    StemPay v (T.leaf x) A sec w θ m (L*reg) := by
  intro m L
  let D := T.leaf x
  have hv := (H.active x).articles
  have hio (i : ℕ) (hi : earns v D i) : v ∈ (T.menu.rays i).val := by
    change (T.menu.rays i) = B.fire v at hi
    rw [hi]
    exact mem_singleton_self _
  have hd : 0 ≤ (P.p.order.factorial : ℝ) := by positivity
  have ha := zero_le_one.trans (atomPrice_ge_one A F he.nonneg)
  have hL : 0 ≤ L := mul_nonneg (mul_nonneg (Real.exp_pos _).le ha) hd
  refine ⟨fun j hj => ?_, ?_⟩
  · change P.p.supBounds _ _ _ ((P.p.order.factorial : ℝ)*H.white j)
    rw [show D.contents.origins v = o v from congrFun T.root v]
    exact native_derivatives ((H.regular j).controls x v (hio j hj)) ht ho hp
  · obtain ⟨b,c,hb,hc,hpay⟩ := H.regularTotal v
    have hunit := mul_nonneg (H.radii v).le (H.unit_nonnegative v)
    have hbl : b ≤ reg := by linarith [budget_nonneg hc]
    apply budget_mono (budget_scale hL (budget_loosen hb hbl))
    · intro j
      unfold gross ink
      split_ifs
      · exact mul_nonneg (H.radii v).le (mul_nonneg (Real.exp_pos _).le
          (mul_nonneg ha (mul_nonneg hd (H.white_nonnegative j))))
      · rw [mul_zero,mul_zero]
    intro j
    by_cases hj : earns v D j
    · have hvj := hio j hj
      have hroot := hv.pins j v hvj
      have bound := joined he hroot (H.white_nonnegative j) hB hs
      rw [if_pos hvj,show T.menu.rays j = B.fire v from hj,Poly.solo_toll]
      unfold gross ink
      rw [if_pos hj]
      exact (mul_le_mul_of_nonneg_left bound (H.radii v).le).trans_eq (by
        change θ v * (L * p.mass (T.menu.branch j) (H.white j)) =
          L * (θ v * p.mass (T.menu.branch j) (H.white j))
        ring)
    · unfold gross ink
      rw [if_neg hj,mul_zero,mul_zero]
      exact mul_nonneg hL (hb.1 j)

end YM.Integration.ActualWilsonPrimaryBudget
