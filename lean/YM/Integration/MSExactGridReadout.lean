import YM.FVA2.Tiles
import YM.FVA2.Pond

/-! Exact original clock positions on each fixed q-adic grid and the
continuity extension of every separated multipoint coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.MSExactGridReadout

open Filter Set Function FVA2 Lattice MS MS.Land MS.Menus MS.Tone MS.Dial MS.Rake
open scoped Topology BigOperators Classical

variable {I W : Type} (q : Side)

def point (m : ℕ) (z : Cover) : QP := Real.exp (-Tiles.clock q m) • Tone.embed z

def rounded (m : ℕ) (x : W → QP) (w : W) : QP :=
  point q m (Tiles.mesh (Tiles.clock q m) (x w))

theorem spacing {m j : ℕ} (h : m ≤ j) :
    Real.exp (Tiles.clock q j) * Real.exp (-Tiles.clock q m) = (q.val : ℝ)^(j-m) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Real.exp_neg, Tiles.clock_scale, Tiles.clock_scale, pow_add, Nat.add_sub_cancel_left]
  have hn : (q.val : ℝ)^m ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr q.property.ne')
  field_simp

theorem lattice {m j : ℕ} (h : m ≤ j) (z : Cover) :
    Tiles.mesh (Tiles.clock q j) (point q m z) = fun i => ((q.val : ℤ)^(j-m)) * z i := by
  funext i
  change ⌊Real.exp (Tiles.clock q j) *
    (Real.exp (-Tiles.clock q m) * ((z i : ℤ) : ℝ))⌋ = _
  rw [← mul_assoc, spacing q h]
  exact_mod_cast Int.floor_intCast (((q.val : ℤ)^(j-m)) * z i)

theorem stable {m j : ℕ} (h : m ≤ j) (z : W → Cover) :
    rounded q j (fun w => point q m (z w)) = fun w => point q m (z w) := by
  funext w i
  unfold rounded
  rw [lattice q h]
  change Real.exp (-Tiles.clock q j) * (((q.val : ℤ)^(j-m) * z w i : ℤ) : ℝ) =
    Real.exp (-Tiles.clock q m) * (z w i : ℝ)
  push_cast
  rw [← spacing q h]
  rw [← mul_assoc, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

theorem dense (hq : 1 < q.val) (x : W → QP) :
    Tendsto (fun j => rounded q j x) atTop (𝓝 x) := by
  apply tendsto_pi_nhds.mpr
  intro w
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [dist_eq_norm]
  exact squeeze_zero' (.of_forall fun _ => norm_nonneg _)
    (.of_forall fun j => Tiles.unmesh _ (x w))
    (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (Tiles.forward q hq)))

theorem trial [LinearOrder W] [Fintype W] (hq : 1 < q.val) (μ : ℝ)
    (m : ℕ) (z : W → Cover) (hx : Injective fun w => point q m (z w)) :
    ∃ k : ℕ, ∀ o : ℕ → Cover, (∀ j, Tiles.Daily q j (o j)) →
      let F := Tiles.ladder (fun w => point q m (z w)) q μ o k
      Uses F atTop μ ∧ ∀ᶠ j in atTop, testP F j = fun w => point q m (z w) := by
  obtain ⟨k, hk⟩ := Tiles.ranges q hq μ (fun w => point q m (z w)) hx
  refine ⟨k, fun o ho => ⟨(hk o ho).1, ?_⟩⟩
  filter_upwards [eventually_ge_atTop m] with j hj
  exact stable q (by omega : m ≤ j+k) z

theorem extend [Fintype W] (hq : 1 < q.val) (x : W → QP) (hx : Injective x)
    (f g : (W → QP) → ℂ) (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (he : ∀ (m : ℕ) (z : W → Cover), Injective (fun w => point q m (z w)) →
      f (fun w => point q m (z w)) = g (fun w => point q m (z w))) :
    f x = g x := by
  have hd := dense q hq x
  have separated : IsOpen {z : W → QP | Injective z} := by
    let P := {p : W × W | p.1 ≠ p.2}
    have split : {z : W → QP | Injective z} =
        ⋂ p : P, {z : W → QP | z p.val.1 ≠ z p.val.2} := by
      ext z
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      exact ⟨fun h p => h.ne p.property, fun h i j he =>
        Classical.byContradiction fun hn => h (⟨(i,j),hn⟩ : P) he⟩
    rw [split]
    exact isOpen_iInter_of_finite fun p => isOpen_ne_fun (continuous_apply _) (continuous_apply _)
  have ho : ∀ᶠ j in atTop, Injective (rounded q j x) :=
    hd (separated.mem_nhds hx)
  exact tendsto_nhds_unique (hf.tendsto.comp hd)
    ((hg.tendsto.comp hd).congr' (ho.mono fun j hj =>
      (he j (fun w => Tiles.mesh (Tiles.clock q j) (x w)) hj).symm))

end YM.Integration.MSExactGridReadout
