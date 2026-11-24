import YM.XSpace.Trinity
import YM.Next.MAXWELL.Turn

/-! The on-shell curl and divergence equations for each chirality, including
the first derivative of a genuine color component of an original Maxwell jet. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonMaxwellThermometerJets
open Set Function Analysis Maxwell Maxwell.Free XSpace.Chiral
open scoped ContDiff BigOperators

def chiral (s : Bool) (a : P) (f : Axis → Axis → ℝ) : ℝ :=
  f 0 (shard a) + sig s * f (shard (a+1)) (shard (a+2))

def first (f : Maxwell.Field ℝ) (x : E4) (k a b : Axis) : ℝ := grad k (f a b) x

private theorem axis_order (f : Axis → ℝ) (a : P) :
    ∑ k, f k = f 0 + f (shard a) + f (shard (a+1)) + f (shard (a+2)) := by
  rw [Fin.sum_univ_four]
  fin_cases a
  · rfl
  · change f 0 + f 1 + f 2 + f 3 = f 0 + f 2 + f 3 + f 1
    ring
  · change f 0 + f 1 + f 2 + f 3 = f 0 + f 3 + f 1 + f 2
    ring

private theorem electric (d : Axis → Axis → Axis → ℝ)
    (ha : ∀ k a b, d k a b = - d k b a) (hd : ∀ b, ∑ k, d k k b = 0)
    (a : P) :
    d 0 0 (shard a) =
      d (shard (a+1)) (shard a) (shard (a+1)) -
      d (shard (a+2)) (shard (a+2)) (shard a) := by
  have h := hd (shard a)
  rw [axis_order _ a] at h
  have diag := ha (shard a) (shard a) (shard a)
  have rev := ha (shard (a+1)) (shard (a+1)) (shard a)
  linarith only [h, diag, rev]

private theorem magnetic (d : Axis → Axis → Axis → ℝ)
    (ha : ∀ k a b, d k a b = -d k b a)
    (hc : ∀ a b c, d a b c + d b c a + d c a b = 0) (a : P) :
    d 0 (shard (a+1)) (shard (a+2)) =
      d (shard (a+1)) 0 (shard (a+2)) - d (shard (a+2)) 0 (shard (a+1)) := by
  linarith only [hc 0 (shard (a+1)) (shard (a+2)),
    ha (shard (a+1)) (shard (a+2)) 0]

structure Equations (s : Bool) (t : Axis → P → ℝ) : Prop where
  divergence : ∑ a : P, t (shard a) a = 0
  evolution (a : P) : t 0 a = sig s *
    (t (shard (a+1)) (a+2) - t (shard (a+2)) (a+1))

private theorem equations (s : Bool) (d : Axis → Axis → Axis → ℝ)
    (ha : ∀ k a b, d k a b = -d k b a) (hd : ∀ b, ∑ k, d k k b = 0)
    (hc : ∀ a b c, d a b c + d b c a + d c a b = 0) :
    Equations s (fun k a => chiral s a (d k)) := by
  constructor
  · have h := hd 0
    rw [Fin.sum_univ_four] at h
    have hE : ∑ a : P, d (shard a) 0 (shard a) = 0 := by
      rw [Fin.sum_univ_three]
      change d 1 0 1 + d 2 0 2 + d 3 0 3 = 0
      linarith only [h, ha 0 0 0, ha 1 0 1, ha 2 0 2, ha 3 0 3]
    have hM : ∑ a : P, d (shard a) (shard (a+1)) (shard (a+2)) = 0 := by
      rw [Fin.sum_univ_three]
      exact hc 1 2 3
    simp only [chiral, Finset.sum_add_distrib, ← Finset.mul_sum, hE, hM, mul_zero, add_zero]
  · intro a
    have he := electric d ha hd a
    have hm := magnetic d ha hc a
    have cyclic : ∀ i : P, i+2+1=i ∧ i+2+2=i+1 ∧ i+1+1=i+2 ∧ i+1+2=i := by decide
    obtain ⟨h1,h2,h3,h4⟩ := cyclic a
    cases s <;> simp only [chiral, sign_pos, sign_neg, h1, h2, h3, h4] <;>
      linarith only [he, hm]

theorem field (s : Bool) (f : Maxwell.Field ℝ) (hf : WaveOn univ f) (x : E4) :
    Equations s (fun k a => chiral s a (first f x k)) := by
  apply equations
  · intro k a b
    have h : f a b = -(f b a) := funext fun y => hf.form _ _ _ (mem_univ y)
    simp only [first, grad, Analysis.D, h, fderiv_neg, neg_apply]
  · exact fun b => hf.divergence b x (mem_univ _)
  · exact fun a b c => hf.cycle a b c x (mem_univ _)

/-- Both regular derivatives retain the native Maxwell equations after
projection on one physical color. -/
theorem original {G : Gauge} {j : ℕ} (A : Shell G j) (L : G.Color →L[ℝ] ℝ)
    (s : Bool) (x : E4) (v : E4) :
    let f := fun a b => L ∘ asWave A a b
    Equations s (fun k a => chiral s a (first f x k)) ∧
    Equations s (fun k a => chiral s a (first (fun u b => Analysis.D v (f u b)) x k)) := by
  let f := fun a b => L ∘ asWave A a b
  have h : WaveOn univ f := Maxwell.composeColor L (wavePoly A)
  exact ⟨field s f h x, field s _ (wave_D h isOpen_univ v) x⟩

end YM.Integration.WilsonMaxwellThermometerJets
