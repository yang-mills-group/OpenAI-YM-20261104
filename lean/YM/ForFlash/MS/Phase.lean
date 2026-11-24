import YangMills.WilsonProof.NativeSupport.YM.MS.Rake.Cluster

/-!
# Uniform external phase budget for a wide mark

East & Gulf: spend `large` **at the actual mark distance**, including for
paying *every derivative* of the external oscillating factor, not with credit
bounded by a fixed multiple of power-counting separation. West: do this also
above the longer of the mark/heater lengths, and use `hob` below. These
are statements for the CoversF regulator of the eventual application (in
particular PulseQ's `planeF`), not for arbitrary box periods/graphs.

Other MS ForFlash modules will extend the Rake/Vane argument with this
estimate, following the weakening plan in (WiderProfiles) (in references/e11);
but the resulting bound **won't charge mark diameter at all in Mesh**.
Note: we still separately use Fleet's geometry and prices, with a growable
`bank`. Our price will work on the polynomial-in-inverse-mesh regions used
when applying to the signed-correlation construction.
-/

set_option autoImplicit false
noncomputable section

namespace YM.MS

variable {ι E F:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {T:Cost ι E} {a:ι→ℝ} {g:Kern ι E ℝ} {S : Scale ι}

lemma Costs.takeOneForFlash {f₁ f₂ f : Kern ι E F}
    (h₁ : Costs T S f₁ g) (h₂ : Costs T S f₂ g)
    (h : ∀ i, f i = f₁ i ∨ f i = f₂ i) : Costs T S f g := by
  refine ⟨fun i=> ?_, fun j=> ?_⟩
  · rcases h i with h|h; exact h ▸ h₁.smooth i; exact h ▸ h₂.smooth i
  have H := Cost.Le.add (h₁.quoted j) (h₂.quoted j) (fun i p hi=> mul_nonneg (h₁.nonneg i p hi) (pow_nonneg (S.pos _).le _))
  apply H.left
  intro i p _
  rcases h i with hi|hi
  · rw [hi]; exact le_add_of_nonneg_right (norm_nonneg _)
  rw [hi]; exact le_add_of_nonneg_left (norm_nonneg _)

namespace Latch
open Set Function Filter Finset Metric Real MeasureTheory
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open scoped Topology ContDiff

section
-- compiler binders in Type
variable {I:Type} {S:Scale I} {x y a v:I→ℝ} {G:Gauge} {P : I → Edge G}
  {A : I → QP} {X Y:I→ Law G} (hk:Sheet S a P)(hx:Lease false true S X x)(hy:Lease false true S Y y)(ha:nn a)(hL:nn x)(hR:nn y)
  {C:ℝ}

include hk hx hy ha hL hR
/-- Join at the uncleared upper end (east/gulf). Compare to the floor, but pay
inside PulseQ at the *actual norm* divided by a constant. -/
theorem PulseQForFlash (hp:0<C)(hb:∀ i,0<v i)(hA:∀ i,C*v i ≤ ‖A i‖)(ht:∀ i,S.length i≤v i)
    (k:ℕ) : Lease false false S (fun i=> Cabin ( A i ) (P i) planeF (X i) (Y i)) (fun i=> a i*(x i*y i)*( S.length i/v i)^k ) := by
  let b i:= ‖A i‖ / C
  have h i : v i ≤ b i := (le_div_iff₀ hp).mpr (by rw [mul_comm]; exact hA i)
  have hh i : C*b i = ‖A i‖ := by unfold b; field_simp
  apply Lease.sticks (PulseQ (T:=C) hk hx hy ha hL hR (fun i=>(hb i).trans_le (h i)) (fun i=>(hh i).le) (fun i=>(ht i).trans (h i)) ⟨C,hp,0,fun i=>by dsimp only; rw [pow_zero,mul_one,hh]⟩ hp k)
  intro i
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (div_nonneg (S.pos i).le ((hb i).le.trans (h i))) (div_le_div_of_nonneg_left (S.pos i).le (hb i) (h i)) k)
    (mul_nonneg (ha i) (mul_nonneg (hL i) (hR i)))

omit hk hx hy ha hL hR in
lemma Lease.takeOneForFlash {F₁ F₂ F : I → Law G} {b c : Bool} (H₁:Lease b c S F₁ a)(H₂:Lease b c S F₂ a)
    (p : ∀ i, F i = F₁ i ∨ F i = F₂ i) : Lease b c S F a := by
  intro E _ _ w hw hc
  refine (H₁ E w hw hc).takeOneForFlash (H₂ E w hw hc) ?_
  intro i
  rcases p i with hi|hi
  · left; funext; unfold Plane.Chart; rw [hi]
  right; funext; unfold Plane.Chart; rw [hi]

theorem hobForFlash {d:ℕ} (H:glob S (fun _=>planeF) d)(ht:Mint S (fun _=>planeF) d) :
    Lease false false S (fun i=> Cabin (A i) (P i) planeF (X i) (Y i)) (a*(x*y)):=by
  classical
  let U (i:I):QP := fun _ : Axis=> S.length i
  let B (i:I):= if S.length i ≤ ‖A i‖ then A i else U i
  let D (i:I):= if S.length i ≤ ‖A i‖ then 0 else A i
  have hB i : S.length i ≤ ‖B i‖ := by
    unfold B; split; assumption
    exact ((Real.norm_of_nonneg (S.pos i).le).symm).le.trans (norm_le_pi_norm (U i) (0:Axis))
  have hD i : ‖D i‖ ≤ S.length i := by
    unfold D; split
    · rw [norm_zero]; exact (S.pos i).le
    exact le_of_not_ge (by assumption)
  apply Lease.takeOneForFlash (F₁:=fun i=> Cabin (B i) (P i) planeF (X i) (Y i)) (PulseQForFlash hk hx hy ha hL hR (A:=B) zero_lt_one (fun i=> (S.pos i).trans_le (hB i)) (fun i=> by rw [one_mul]) hB 0 |>.sticks (fun i=>by simp))
    (hob hk hx hy ha hL hR H ht (A:=D) (fun E _ _ => Cost.of_le fun i _ _=> hD i))
  intro i
  by_cases h: S.length i ≤ ‖A i‖
  · left; rw [show B i=A i from if_pos h]
  right; rw [show D i=A i from if_neg h]
end
end Latch
end YM.MS

end
