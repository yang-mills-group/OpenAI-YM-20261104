import YM.MSbar.Pole.Scale.Tree

/-! # RG differential identity with UV endpoint criterion for tree edges. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Set Filter MeasureTheory Ambient Momentum Mellin Age
open scoped Topology ContDiff BigOperators Classical
variable {I : Type} [Fintype I] {F : ℂ→Cloud I}

def approaching := nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ
instance : approaching.NeBot := by unfold approaching; infer_instance

/-- Tree with a fresh heat slice gives UV-vanishing right side. -/
def Wing (A : Finset I) (d : Age) (F : ℂ→Cloud I) := d.l=0 →
    ∀ᶠ z in approaching, ∀ n x,Tendsto (fun s : ℝ=> roll A d s F z n x) (𝓝[>] 0) (nhds 0)
/-- Radial cost on actual integrals, applied to any positive scale.
Joint germ in all momentum values and positive scales. -/
def Pulse (A : Finset I) (d : Age) (F G : ℂ→Cloud I):= ∀ᶠ z in approaching, ∀ n x (r:ℝ), 0<r →
    HasDerivAt (fun s : ℝ=> roll A d s G z n x) ((r:ℂ)⁻¹ *roll A d r F z n x) r

variable (A:Finset I) (d:Age) {k:ℕ}

lemma currents (h : Vortex k F) (hw : Wing A d F) : Pulse A d F (step A d F) ∧ Wing A d (step A d F) := by
  obtain ⟨R,hr,G,H,hG⟩:= licence h
  have hf z (hz:z∈slit R) (x) (i): F z x i=(z^k)⁻¹*G z x i:= hG z hz x i
  have he z (hz:z∈slit R) (r : ℝ) (n) (x): roll A d r F z n x=(z^k)⁻¹*roll A d r G z n x:= by unfold roll; rw [hf z hz, mul_left_comm]
  have hm z (hz:z∈slit R) (n) (x) : (fun r:ℝ=> roll A d r (step A d F) z n x)=(fun r=> (z^k)⁻¹ * roll A d r (step A d G) z n x):= by
    funext r; unfold roll; rw [finite_mul A d H n _ _ hz.1 _ (fun _=> hf z hz _ (move A _ _)),mul_left_comm]
  have ht (hd:d.l=0): ∀ᶠ z in approaching, ∀ n x,Tendsto (fun r:ℝ=>roll A d r G z n x) (𝓝[>] 0) (nhds 0):= by
    filter_upwards [neighborhood hr,hw hd] with z hz h n x
    have hy : z≠0:=hz.2
    have hb (r : ℝ): roll A d r G z n x=z^k*roll A d r F z n x:= by rw [he z hz,mul_inv_cancel_left₀ (pow_ne_zero k hy)];
    simpa only [hb,mul_zero] using ((h n x).const_mul (z^k))
  refine ⟨?_,fun hd=>?_⟩
  · have h₁ : ∀ᶠ z in approaching, ∀ n x, ∀ j<d.safety,d.increment j z≠ 0 ∨ pbody A G j z n x=0:= by
      have h₂ := eventually_all_finset (Finset.range d.safety) |>.mpr (fun i hi => d.guards i)
      by_cases hb:d.l=0
      · filter_upwards [ht hb,neighborhood hr,h₂] with z he hz hf n x j hj; rcases hf j (Finset.mem_range.mpr hj) with hx|hx; exact Or.inl hx
        exact Or.inr ((counts H hz.1 _ d hb (he n x) j (le_of_eq hx.2)).2)
      filter_upwards [h₂] with z hz n x j hj; exact Or.inl ((hz j (Finset.mem_range.mpr hj)).resolve_right fun h=> hb h.1)
    unfold Pulse; have h₂ : ∀ᶠ z in approaching,2≤(d.alpha z).re+d.safety := d.safely.filter_mono nhdsWithin_le_nhds
    filter_upwards [neighborhood hr,h₂,h₁] with z hz ha hb n x r hk
    rw [hm z hz,he z hz]; refine (((differential A H hz.1 x d hk ha (hb n x)).const_mul _).congr_deriv ?_)
    unfold roll; rw [Complex.cpow_sub _ _ (by exact_mod_cast hk.ne'),Complex.cpow_one]; ring
  filter_upwards [ht hd,neighborhood hr] with z ht hz n x
  rw [hm z hz]; simpa using (child H hz.1 x d hd (ht n x)).const_mul ((z^k)⁻¹)
end YM.MSbar.Pole
