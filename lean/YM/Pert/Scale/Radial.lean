import YM.Extra.FREE_DETECTOR_ALGEBRA.GradedBasis
import YM.Pert.Position.Frame
/-! Homogeneity of actual separated bare-curl Wick entries including derivatives. -/
set_option autoImplicit false
noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 420000
namespace YM.Pert.Scale
open Maxwell Set Topology Filter Function Tensor Analysis
open scoped ContDiff
section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
structure Rays (f : E4 → V) (k:ℕ) : Prop where
  diff {x : E4} : x≠0 → ContDiffAt ℝ ∞ f x
  stretch {x : E4} (hx : x≠0) {a : ℝ} : a ≠ 0 → a^k • f (a•x) = f x

lemma Rays.step {f : E4 → V} {k : ℕ} (h : Rays f k) (v : E4) : Rays (D v f) (k+1) := by
  refine ⟨fun hx=>dSmooth (h.diff hx) _ (by simp),?_⟩
  intro x hx a ha
  let T : E4 →L[ℝ] E4 := a • ContinuousLinearMap.id ℝ _
  let A : V →L[ℝ] V := a^k • ContinuousLinearMap.id ℝ _
  have he : f =ᶠ[𝓝 x] A ∘ (f ∘ T) := by
     filter_upwards [open_away.mem_nhds (show x∈away from hx)] with y hy; exact (h.stretch hy ha).symm
  let q := ((h.diff (show T x≠0 from smul_ne_zero ha hx)).differentiableAt (by decide)).hasFDerivAt
  unfold D
  rw [he.fderiv_eq, (A.hasFDerivAt.comp x (q.comp x T.hasFDerivAt)).fderiv]
  change a^(k+1) • _ = a^k • (fderiv ℝ f (a • x) (a • v))
  simp only [map_smul,pow_succ,mul_smul]

protected lemma Rays.coeff {f : E4 → V} {k j : ℕ} (h : Rays f k) (u : Fin j → E4) : Rays (fun x => coeff f j x u) (k+j) := by
  induction j generalizing k f with
  | zero => simpa only [Nat.add_zero,coeff_apply_zero] using h
  | succ j ih =>
    let t := ((↑(j+1 : ℕ) : ℝ))⁻¹
    let v := Fin.tail u
    let w := fun x => coeff (D (u 0) f) j x v
    have he (x : E4) (hx : x≠0) : coeff f (j+1) x u = t • w x := (Fin.cons_self_tail u) ▸ coeff_apply_cons ((h.diff hx).of_le (WithTop.coe_le_coe.mpr le_top)) (u 0) v
    let hl : Rays w (k+1+j) := ih (h.step _) v
    refine ⟨fun {x} hx => ?_,fun {x} hx {a} ha => ?_⟩
    · refine (show ContDiffAt ℝ ∞ (fun x : E4 => t • w x) x from contDiffAt_const.smul (hl.diff hx)).congr_of_eventuallyEq ?_
      filter_upwards [open_away.mem_nhds (show x∈away from hx)] with y hy; exact he y hy
    rw [he x hx,he _ (smul_ne_zero ha hx),smul_comm _ t, show k+(j+1)=k+1+j by omega, hl.stretch hx ha]
end
lemma rays_green : Rays Green 2 where
  diff := freeSmooth
  stretch hx := by intro a ha; simp [Green,norm_smul,mul_pow]; field_simp

lemma branch (i j : Axis) : Rays (grad i (grad j Green)) 4 := (rays_green.step _).step _
set_option maxHeartbeats 320000 in
lemma uncolored (i j a b : Axis) : Rays (bareCurl i j a b) 4 where
  diff hx := Bare.curl_diff hx i j a b
  stretch {x} hx {w} hw := by
    have h' (k l : Axis) : w^4 * grad k (grad l Green) (w • x)=grad k (grad l Green) x := (branch k l).stretch hx hw
    have H := smul_ne_zero hw hx
    simp only [bareCurl,Pi.sub_apply, Bare.opp_grad hx,Bare.opp_grad H,smul_eq_mul,mul_sub,mul_ite,mul_zero, h']

end YM.Pert.Scale
