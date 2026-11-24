import YM.XSpace.Jets
import YM.Analysis.SmoothJets
/-! # Interchange two finite Taylor tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Formal
open Function Set Filter Analysis
open scoped Topology InnerProductSpace BigOperators ContDiff

variable {F : (ℝ × ℝ) → ℂ} {x y : ℝ}

private lemma dir1 (h : ContDiffAt ℝ ω F (x,y)) :
    deriv (fun t=>F (t,y)) x = D (1,0) F (x,y) := by
  let g (t:ℝ):=(t,y)
  have he : HasDerivAt g (1,0) x := (hasDerivAt_id' _).prodMk (hasDerivAt_const ..)
  exact ((show HasFDerivAt F _ (g x) from (h.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt x he).deriv
private lemma dir2 (h : ContDiffAt ℝ ω F (x,y)) :
    deriv (fun t=>F (x,t)) y = D (0,1) F (x,y) := by
  let g (t:ℝ):=(x,t)
  have he : HasDerivAt g (0,1) y := (hasDerivAt_const ..).prodMk (hasDerivAt_id' _)
  exact ((show HasFDerivAt F _ (g y) from (h.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt y he).deriv

def repeated (v : ℝ × ℝ) (F : ℝ×ℝ→ℂ) : ℕ→ (ℝ×ℝ→ℂ)
| 0=>F
| k+1=>D v (repeated v F k)

private lemma d_omega (u : ℝ × ℝ) (h : ContDiffAt ℝ ω F (x,y)) (n) : ContDiffAt ℝ ω (repeated u F n) (x,y) := by
  induction n with | zero=>exact h|succ n ih=> exact dSmooth ih u (by simp)
private lemma lane1 (h : ContDiffAt ℝ ω F (x,y)) (n) : iteratedDeriv n (fun t=> F (t,y)) x = repeated (1,0) F n (x,y) := by
  induction n generalizing x with
  | zero=> rfl
  | succ n ih=>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n (fun t => F (t,y)) =ᶠ[𝓝 x] fun t => repeated (1,0) F n (t,y) :=
      (((continuous_id.prodMk (continuous_const (y:=y))).tendsto x).eventually (h.eventually (by simp))).mono fun i hi=> ih hi
    rw [he.deriv_eq]; exact dir1 (d_omega _ h n)
private lemma lane2 (h : ContDiffAt ℝ ω F (x,y)) (n) : iteratedDeriv n (fun t=> F (x,t)) y = repeated (0,1) F n (x,y) := by
  induction n generalizing y with
  | zero=> rfl
  | succ n ih=>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n (fun t => F (x,t)) =ᶠ[𝓝 y] fun t => repeated (0,1) F n (x,t) :=
      ((((continuous_const (y:=x)).prodMk continuous_id).tendsto y).eventually (h.eventually (by simp))).mono fun i hi=> ih hi
    rw [he.deriv_eq]; exact dir2 (d_omega _ h n)

private lemma r_move (v w : ℝ×ℝ) {z : ℝ×ℝ} (h : ContDiffAt ℝ ω F z) (n) :
    D v (repeated w F n) z= repeated w (D v F) n z := by
  induction n generalizing z with
  | zero=>rfl
  | succ n ih=>
    rw [repeated, Analysis.commuteD ((show ContDiffAt ℝ ω (repeated w F n) z from d_omega _ (show ContDiffAt ℝ ω F (z.1,z.2) from h) _).of_le le_top), repeated]
    exact GermD w ((h.eventually (by simp)).mono fun i hi=> ih hi)

private lemma r_switch (v w : ℝ×ℝ) {z : ℝ×ℝ} (h : ContDiffAt ℝ ω F z) (m n) :
    repeated v (repeated w F n) m z = repeated w (repeated v F m) n z := by
  induction m generalizing z with
  | zero=>rfl
  | succ m ih=>
    rw [repeated, GermD v ((h.eventually (by simp)).mono fun i hi => ih hi)] -- inspect
    exact r_move v w (d_omega v (show ContDiffAt ℝ ω F (z.1,z.2) from h) _) n

theorem swap (h : ContDiffAt ℝ ω F (x,y)) (m n : ℕ) :
    iteratedDeriv n (fun u=> iteratedDeriv m (fun v=>F (u,v)) y) x=
    iteratedDeriv m (fun v=> iteratedDeriv n (fun u=>F (u,v)) x) y := by
  have he : (fun u : ℝ=> iteratedDeriv m (fun v=>F (u,v)) y) =ᶠ[𝓝 x] fun u=> repeated (0,1) F m (u,y) :=
    (((continuous_id.prodMk (continuous_const (y:=y))).tendsto x).eventually (h.eventually (by simp))).mono fun i hi=> lane2 hi m
  have ht : (fun v : ℝ=> iteratedDeriv n (fun u=>F (u,v)) x) =ᶠ[𝓝 y] fun v=> repeated (1,0) F n (x,v) :=
    ((((continuous_const (y:=x)).prodMk continuous_id).tendsto y).eventually (h.eventually (by simp))).mono fun i hi=> lane1 hi n
  rw [he.iteratedDeriv_eq,ht.iteratedDeriv_eq, lane2 (d_omega _ h _), lane1 (d_omega _ h _), r_switch _ _ h]
end YM.XSpace.Formal
