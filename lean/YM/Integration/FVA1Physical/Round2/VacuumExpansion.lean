import YM.Integration.FVA1Physical.Round2.VacuumShells
import YM.Integration.FVA1Physical.VacuumTrajectory

/-! A finite, exact shell presentation of the physical vacuum discrepancy
on the small-field chart. The shell supports and their prices are explicit,
and the scalar at the origin is retained. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Lattice Push Push.Uniform MSbar MSbar.Lis MSbar.Whisk MeasureTheory
open scoped BigOperators Classical Topology Interval
variable {σ : Type} [Fintype σ] {n : Side}

/-- The zeroth shell is local to one lattice site. Later shells are radial
differences with their full actual coordinate support. -/
def radialShell (site : σ → Site n) (F : Positions σ → ℝ) (i : σ)
    (x : Positions σ) : ℕ → ℝ
  | 0 => radialShare F i (nearField site i 0 x)
  | r+1 => radialShare F i (nearField site i (r+1) x) -
      radialShare F i (nearField site i r x)

omit [Fintype σ] in
theorem shell_depends_on_ball (site : σ → Site n) (F : Positions σ → ℝ)
    (i : σ) (r : ℕ) {x y : Positions σ}
    (same : ∀ j, separation (site i) (site j) ≤ r → x j = y j) :
    radialShell site F i x r = radialShell site F i y r := by
  cases r with
  | zero => exact radialShare_local site i 0 F same
  | succ r =>
    exact congrArg₂ (·-·) (radialShare_local site i (r+1) F same)
      (radialShare_local site i r F (fun j h => same j (h.trans (Nat.le_succ r))))

omit [Fintype σ] in
private theorem near_near (site : σ → Site n) (i : σ) {r R : ℕ} (hr : r ≤ R)
    (x : Positions σ) : nearField site i r (nearField site i R x) = nearField site i r x := by
  funext j
  by_cases he : separation (site i) (site j) ≤ r
  · simp [nearField,he,he.trans hr]
  · simp [nearField,he]

omit [Fintype σ] in
private theorem shells_telescope (site : σ → Site n) (F : Positions σ → ℝ)
    (i : σ) (x : Positions σ) (R : ℕ) :
    ∑ r ∈ Finset.range (R+1), radialShell site F i x r = radialShare F i (nearField site i R x) := by
  induction R with
  | zero => simp [radialShell]
  | succ R ih =>
    rw [Finset.sum_range_succ,ih]; simp [radialShell]

/-- A torus-independent decay envelope on each outer shell, in the actual
supremum norm on its entire field ball. -/
theorem shell_price {site : σ → Site n} {a w B : ℝ} {s k : ℕ}
    {F : Positions σ → ℝ} (J : JetTab site a s w (Metric.closedBall 0 w) F 1 B)
    (hw : 0 < w) (ha : 0 ≤ a) (hf : ∀ x ∈ Metric.closedBall 0 w, ContDiffAt ℝ k F x)
    (hk : 2 ≤ k) (i : σ) (r : ℕ) {x : Positions σ} (hx : x ∈ Metric.closedBall 0 w) :
    ‖radialShell site F i x (r+1)‖ ≤ B / liftW a s (r+1) := by
  let y := nearField site i (r+1) x
  have hy : ‖y‖ ≤ w := (nearField_norm ..).trans (mem_closedBall_zero_iff.1 hx)
  have h := radialShare_tail J hw ha hf hk i r (mem_closedBall_zero_iff.2 hy)
  rw [show nearField site i r y = nearField site i r x from near_near site i (Nat.le_succ r) x] at h
  refine h.trans ?_
  have hiy : ‖y i‖ ≤ w := (norm_le_pi_norm y i).trans hy
  have p : 0 ≤ B / w^2 := div_nonneg J.zeroP (sq_nonneg _)
  calc
    ‖y i‖ * (‖y‖ * (B / w^2) / liftW a s (r+1)) ≤
      w * (w * (B / w^2) / liftW a s (r+1)) :=
        mul_le_mul hiy (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hy p) (wpos ..).le)
          (div_nonneg (mul_nonneg (norm_nonneg _) p) (wpos ..).le) hw.le
    _ = _ := by field_simp

/-- Exact equality on any finite geometry. D is its actual diameter. -/
theorem shells_reconstruct {site : σ → Site n} {w : ℝ} {k : ℕ} {F : Positions σ → ℝ}
    (hf : ∀ x ∈ Metric.closedBall 0 w, ContDiffAt ℝ k F x) (hk : 1 ≤ k)
    {x : Positions σ} (hx : x ∈ Metric.closedBall 0 w) :
    let D := extent (Finset.univ.image site)
    F x = F 0 + ∑ i, ∑ r ∈ Finset.range (D+1), radialShell site F i x r := by
  intro D
  have full (i : σ) : nearField site i D x = x := by
    funext j
    have d : separation (site i) (site j) ≤ D := curve (Finset.mem_image_of_mem site (Finset.mem_univ i))
      (Finset.mem_image_of_mem site (Finset.mem_univ j))
    simp [nearField,d]
  simp_rw [shells_telescope, full]
  rw [radialShare_sum hf hk hx]; ring

open Filter RG Wilson Precision MSbar.Midpoint
open PhysicalNext.Repeat.Legato

/-- The repeatable calibrated family, actual kinetic reset, and exact small-field
vacuum representation with uniform anchored shell prices are witnessed jointly. -/
theorem shells_on_calibrated_family {G : Gauge} (hG : G.Simple) (d : ℝ) (hd : 0 < d) :
    ∃ (C : Family G) (Z : Horizon C.path.levels) (u : G.ColorIndex)
      (K : Kin Z (Next.Foundations.chart G)),
      C.path.levels.clock.kernel.penalty = d ∧ Spec.Calibrated C ∧ C.Makes ∧
      ∀ (s p m : ℕ), 6 ≤ s → 4 ≤ m → p+2 ≤ m → ∀ᶠ k : ℕ in atTop,
        ∀ (N i : ℕ), k ≤ N → ∃ S : Scene C.path.levels i p,
          Realized K N i k p (Lis.sun G u) S ∧
          (∀ j, k ≤ j → j ≤ N →
            let Q := C.path.rep N i j
            let β := C.path.levels.clock.hatBeta j
            let site := Measuring.chart (C.path.levels.S.side j i) G
            let F := Aqua.film Q (S.Poly j) (Heath.Stock.cue Q.beta) p
            ∀ x ∈ Metric.closedBall 0 (Mosaic.vol β),
              F x = F 0 + ∑ v, ∑ r ∈ Finset.range (extent (Finset.univ.image site)+1),
                radialShell site F v x r ∧
              ∀ v r, ‖radialShell site F v x (r+1)‖ ≤
                (5 * Mosaic.goalP β p) / liftW (Mosaic.αm β) s (r+1)) ∧
          ∀ j, k ≤ j → j < N →
            |Heath.Stock.cue (C.path.rep N i j).beta / Heath.Stock.cue (C.path.rep N i (j+1)).beta -
              Bakery.taste p (S.action j) (Heath.Stock.cue (C.path.rep N i j).beta)| ≤
              Mosaic.goalP (C.path.levels.clock.hatBeta j) p := by
  obtain ⟨C, penalty, calibrated, makes, _, _, ⟨Z, u, K, docket⟩, _⟩ := newyearV hG hd
  refine ⟨C, Z, u, K, penalty, calibrated, makes, ?_⟩
  intro s p m hs hm hp
  have grows := Alto.broad.comp (Multi.Wage.hat_tend hG C.path.levels)
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.mp (grows.eventually_gt_atTop 0)
  filter_upwards [docket.purse s p m hs hm hp, eventually_ge_atTop k₀] with k paid hwide
  intro N i hkN
  obtain ⟨⟨S, hS⟩, covers⟩ := paid N i hkN
  obtain ⟨tickets, reset, _⟩ := covers S hS
  refine ⟨S, hS, ?_, reset⟩
  intro j hkj hjN
  dsimp only
  intro x hx
  have T := tickets j hkj hjN
  have wide := hk₀ j (hwide.trans hkj)
  have hw : 0 < Mosaic.vol (C.path.levels.clock.hatBeta j) := div_pos wide (by norm_num)
  have ha : 0 ≤ Mosaic.αm (C.path.levels.clock.hatBeta j) := zpow_nonneg wide.le _
  have J := JetTab.levelAll hw ha T.grown T.rangeP hm le_rfl 1 (by omega)
  exact ⟨shells_reconstruct T.grown (by omega) hx, fun v r =>
    shell_price J hw ha T.grown (by omega) v r hx⟩

end YM.Integration.FVA1Physical.Round2
