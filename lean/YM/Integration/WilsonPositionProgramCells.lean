import YM.Integration.WilsonPositionProgramPoint

/-! Compare the actual directory to the continuum coefficient at every location of a
compact separated test, including positions between the auxiliary lattice points. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramCells
open Filter Set Function Metric Maxwell XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1
open FVA2 FVA2.Register MS MS.Land Lattice
open scoped BigOperators Classical Topology ContDiff
variable {G : Gauge} (Z : WilsonPrescription G) {g : G.Simple}
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {T : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z g M T dial)
    {n : ℕ} (d : ℕ) (μ : ℝ) (v : Tags G d n) (k : ℕ)

include H in
theorem compact (K : Set (Points n)) (hK : IsCompact K) (separated : K ⊆ conf n) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ i : ℕ in atTop, ∀ B (P : Handoff.Directory Z i B),
      Handoff.Directory.budget G n d + k ≤ B → ∀ x ∈ K,
      ‖WilsonPositionProgramPoint.entry Z (T:=T) P d μ
        (draw x (Z.run.step i) (river (Z.run.step i))) v k - Dframe.meteor μ M d x k v‖ ≤
        C * (Speed.chip (Z.run.step i) + (Z.run.step i).spacing) := by
  obtain ⟨r,pos,rK⟩ := hK.exists_cthickening_subset_open (conf_open n) separated
  let K' := cthickening r K
  have hc : IsCompact K' := hK.cthickening
  let Y := fun x : Points n => Dframe.meteor μ M d x k v
  have hs (x) (hx : x ∈ K') : ContDiffAt ℝ ∞ Y x := Speed.Star.smooth_r μ M v k x (rK hx)
  have hd : ContinuousOn (fderiv ℝ Y) K' := fun x hx =>
    ((hs x hx).continuousAt_fderiv (by simp)).continuousWithinAt
  obtain ⟨L,hL⟩ := (hc.image_of_continuousOn hd.norm).bddAbove
  obtain ⟨C,hC,ready⟩ := WilsonPositionProgramPoint.priced Z H d μ K' hc rK v k
  let D := max L 0 * (4*n:ℝ)
  have nonneg : 0 ≤ D := mul_nonneg (le_max_right ..) (by positivity)
  have near : ∀ᶠ i : ℕ in atTop, (4*n:ℝ)*(Z.run.step i).spacing < r := by
    have h := (frontier.endpt.comp H.onSchedule).const_mul (4*n:ℝ)
    have h' : Tendsto (fun i => (4*n:ℝ)*(Z.run.step i).spacing) atTop (𝓝 0) := by
      simpa only [mul_zero, Function.comp_apply, Expense.a, id_eq] using h
    exact (tendsto_order.mp h').2 r pos
  refine ⟨C+D,add_pos_of_pos_of_nonneg hC nonneg,?_⟩
  filter_upwards [ready, near] with i price hi
  intro B P cap x hx
  let m := Z.run.step i
  let y := familiar (ascend x m)
  have hxy : dist y x ≤ (4*n:ℝ)*m.spacing := m.upper_corner (river m) (x:=draw x m (river m)) (z:=x) rfl
  have hB : closedBall x r ⊆ K' := fun z hz => mem_cthickening_of_dist_le z x r K hx hz
  have hy : y ∈ closedBall x r := hxy.trans hi.le
  have h₁ := price B P (draw x m (river m)) (river m) cap (sits m) (hB hy)
  have h₂ : ‖Y y-Y x‖ ≤ max L 0 * ‖y-x‖ :=
    (convex_closedBall x r).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => (hs z (hB hz)).differentiableAt (by simp))
      (fun z hz => (hL (mem_image_of_mem _ (hB hz))).trans (le_max_left ..))
      (mem_closedBall_self pos.le) hy
  have h₂' : ‖Y y-Y x‖ ≤ D*m.spacing := by
    rw [show D*m.spacing=max L 0*((4*n:ℝ)*m.spacing) by dsimp [D]; ring]
    exact h₂.trans (mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using hxy) (le_max_right ..))
  have hc₁ := norm_add_le (WilsonPositionProgramPoint.entry Z (T:=T) P d μ
    (draw x m (river m)) v k - Y y) (Y y - Y x)
  rw [sub_add_sub_cancel] at hc₁
  calc
    _ ≤ C*Speed.chip m+D*m.spacing := hc₁.trans (add_le_add h₁ h₂')
    _ ≤ (C+D)*(Speed.chip m+m.spacing) := by
      have hp : 0 ≤ Speed.chip m := (Speed.f_pos id m).le
      have hm : 0 ≤ m.spacing := m.positive.le
      nlinarith [mul_nonneg nonneg hp,mul_nonneg hC.le hm]

end YM.Integration.WilsonPositionProgramCells
end
