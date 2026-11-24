import YM.Integration.WilsonPhysicalTagCumulants
import YM.Integration.WilsonAxialCoordinates
import YM.Integration.WilsonAxialReach
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Draught
import YM.Branch.Predict

/-! A changed physical likelihood requires a true rough plaquette in a fixed rooted window. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonTagThermalWindow
open Filter Set MeasureTheory Lattice Wilson RG Pressure OPE.Therm
open WilsonPhysicalTagCumulants WilsonAxialWindow
open AnalyticNext.ConnectedActivity
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side}

private theorem embedded (q : Ratio c f) (x y : Site c) :
    separation (q.embed x) (q.embed y) ≤ q.count.val * separation x y := by
  unfold separation
  rw [← q.root_embed,← q.root_embed,← map_sub,q.root_embed]
  apply Finset.sup_le
  intro i _
  rw [q.lift_embed]
  simp only [Pi.smul_apply,nsmul_eq_mul,Int.natAbs_mul,Int.natAbs_natCast]
  exact Nat.mul_le_mul_left _ (component_le _ _)

private theorem reached (q : Ratio c f) (x : Site c) (z : Site f)
    {B : ℕ} (h : separation x (q.parent z) ≤ B) :
    separation (q.embed x) z < q.count.val*(B+1)+1 := by
  have ha := (embedded q x (q.parent z)).trans (Nat.mul_le_mul_left _ h)
  have hb := Corona.near q z
  rw [separation_comm z _] at hb
  have hc := separation_triangle (q.embed x) (q.embed (q.parent z)) z
  rw [Nat.mul_add,Nat.mul_one]
  omega

def changed (S : StepData c f) (t : S.Choices) (e : Edge (Site c)) : Set (Config G f) :=
  {W | frameDensity S W e.1 (t.1 e.1) ≠ 1 ∨ connectorDensity S W t.1 e (t.2 e) ≠ 1}

/-- The error set ranges over every joint label choice at this physical site. -/
def activated (S : StepData c f) (e : Edge (Site c)) : Set (Config G f) :=
  {W | ∃ t : S.Choices, W ∈ changed S t e}

private theorem moved (S : StepData c f) (h : S.patch.Branches S.kernel G)
    (W : Config G f) (k : Site f → G.El) (t : S.Choices) (e : Edge (Site c)) :
    frameDensity S (Lattice.gauge k W) e.1 (t.1 e.1) = frameDensity S W e.1 (t.1 e.1) ∧
    connectorDensity S (Lattice.gauge k W) t.1 e (t.2 e) = connectorDensity S W t.1 e (t.2 e) := by
  constructor
  · unfold frameDensity
    rw [expandAt_gauge,(S.patch.frame_gauged h ..).1]
  · unfold connectorDensity
    rw [S.updateGauged h,(S.patch.bond_gauge (h:=h) ..).1]

structure Window (G : Gauge) (D : Patch) (K : KernelChoices) where
  r : ℕ
  gate : ℝ
  positive : 0 < gate
  clean {c f : Side} (S : StepData c f) (hd : S.patch = D) (hk : S.kernel = K)
    (hn : 2*r < f.val) (W : Config G f) (t : S.Choices) (e : Edge (Site c)) :
    (∀ z∈cells (S.ratio.embed e.1) r, G.chord (faceValue W z) ≤ gate) → W ∉ changed S t e

/-- Fix a single admitted link neighborhood before every period and fine field. -/
theorem purchase (D : Patch) (K : KernelChoices) (h : D.Branches K G) : Nonempty (Window G D K) := by
  have hc := (Aff.tap_open D K h 0 1 zero_lt_one).and
    ((Work.E09.betaF_growth G D.L).eventually (eventually_gt_atTop 0))
  obtain ⟨x,hx,hβ⟩ := hc.exists
  let r := D.L.val*(radiusB x/2+1)+1
  let a := Rates.allowance G D x 1 0
  have ha : 0 < a := by
    simpa only [a,Rates.allowance,Rates.pieces,pow_zero,one_mul,pow_one,Pressure.fiery]
      using Work.E09.temp_pos hβ
  let B : ℝ := 4*(r:ℝ)*Fintype.card PlaqAxes
  have hr : 0 < r := Nat.zero_lt_succ _
  have hb : 0 < B := by
    have hp : 0 < Fintype.card PlaqAxes := Fintype.card_pos
    dsimp [B]
    positivity
  refine ⟨⟨r,a/B,div_pos ha hb,?_⟩⟩
  intro c f S hd hk hn W t e quiet
  let k := frame (1:Lattice.Order) (S.ratio.embed e.1) W
  have small (j : Edge (Site f)) (hj : separation e.1 (S.ratio.parent j.1) ≤ radiusB x/2) :
      G.chord (Lattice.gauge k W j) ≤ a := by
    have inside := reached S.ratio e.1 j.1 hj
    have hr' : S.ratio.count.val*(radiusB x/2+1)+1 = r := by
      change S.patch.L.val*(radiusB x/2+1)+1 = _
      rw [hd]
    rw [hr'] at inside
    exact (WilsonAxialWindow.bound _ _ W r hn j inside (div_pos ha hb).le quiet).trans_eq
      (by change B*(a/B)=a; field_simp)
  have both := hx S hd hk (Lattice.gauge k W) t e small
  have hs : S.patch.Branches S.kernel G := by rw [hd,hk]; exact h
  have hm := moved S hs W k t e
  have hm' := frame_germ S (Lattice.gauge k W) e.1 (t.1 e.1) (hk.symm ▸ both.1)
  have hb' := connector_germ S (Lattice.gauge k W) t.1 e (t.2 e) (hk.symm ▸ both.2.1)
  exact fun bad => bad.elim (fun no => no (hm.1.symm.trans hm')) (fun no => no (hm.2.symm.trans hb'))

/-- The thermal bound uses the original probability at each cutoff and a fixed
number of plaquettes independent of the period, tag, and position. -/
theorem selected {H : History G} (Y : H.Selected) (P : Poetry H.levels) (hG : G.Simple)
    (D : Patch) (K : KernelChoices) (h : D.Branches K G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ m : ℕ in atTop, ∀ N, m ≤ N → ∀ p, ∀ {c : Side}
      (S : StepData c (H.S.side m p)), S.patch = D → S.kernel = K →
      ∀ e : Edge (Site c),
      (scene H N p m).real (activated (G:=G) S e) ≤ C*vanishP H.levels m := by
  let T := Classical.choice (purchase D K h)
  refine ⟨((T.r+T.r+1)^4*Fintype.card PlaqAxes : ℕ),by positivity,?_⟩
  have cold : Tendsto (cool H.levels) atTop (𝓝 0) := by
    simpa [WilsonAxialReach.reach] using WilsonAxialReach.cools H.levels hG 1 0
  filter_upwards [cold.eventually (gt_mem_nhds T.positive),WilsonAxialReach.fixed H.S T.r,
    rare (H:=H) P hG Y] with m hcool hside hit N hN p c S hd hk e
  letI : IsProbabilityMeasure (scene H N p m) := probability (H:=H) (p:=p) Y hN
  have sub : activated (G:=G) S e ⊆ WilsonAxialCoordinates.excluded (S.ratio.embed e.1) T.r (cool H.levels m) := by
    rintro W ⟨t,bad⟩
    by_contra hn
    exact T.clean S hd hk (hside p) W t e (fun z hz => (WilsonAxialCoordinates.outside hn z hz).trans hcool.le) bad
  calc
    _ ≤ _ := measureReal_mono sub (measure_ne_top _ _)
    _ ≤ _ := WilsonAxialCoordinates.omitted _ _ _ _ _ (fun z _ => hit N hN p z)
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (WilsonAxialWindow.count _ T.r)) (Real.exp_pos _).le

end YM.Integration.WilsonTagThermalWindow
