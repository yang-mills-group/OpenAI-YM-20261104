import YM.Integration.FVA1Physical.Wilson.PacketGrade
import YM.Integration.WilsonOriginalCoverCoefficient

/-! A group-field representative formed solely from the independently computed angular coefficients. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonOriginalCoverJetColors
open Function Filter Lattice RG Exterior Tree Precision Marker Multi
open Comparison.RG02 Assembly Valence Adjacent
open YM.Wilson FVA1Physical.Wilson QuadraticLocal.Earn QuadraticLocal.Sunrise
open scoped Topology Classical ContDiff BigOperators

variable {G : Gauge} {V : Type} [DecidableEq V] {R : Census V} {c : Side}
variable (quiet : ℝ → Config G c → ℝ) (power : Hot R → ℕ) (p : ℕ)
  (head : Hot R → ℕ → fieldDir G c 1 → ℂ)

/-- Canonical finite Taylor representative on the group, keeping the prescribed vacuum unchanged. -/
def colors : Bulk.Colors R G c where
  vac := quiet
  power := power
  mark s t U := clockPacket (power s) p (head s) (t,forestLog U)

private theorem chart (s : Hot R) :
    Bulk.projected ((colors quiet power p head).mark s) =ᶠ[𝓝 0] clockPacket (power s) p (head s) := by
  have single (e : Body 1 c) : ∀ᶠ x : fieldDir G c 1 in 𝓝 0, G.plog (G.mat (G.lieExp (x e))) = x e := by
    have pr : Tendsto (fun x : fieldDir G c 1 => x e) (𝓝 0) (𝓝 0) := (continuous_apply e).tendsto 0
    exact pr.eventually G.plog_left
  have near : ∀ᶠ x : fieldDir G c 1 in 𝓝 0, forestLog (represent x) = x := by
    filter_upwards [Filter.eventually_all.mpr single] with x hx
    funext e
    simpa only [forestLog, Work.F03.represent_link,
      show coord (axisEquiv.symm e.2) = e.2 from axisEquiv.apply_symm_apply _] using hx e
  filter_upwards [continuous_snd.continuousAt.tendsto.eventually near] with x hx
  change clockPacket _ _ _ (x.1,forestLog (represent x.2)) = _
  rw [hx]

theorem grade (bounded : ∀ s j, j≤p → Level ((power s+j:ℕ):ℤ) (head s j)) (s : Hot R) :
    GradeAt (power s) (Bulk.projected ((colors quiet power p head).mark s)) :=
  (clockPacket_grade (bounded s)).depends (chart quiet power p head s).symm

theorem angular (bounded : ∀ s j, j≤p → Level ((power s+j:ℕ):ℤ) (head s j))
    (j : ℕ) (hj : j≤p) (z : fieldDir G c 1) :
    Air.discharge (colors quiet power p head) j z = lit R (fun s => head s j z) := by
  apply congrArg (lit R)
  funext s
  change jet (Bulk.projected ((colors quiet power p head).mark s)) (power s+j) (1,z) = _
  rw [show jet (Bulk.projected ((colors quiet power p head).mark s)) (power s+j) =
        jet (clockPacket (power s) p (head s)) (power s+j) from by
    unfold Assembly.jet
    rw [((chart quiet power p head s).iteratedFDeriv ℝ _).eq_of_nhds]]
  exact clockPacket_read (bounded s) hj z

theorem occupied_degree (X : Bulk.Colors R G c)
    (regular : ∀ s, GradeAt (X.power s) (Bulk.projected (X.mark s))) (s : Hot R) (j : ℕ) :
    Level ((X.power s+j:ℕ):ℤ) (fun x => (Air.discharge X j x).part s.val) := by
  simp only [Air.discharge, part_lit]
  have h := SignCovariance.affine_degree ((1:ℝ),(0:fieldDir G c 1))
    (ContinuousLinearMap.inr ℝ ℝ (fieldDir G c 1)) (Adjacent.levelJet (regular s).smooth (X.power s+j))
  simpa using h

/-- Measured own-coupling reset applied to the independently declared covered data. -/
def reset (value : ℕ → Stationary.Link G c → Poly R) (unit : UnitCost) (s : Hot R) (j : ℕ)
    (x : fieldDir G c 1) : ℂ :=
  born (fun d a => (value d a).part s.val) unit 0 p j ((Stationary.arm G c 1).symm x)

end YM.Integration.WilsonOriginalCoverJetColors
