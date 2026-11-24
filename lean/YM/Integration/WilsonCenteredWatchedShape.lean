import YM.Integration.WilsonCenteredCubeMass
import YM.Integration.WilsonMacroscopicRichFixedWatchSale

/-! Joint placements at the actual external detector and a whole compact near
shape. The radius is chosen from the true detector before either regulator. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredWatchedShape
open Function Set Filter Metric MeasureTheory Analysis Table Spec Lattice Extraction Next.UVStress
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {n : ℕ} (W : Watch C)

def joint (r : ℝ) (x : Points n) : Points (n+W.n) :=
  points (Fin.append (fun i=>(r • x) i) (fun j=>W.held j.succ))

theorem continuous_joint (r : ℝ) : Continuous (joint W r : Points n → _) :=by
  unfold joint points
  apply (PiLp.continuous_toLp _ _).comp
  apply continuous_pi
  intro k
  refine Fin.addCases (fun i=>?_) (fun j=>?_) k
  · simp only [Fin.append_left]
    fun_prop
  · simp only [Fin.append_right]
    exact continuous_const

private theorem outer (j : Fin W.n) (a : Axis) : W.held j.succ a ≠ 0 :=by
  intro h
  have eq : W.held j.succ a = (W.held 0) a :=by rw [W.origin]; exact h
  exact Fin.succ_ne_zero j ((W.wild a) eq)

private theorem coordinates (r : ℝ) (x : Points n) (a : Axis) :
    (fun i=>joint W r x i a) =
      Fin.append (fun i=>(r • x) i a) (fun j=>W.held j.succ a) :=by
  funext k
  refine Fin.addCases (fun i=>?_) (fun j=>?_) k <;>
    simp only [joint,points,WithLp.ofLp_toLp,Fin.append_left,Fin.append_right]

private theorem separated (φ : Test n) :
    ∃ ρ > 0, ∀ r : ℝ, 0 < r → r < ρ → ∀x∈tsupport (φ : Points n→ℂ),∀(i:Fin n)(j:Fin W.n)(a:Axis),(r • x) i a ≠ W.held j.succ a :=by
  obtain ⟨M,cap⟩:=φ.hasCompactSupport.isBounded.exists_norm_le
  have small : ∀ᶠ r : ℝ in 𝓝 0,∀j:Fin W.n,∀a:Axis, |r| * max 1 M < |W.held j.succ a| :=by
    apply eventually_all.mpr
    intro j
    apply eventually_all.mpr
    intro a
    have h := (continuous_abs.mul continuous_const).continuousAt
      (x:=0) (f:=fun r:ℝ=>|r| * max 1 M)
    exact h.tendsto.eventually (gt_mem_nhds (by simpa using abs_pos.mpr (outer W j a)))
  obtain ⟨ρ,hρ,h⟩:=Metric.mem_nhds_iff.mp small
  refine ⟨ρ,hρ,fun r hr hR x hx i j a eq=>?_⟩
  have haway:=h (show r∈Metric.ball 0 ρ by simpa [Real.dist_eq,abs_of_pos hr] using hR) j a
  have hc : |x i a| ≤ max 1 M :=
    (show |x i a| ≤ ‖x i‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (x i) a).trans
      ((PiLp.norm_apply_le x i).trans ((cap x hx).trans (le_max_right 1 M)))
  have near : |(r • x) i a| ≤ |r| * max 1 M :=by
    change |r * x i a| ≤ _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hc (abs_nonneg _)
  exact (ne_of_lt (near.trans_lt haway)) (congrArg abs eq)

/-- The joint position stays in the original configuration domain, and almost
every one of the signed test's near configurations meets the original generic
point-limit hypothesis at the detector's exact fixed exterior sites. -/
theorem original (φ : Test n) :
    ∃ ρ > 0, ∀ r : ℝ, 0 < r → r < ρ → 
      (∀x∈tsupport (φ : Points n→ℂ),joint W r x ∈ conf _) ∧
      (∀ᵐ x ∂volume.restrict (tsupport (φ : Points n→ℂ)),joint W r x ∈ generic _) :=by
  obtain ⟨ρ,hp,buy⟩:=separated W φ
  refine ⟨ρ,hp,fun r hr hR=>⟨?_,?_⟩⟩
  · intro x hx
    change Function.Injective (Fin.append (fun i=>(r • x) i) (fun j=>W.held j.succ))
    apply Fin.append_injective_iff.mpr
    refine ⟨Work.A05.smul_conf hr (φ.tsupport_subset hx),W.distinct.comp (Fin.succ_injective W.n),?_⟩
    intro i j eq
    exact buy r hr hR x hx i j 0 (congrArg (fun y:E4=>y 0) eq)
  · filter_upwards [ae_restrict_of_ae (almostGeneric n),ae_restrict_mem φ.hasCompactSupport.measurableSet] with x hx hk
    intro a
    rw [coordinates]
    apply Fin.append_injective_iff.mpr
    refine ⟨?_,(W.wild a).comp (Fin.succ_injective W.n),fun i j=>buy r hr hR x hk i j a⟩
    intro i j eq
    apply hx a
    exact mul_left_cancel₀ hr.ne' (show r*x i a=r*x j a from eq)

end YM.Integration.WilsonCenteredWatchedShape
