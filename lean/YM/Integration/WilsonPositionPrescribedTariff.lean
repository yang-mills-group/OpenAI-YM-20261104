import YM.Integration.WilsonPositionPrescribedScreen
import YM.Integration.WilsonOrdinaryPositionTaylor
import YM.Integration.WilsonPositionIndependentIntegral

/-! Numerical error propagation for the SAME MS test store. The reference
uses the actual finite list of independent (un-normalized) MS position
coefficients; the differences on the right are honest signed physical test
values. A separate algebraic identification recovers the native formal root. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionPrescribedTariff
open Function Filter Set Finset Metric MeasureTheory Extraction Table Spec OPE OPE.Orbits Climb PhysMS Maxwell
open Trace.Pilot XSpace XSpace.Normalize FVA2 FVA2.Arrival MS MS.Land
open WilsonPositionPrescribedScreen
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} (V : Store G) (ν : ℝ)
    (T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (d q : ℕ)

/-- Zeroth layer is the original reference. The sum uses the signed finite
scopes and all their basis columns, computed from the genuine MS coefficients. -/
def target (t : ℝ) : (V.survey d).Bag :=
  (V.survey d).opening.1 + ∑ i ∈ Finset.range q,
    (t:ℂ)^(i+1) • (V.survey d).purse (Reg.State.kernel ν T d (i+1))

theorem anchored : target V ν T d q 0=(V.survey d).opening.1 := by simp [target]

theorem smooth : ContDiff ℝ ω (target V ν T d q) := by
  apply contDiff_const.add
  apply ContDiff.sum
  intro i _
  exact (show ContDiff ℝ ω (fun t : ℝ=>(t:ℂ)^(i+1)) from Complex.ofRealCLM.contDiff.pow _).smul contDiff_const

def reading (t : ℝ) : MoveSpace G d := (V.survey d).route (V.prepared d) (target V ν T d q t)

theorem analytic : ContDiffAt ℝ ω (reading V ν T d q) 0 :=
  ((anchored V ν T d q).symm ▸ (V.survey d).train (V.prepared d)).comp 0 (smooth V ν T d q).contDiffAt

variable {C : Family G} {f : Extraction.Order} {S : Table C.book} (F : Final C f S) (J : ℝ→PhysMS.tower S)

theorem evaluated (lead : PhysMS.Leading F J) {t : ℝ→ℝ} (small : Tendsto t Trace.Pilot.trail (𝓝 0)) :
    ∃ L : ℝ,0≤L ∧ ∀ᶠ r in Trace.Pilot.trail,
      ‖guide G d (correction F J V d r)-reading V ν T d q (t r)‖ ≤
      L*‖(V.survey d).purse (hierarchy F J d r)-target V ν T d q (t r)‖ := by
  let D := V.survey d
  let H := V.prepared d
  have phys := WilsonPositionPrescribedScreen.warm F J lead V d
  have ms : Tendsto (fun r=>target V ν T d q (t r)) Trace.Pilot.trail (𝓝 D.opening.1) := by
    have a := ((smooth V ν T d q).continuous.tendsto 0).comp small
    rw [anchored] at a
    exact a
  obtain ⟨A,U,nbd,lip⟩ := ((D.train H).of_le (by decide : 1≤ω)).exists_lipschitzOnWith
  refine ⟨(A:ℝ),A.property,?_⟩
  filter_upwards [phys.eventually nbd,ms.eventually nbd] with r hp hm
  have b := lip.dist_le_mul _ hp _ hm
  rw [dist_eq_norm,dist_eq_norm] at b
  change ‖guide G d (D.firstPass H (hierarchy F J d r))-D.route H (target V ν T d q (t r))‖≤_
  rw [D.guid]
  exact b

theorem priced (lead : PhysMS.Leading F J) {t : ℝ→ℝ} (small : Tendsto t Trace.Pilot.trail (𝓝[>]0)) :
    ∃ A L : ℝ,0≤A ∧ 0≤L ∧ ∀ᶠ r in Trace.Pilot.trail,
      ‖guide G d (correction F J V d r) -
        WilsonOrdinaryPositionTaylor.truncation (reading V ν T d q) q (t r)‖ ≤
        L*‖(V.survey d).purse (hierarchy F J d r)-target V ν T d q (t r)‖ + A*(t r)^(q+1) := by
  obtain ⟨L,hL,paid⟩ := evaluated V ν T d q F J lead (small.mono_right nhdsWithin_le_nhds)
  obtain ⟨A,hA,tail⟩ := WilsonOrdinaryPositionTaylor.remainder (reading V ν T d q) (analytic V ν T d q) q
  refine ⟨A,L,hA,hL,?_⟩
  filter_upwards [paid,small.eventually tail] with r bill order
  have tri := dist_triangle (guide G d (correction F J V d r)) (reading V ν T d q (t r))
    (WilsonOrdinaryPositionTaylor.truncation (reading V ν T d q) q (t r))
  simp only [dist_eq_norm] at tri
  exact tri.trans (add_le_add bill order)

end YM.Integration.WilsonPositionPrescribedTariff
