import YM.Integration.WilsonMacroscopicRichMeasuredGram
import YM.SchemeConversionRG11.Read.Nested
import YM.SchemeConversionRG11.Maxwell.Frozen

/-! The literal multi-slot position tests of the original position
prescription receive the original positive continuum at every real radius.
The purchased Maxwell rank and nested polls precede every measured radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOrdinaryPositionPoll
open Function Filter Matrix Pert Pert.Position MeasureTheory Set Extra.FD
open Next.UVStress SchemeConversionRG11 SchemeConversionRG11.Detector
open Extraction Table Spec Climb OPE OPE.Orbits PhysMS Maxwell Trace.Pilot
open private weight from YM.Integration.WilsonPhysicalExteriorProfiles
open scoped Topology Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
  (F : Final C f S) (J : ℝ→PhysMS.tower S)

theorem nested (hG : G.Simple) : ∃ P : (d : ℕ)→Poll C.labels d, Poll.FamilyMenu P :=
  Poll.menu_of_rank (fun d=>SchemeConversionRG11.Corona.frozen C.labels hG d)

def reading {n d : ℕ} (t : Test n) (r : ℝ) (v : Fin n→E C.labels d) : ℂ :=
  t.applyTo (PhysMS.measured F none (J r) (d:=fun _=>d) v r)

theorem regular {n d : ℕ} (v : Fin n→E C.labels d) {r : ℝ} (hr : 0<r) :
    ContinuousOn (PhysMS.measured F none (J r) (d:=fun _=>d) v r) (conf n) := by
  let z (i : Fin n) : S.Tag := ⟨d,J r d (v i)⟩
  intro x hx
  exact (((S.class_smooth (spectator F none) (spectate F none).smooth z).contDiffAt
    ((conf_open _).mem_nhds (Work.A05.smul_conf hr hx))).continuousAt.comp
    (continuousAt_id.const_smul r)).continuousWithinAt

theorem tends (L : PhysMS.Leading F J) {n d : ℕ} (t : Test n) (v : Fin n→E C.labels d) :
    Tendsto (fun r=>reading F J t r v) trail (𝓝 (t.applyTo (WickGoal (C:=C) (d:=fun _=>d) v))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let mass := ∫ x,‖t x‖
  have hs : 0 ≤ mass := integral_nonneg fun _=>norm_nonneg _
  let δ := ε/(mass+1)
  have hδ : 0<δ := div_pos hε (by linarith)
  have small : mass*δ<ε := calc
    _ < (mass+1)*δ := mul_lt_mul_of_pos_right (lt_add_one _) hδ
    _ = ε := by dsimp [δ];field_simp
  have A := L.lead n (fun _=>d) v 0 _ t.hasCompactSupport t.tsupport_subset
  have free : ContinuousOn (WickGoal (C:=C) (d:=fun _=>d) v) (conf n) :=
    fun x hx=>(WickGoal_tied v hx).continuousAt.continuousWithinAt
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp A δ hδ,RG17.positiveLength] with r bought rp
  let a := PhysMS.measured F none (J r) (d:=fun _=>d) v r
  let b := WickGoal (C:=C) (d:=fun _=>d) v
  change dist (t.applyTo a) (t.applyTo b)<ε
  rw [dist_eq_norm,←test_sub a b (regular F J v rp) free t]
  refine (weight t (a-b) δ ?_).trans_lt small
  intro x hx
  have price := bought x hx
  rw [dist_comm,dist_eq_norm] at price
  have jets : iteratedFDeriv ℝ 0 a x-iteratedFDeriv ℝ 0 b x=iteratedFDeriv ℝ 0 (a-b) x := by ext z;simp
  change ‖iteratedFDeriv ℝ 0 a x-iteratedFDeriv ℝ 0 b x‖<δ at price
  rw [jets,norm_iteratedFDeriv_zero] at price
  exact price.le

def ledger {d : ℕ} (P : Poll C.labels d) (r : ℝ) : Ledger P.board :=
  fun i k=>(reading F J (P.table i).f r (fun j=>baring C.labels d (k j)))

theorem original (L : PhysMS.Leading F J) {d : ℕ} (P : Poll C.labels d) :
    Tendsto (ledger F J P) trail (𝓝 (white P.board)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro k
  exact tends F J L (P.table i).f (fun j=>baring C.labels d (k j))

end YM.Integration.WilsonOrdinaryPositionPoll
end

