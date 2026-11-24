import YM.Integration.WilsonCenteredNestedElection
import YM.Integration.WilsonCenteredNestedViewer
import YM.Integration.WilsonPhysicalCutoffCurrency

/-! One admitted marked filter, one original physical exterior and the
genuine running coupling at every vertex. Its numerical clock is the
stopping date on the same Wilson run and is chosen before either regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedActual
open OPE OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Tree OPE.Log
open Extraction Spec Table Filter Set Trace.Pilot PhysicalNext.Repeat.Legato
open WilsonCenteredNestedProgram WilsonCenteredNestedIntake
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) (simple : G.Simple)

def amount (B : ℕ) (g : ℝ→ℝ) (a : ℝ) : ℝ :=
  R.family.path.levels.clock.hatBeta (WilsonMeasuredWindow.stop R.family.path.levels simple B a) * g a^2

theorem currency (slow : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (bp : 0 < B)
    (g : ℝ→ℝ) (hg : Coupling G g) {t : Tree} {δ : ℝ} (dp : 0 < δ) :
    ∀ᶠ r:ℝ in 𝓝[>]0,∀ s : t.Inner→ℝ,t.Tapered r 1 s →
    ∀ v,|amount R simple B g (s v) - 1| < δ := by
  have clock := WilsonPhysicalCutoffCurrency.temperature R simple slow bp g hg
  have near : ∀ᶠ a:ℝ in 𝓝[>]0,|amount R simple B g a - 1| < δ := by
    simpa only [Metric.mem_ball,Real.dist_eq,amount] using
      clock.eventually (Metric.ball_mem_nhds (1:ℝ) dp)
  obtain ⟨ρ,rp,seated⟩ := Metric.mem_nhdsWithin_iff.mp near
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0:ℝ) rp)] with r small
  intro s levels v
  have vp := levels.positive v
  have vr := levels.within (le_refl 1) v
  have rpos := vp.trans_le vr
  have atSeat : s v < ρ := vr.trans_lt (by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos rpos] using small)
  exact seated ⟨by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos vp] using atSeat,vp⟩

/-- The signed independently named vertex programme is tested in the same
ordinary Wilson reading as the measured nested truncation, including the
unselected viewer and all scalar and higher deposited fields. -/
theorem original {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (fac : Facilities R.family f S) (l : Ultrafilter (ℕ×ℕ)) (lo : (l : Filter _) ≤ f.fuse)
    (ticket : MatrixTicket (C:=R.family) S F.sector.derivatives (l : Filter _))
    (slow : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (bp : 0 < B)
    (g : ℝ→ℝ) (hg : Coupling G g) (A : Rule F Q) (L : ℝ→ℝ) (Ln : ∀ r,0 ≤ L r)
    {n : ℕ} {p : Fin n→Tree} {I : Type} [Fintype I] (order : ℕ)
    (v : (fork n p).Leaf→S.Tag) (w : I→S.Tag) (H : ℕ) (D : (fork n p).Inner→ℕ)
    (M η ε δ : ℝ) (Mn : 0 ≤ M) (ηp : 0 < η) (ep : 0 < ε) (dp : 0 < δ)
    (rows : localRows F Q A g L (fun a=>|g a|^order) M η (fork n p) v D H) :
    Nesting.Uniform F Q ∧ LogTrace F Q.port ∧
    ∃ b : Fin (H+1)→ℝ,(∀j,0 ≤ b j) ∧
    ∀ᶠ r:ℝ in 𝓝[>]0,∀ (s : (fork n p).Inner→ℝ) (z : (fork n p).Plot) (y : I→E4),
      Accept r M η s z → Buffer z y δ →
      (∀ i,|amount R simple B g (s i)-1| < ε) ∧ ∀ q : Viewers F,
      ‖whole (spectator F q) (Tree.profile z) (voices v) y (voices w) -
        WilsonCenteredNestedViewer.predicted F Q A g v w H D s z y q‖ ≤
      toll (wages v) ε (H+1:ℝ) s + ∑ j : Fin (H+1),∑ c : Q.channels j,
        (bothToll (wages v) ε j D s +
          WilsonCenteredNestedPhysical.vertexFee F Q s v D j L (fun a=>|g a|^order)) *
        (b j * ‖Q.actor j c‖) := by
  obtain ⟨uniform,raw⟩ := WilsonCenteredNestedElection.on_ticket R F Q fac l lo ticket
  obtain ⟨b,bn,read⟩ := WilsonCenteredNestedViewer.original F Q fac.toServices A g L Ln order
    v w H D M η ε δ Mn ηp ep dp rows
  refine ⟨uniform,raw,b,bn,?_⟩
  filter_upwards [currency R simple slow bp g hg (t:=fork n p) ep,read] with r clock bound
  exact fun s z y accept clear=>⟨clock s accept.levels,bound s z y accept clear⟩

end YM.Integration.WilsonCenteredNestedActual
