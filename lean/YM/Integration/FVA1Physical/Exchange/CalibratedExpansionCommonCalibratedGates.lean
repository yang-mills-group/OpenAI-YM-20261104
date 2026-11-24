import YM.Integration.FVA1Physical.Exchange.ContinuumLimitThermometer

set_option autoImplicit false

namespace YM.Integration.FVA1Physical.Exchange.CalibratedExpansion

open Function Filter Set Topology
open XSpace XSpace.Cirrus XSpace.Expense XSpace.TestBudget XSpace.Normalize XSpace.Structure1
open MS MS.Local.Physical MS.Menus MS.Land MS.Book MS.Book.Program MS.Book.Convolve
open MS.High MS.High.Knobs MS.Outlook MS.Wind MS.Wind.Leading MS.Motif MS.Mach MS.Dock MS.Hem
open FVA2 FVA2.Position WilsonMS
open scoped Topology Classical

private theorem senses_of_vitals {n : ℕ} {u : Sample n → ℂ} {p : Points n → ℂ}
    (cont : ContinuousOn p (conf n))
    (paid : ∀ (K : Set (Points n)), IsCompact K → K ⊆ conf n → FrameConj.Vitals u p K) :
    Senses (conf n) u p := by
  intro x hx
  obtain ⟨r, hr, collar⟩ := Metric.mem_nhds_iff.mp ((conf_open n).mem_nhds hx)
  let K := Metric.closedBall x (r / 2)
  have within : K ⊆ conf n :=
    (Metric.closedBall_subset_ball (show r / 2 < r by linarith)).trans collar
  obtain ⟨a, ha, D, _, bill⟩ := (paid K (isCompact_closedBall ..) within).run
  have inK : ∀ᶠ i in Gate x, familiar i ∈ K :=
    (senseG x).eventually (Metric.closedBall_mem_nhds _ (by positivity))
  have err : Tendsto (fun i => ‖u i - p (familiar i)‖) (Gate x) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _)
      (g := fun i : Sample n => D * VisitH.FareP a i.F)
    · filter_upwards [inK, welcomeG x, (liftG x).eventually bill] with i hi hw h
      exact h i.layout i.center hw hi
    have HT := ((VisitH.fare_limit ha).comp (liftG x)).const_mul D
    rw [mul_zero] at HT
    exact HT
  have limit := (cont.continuousAt ((conf_open n).mem_nhds hx)).tendsto.comp (senseG x)
  have joined := ((tendsto_zero_iff_norm_tendsto_zero).mpr err).add limit
  rw [zero_add] at joined
  exact joined.congr fun i => sub_add_cancel _ _

variable {G : Gauge}

theorem original_calibrated_gate_of_team (μ : ℝ) (W : Initialize G) (V : Store G)
    (S : Prescription (Press.portDeck G)) (A : Prescription (Ensure.deck G))
    {O : Booked (Press.portDeck G)} (T : MS_Data G O)
    {M : Booked (Ensure.deck G)} (F : MS_Data G M) (h : G.Simple)
    (hs : TaylorOKF T (Press.wickInput W) S) (hr : Favors.Horder S) (hv : Ace.UnitP S)
    (ha : BMenu.Installed W F A) (hc : Rider.Commuting A) (team : S.team = A.team)
    (n d k : ℕ) (v : Tags G d n) (x : Points n) (hx : x ∈ conf n) :
    Reg.State.wall μ V T d x k v = FrameConj.Gates.Thaw V F μ d x k v := by
  have wilson := senses_of_vitals ((FrameConj.Gates.theorem_F V μ F d n) k v).1
    (fun K compact within => FrameConj.Gates.picture_cost W V A μ F h ha hc compact within d k v)
  apply tendsto_nhds_unique _ (wilson x hx)
  apply (Reg.State.moveT μ W V S T h hs hr hv v k x hx).congr'
  filter_upwards [(liftG x).eventually (continuumLimit_reset μ S A team)] with i hi
  rw [hi]

theorem original_filed_calibrated_gates (W : Initialize G)
    (T : MS_Data G (OpenAxis.Plot (Press.portDeck G)))
    (F : MS_Data G (JRad.book G)) (h : G.Simple) :
    ∀ (μ : ℝ) (V : Store G) (n d k : ℕ) (v : Tags G d n) (x : Points n),
      x ∈ conf n → Reg.State.wall μ V T d x k v = FrameConj.Gates.Thaw V F μ d x k v := by
  obtain ⟨A, hc, ha⟩ := Rider.Equipped W F h
  have hb : Fixed (col (skyline G A.team)) (Archive 4 T.bulk) true 4 1 := by
    rw [← continuumLimit_ms_bulk F T]
    exact ha.bulk
  obtain ⟨S, ht, hs⟩ := continuumLimit_fund_team W T h A.team hb
  intro μ V n d k v x hx
  exact original_calibrated_gate_of_team μ W V S A T F h hs.Taylor hs.still hs.base
    ha hc ht n d k v x hx

theorem original_filed_calibrated_reports (W : Initialize G)
    (T : MS_Data G (OpenAxis.Plot (Press.portDeck G)))
    (F : MS_Data G (JRad.book G)) (h : G.Simple) (μ : ℝ) (V : Store G) (d k : ℕ) :
    Reg.State.author μ V T d k = FrameConj.Gates.thawed V F μ d k := by
  ext1 n
  ext1 t
  ext1 v
  rw [Reg.State.exact_trace μ V T t v, ((FrameConj.Gates.theorem_F V μ F d n) k v).2 t]
  exact Test.apply_eq _ (fun x hx => original_filed_calibrated_gates W T F h μ V n d k v x hx)

theorem original_first_triple_income (W : Initialize G) (V : Store G) (P : Rose.Pick V)
    (T : MS_Data G (OpenAxis.Plot (Press.portDeck G)))
    (F : MS_Data G (JRad.book G)) (h : G.Simple) (μ : ℝ) :
    (Rose.test P).applyTo (fun x => Reg.State.wall μ V T 6 x 1 (Rose.tag G)) = (Rose.c_T P : ℂ) ∧
    (Rose.test P).applyTo (fun x => FrameConj.Gates.Thaw V F μ 6 x 1 (Rose.tag G)) =
      (Rose.c_T P : ℂ) := by
  have fitted := original_filed_calibrated_gates W T F h μ V
  have free (x : Points 3) (hx : x ∈ conf 3) :
      FrameConj.Gates.Thaw V F μ 6 x 0 = XSpace.Normalize.scene (G := G) x 6 := by
    ext v
    rw [← fitted 3 6 0 v x hx]
    exact congrArg (fun b : Point G 6 3 => b v) (Reg.State.spirit (d := 6) μ V T x hx)
  have raw := Test.apply_eq (Rose.test P)
    (fun x hx => Rose.tangent W h (FrameConj.Gates.Thaw V F μ 6 x) (free x hx) hx)
  obtain ⟨A, hc, ha⟩ := Rider.Equipped W F h
  have first := FrameConj.trueFirst μ P W A F h ha hc
  change PowerSeries.coeff 1 (FrameConj.observed P (FrameConj.Gates.Thaw V F μ 6)) = 1 at first
  rw [FrameConj.takes P (FrameConj.Gates.Thaw V F μ 6) 1 one_ne_zero] at first
  change (Rose.c_T P : ℂ)⁻¹ *
    (Rose.test P).applyTo (fun x => PowerSeries.coeff 1
      (Rose.b3 (Rose.batchT (FrameConj.Gates.Thaw V F μ 6 x)))) = 1 at first
  rw [raw] at first
  have value :
      (Rose.test P).applyTo (fun x => FrameConj.Gates.Thaw V F μ 6 x 1 (Rose.tag G)) =
        (Rose.c_T P : ℂ) := by
    have nz : (Rose.c_T P : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr P.fresh.ne
    calc
      _ = (Rose.c_T P : ℂ) * ((Rose.c_T P : ℂ)⁻¹ *
        (Rose.test P).applyTo (fun x => FrameConj.Gates.Thaw V F μ 6 x 1 (Rose.tag G))) := by
          rw [← mul_assoc, mul_inv_cancel₀ nz, one_mul]
      _ = _ := by rw [first, mul_one]
  exact ⟨(Test.apply_eq (Rose.test P) (fun x hx => fitted 3 6 1 (Rose.tag G) x hx)).trans value, value⟩

end YM.Integration.FVA1Physical.Exchange.CalibratedExpansion
