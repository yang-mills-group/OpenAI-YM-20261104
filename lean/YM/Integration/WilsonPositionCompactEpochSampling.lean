import YM.Integration.WilsonPositionProtectedTuplePrice
import YM.Integration.WilsonPositionEpochCellTariff
import YM.Integration.WilsonPositionBareScalarDiagonal

/-! On every translated center used by the actual Handoff, pay the Wilson array in the
compact within-cell quadrature by the original position bound and the logarithmic cutoff
mass of its bare coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionCompactEpochSampling
open Filter Set Finset Function Metric MeasureTheory Lattice Maxwell XSpace XSpace.Cirrus XSpace.Normalize XSpace.TestBudget
open XSpace.Structure1 FVA2 FVA2.Register MS MS.Land PowerSeries
open WilsonPositionEpochCellTariff WilsonPositionProtectedTuplePrice
open scoped Topology BigOperators Classical
variable {G : Gauge} (Z : WilsonPrescription G) {g : G.Simple}
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {T : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z g M T dial)
    {n d : ℕ} (q : ℕ) (φ : Test n) (v : Tags G d n)

private theorem entry (s : Sample n) (large : 16 ≤ s.F.p.side.val) (unit : s.F.spacing ≤ 1)
    (center : s.center∈s.F.Box) : Notch.Entry (1/16) s := by
  left
  intro x
  have h : Arrival.Schedule.Sized s := ⟨large,unit,center⟩
  change (1/16:ℝ)*_ ≤ _
  linarith [MS.Vista.E_n _ (Arrival.Schedule.cleared s h x)]

include H in
theorem centers :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ i : ℕ in atTop, ∀ {B} (P : Handoff.Directory Z i B),
      Handoff.Directory.budget G n d + q ≤ B → ∀ (u : ℝ), |u|≤1 →
      ∀ c∈(Z.run.step i).Box, ‖sampled (Z.run.step i) φ (data P d q v (u:ℂ)) c-
        submitted (Z.run.step i) φ (data P d q v (u:ℂ)) c‖ ≤ C*weight Z q (Z.run.step i)^q*(Z.run.step i).spacing := by
  let K := tsupport (φ:Points n→ℂ)
  have hK : IsCompact K := φ.hasCompactSupport
  obtain ⟨b,hb,chart⟩ := bound_fin φ
  obtain ⟨Δ,positive,sep⟩ := hK.exists_cthickening_subset_open (conf_open n) φ.tsupport_subset
  have image := (hK.image continuous_norm).bddAbove
  obtain ⟨D,hD⟩ := image
  obtain ⟨C,hC,rows⟩ := WilsonPositionProtectedTuplePrice.actual Z H v q (K:=cthickening Δ K)
    hK.cthickening sep (by norm_num : (0:ℝ)<1/16)
  let V := volume.real (closedBall (0:Points n) (D+4*n))
  refine ⟨b*(4*n)*C*V,by dsimp [V];positivity,?_⟩
  have small := (frontier.endpt.comp H.onSchedule).const_mul (4*n:ℝ)
  have at0 : Tendsto (fun i => (4*n:ℝ)*(Z.run.step i).spacing) atTop (𝓝 0) := by
    simpa only [mul_zero,comp_apply,Expense.a,id_eq] using small
  filter_upwards [rows,at0.eventually_lt_const positive,H.onSchedule.eventually frontier.smaller,
    (frontier.horizon.comp H.onSchedule).eventually_ge_atTop 16] with i words margin thin large
  intro B P cover u hu c hc
  let m := Z.run.step i
  have width (c) (hc : c∈m.Box) (x : m.Tuple (n:=n)) (used : ∃y∈m.cell c (m.back x),
      m.rel (m.back x) c∈K ∨ y∈K) :
      ‖data P d q v (u:ℂ) x‖≤ C*weight Z q m^q := by
    let s : Sample n := ⟨m,m.back x,c⟩
    have rooted : familiar s∈cthickening Δ K := by
      rcases used with ⟨y,hy,leg|test⟩
      · exact (self_subset_cthickening K) leg
      · exact mem_cthickening_of_dist_le (familiar s) y Δ K test ((m.upper_corner c hy).trans margin.le)
    exact words P cover s rfl (entry s (by exact_mod_cast (show (16:ℝ) ≤ (s.F.p.side.val:ℝ) from large)) thin hc) rooted u hu
  have fee : 0≤C*weight Z q m^q := by
    have hm : 0≤WilsonPositionRawMesh.mass Z m q := sum_nonneg fun _ _=>abs_nonneg _
    unfold weight
    positivity
  have h := WilsonPositionEpochCellTariff.difference m φ (data P d q v (u:ℂ)) c thin chart fee
    (fun x hx=>hD (mem_image_of_mem _ hx)) (width c hc)
  refine h.trans_eq ?_
  dsimp only [V,m]
  ring

include H in
theorem formal :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ i : ℕ in atTop, ∀ {B} (P : Handoff.Directory Z i B),
      Handoff.Directory.budget G n d + q ≤ B → ∀ (u : ℝ), |u|≤1 →
      ∀ ε value, (∀ c∈(Z.run.step i).Box, ‖submitted (Z.run.step i) φ (data P d q v (u:ℂ)) c-value‖ ≤ ε) →
      ‖(∑ k∈range (q+1), WilsonPositionRawEpoch.row Z P d φ v k*(u:ℂ)^k)-value‖ ≤
        C*weight Z q (Z.run.step i)^q*(Z.run.step i).spacing+ε := by
  obtain ⟨C,hC,checks⟩ := centers Z H q φ v
  refine ⟨C,hC,?_⟩
  filter_upwards [checks] with i hi B P cover u hu ε value hears
  let m := Z.run.step i
  let Y (s : Sample n) := ∑ k∈range (q+1),WilsonPositionOriginalEpochQuadrature.point P d v s.layout k*(u:ℂ)^k
  rw [WilsonPositionOriginalEpochQuadrature.whole]
  change ‖Deposit m Y φ-value‖ ≤ _
  apply homeward_price m φ Y value _
  intro c hc
  rw [stroll]
  change ‖sampled m φ (data P d q v (u:ℂ)) c-value‖ ≤ _
  have hf := hi P cover u hu c hc
  calc
    _ ≤ ‖sampled m φ (data P d q v (u:ℂ)) c-submitted m φ (data P d q v (u:ℂ)) c‖ +
        ‖submitted m φ (data P d q v (u:ℂ)) c-value‖ := by
      simpa only [dist_eq_norm] using dist_triangle (sampled m φ (data P d q v (u:ℂ)) c)
        (submitted m φ (data P d q v (u:ℂ)) c) value
    _ ≤ _ := add_le_add hf (hears c hc)

end YM.Integration.WilsonPositionCompactEpochSampling
