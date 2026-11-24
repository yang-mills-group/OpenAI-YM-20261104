import YM.Integration.WilsonPositionProgramPublicDirectoryGround

/-! The leading independent reflected Gram on the short aligned mesh. The high internal Taylor order only moves the eventual starting index. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPublicPlantedGramBudget
open Filter Set Finset Function Metric MeasureTheory Lattice Maxwell XSpace XSpace.Cirrus XSpace.Normalize
open XSpace.Structure1 FVA2 FVA2.Register FVA2.Scale MS MS.Land PowerSeries
open WilsonPositionRawFiling WilsonPositionProtectedTuplePrice
open WilsonPositionProgramPublicDirectoryCoin
open scoped Topology BigOperators Classical Polynomial
variable {G:Gauge} (Z:WilsonPrescription G) {g:G.Simple}
    {M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {T:Prescription (Press.portDeck G)}
    {dial:Bool} (H:Main.Match Z g M T dial)

private theorem runs {l : Filter ℝ} {t : ℝ→ℝ} (pos : ∀ᶠ r in l,0<t r)
    (small : Tendsto t l (𝓝 0)) : Tendsto (fun r=>-Real.log (t r)) l atTop :=
  tendsto_neg_atTop_iff.mpr (Real.tendsto_log_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨small,pos⟩))

include H in
private theorem mass (q d : ℕ) (C : ℝ) (l : Filter ℝ) {t : ℝ→ℝ}
    (pos : ∀ᶠ r in l,0<t r) (small : Tendsto t l (𝓝 0)) {δ : ℝ} (hd : 0<δ) :
    ∃ i₀:ℕ, ∀ᶠ r in l, ∀ i≥i₀,
      (i:ℝ) ≤ C*(-Real.log (t r))^d →
      (1+WilsonPositionRawMesh.mass Z (Z.run.step i) q)^q*|t r| ≤ δ := by
  obtain ⟨p,hp⟩ := WilsonPositionBareDetectorGrowth.mass Z H q
  let b : ℝ[X] := (1+p)^q
  have deg : b.degree ≤ ((Polynomial.X:ℝ[X])^b.natDegree).degree := by
    rw [Polynomial.degree_X_pow];exact Polynomial.degree_le_natDegree
  obtain ⟨B,hB,h⟩ := (b.isBigO_atTop_of_degree_le _ deg).exists_pos
  have nat := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually h.bound
  have lim : ∀ᶠ i:ℕ in atTop,
      (1+WilsonPositionRawMesh.mass Z (Z.run.step i) q)^q ≤ B*(i:ℝ)^b.natDegree := by
    filter_upwards [nat,hp] with i y x
    have nonneg : 0≤WilsonPositionRawMesh.mass Z (Z.run.step i) q := by
      unfold WilsonPositionRawMesh.mass; positivity
    calc
      _ ≤ (1+p.eval (i:ℝ))^q := pow_le_pow_left₀ (by linarith) (by linarith) q
      _ = b.eval (i:ℝ) := by simp [b]
      _ ≤ ‖b.eval (i:ℝ)‖ := Real.le_norm_self _
      _ ≤ B*(i:ℝ)^b.natDegree := by simpa using y
  obtain ⟨j,hj⟩ := eventually_atTop.mp lim
  let D := d*b.natDegree
  have van : Tendsto (fun x:ℝ=>x^D*Real.exp (-x)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (D:ℝ) 1 zero_lt_one
  have curve : Tendsto (fun r=>B*C^b.natDegree*((-Real.log (t r))^D*Real.exp (-(-Real.log (t r))))) l (𝓝 0) := by
    simpa using (van.comp (runs pos small)).const_mul (B*C^b.natDegree)
  refine ⟨j,?_⟩
  filter_upwards [pos,curve.eventually_lt_const hd] with r hr low i large short
  rw [abs_of_pos hr]
  rw [neg_neg,Real.exp_log hr] at low
  calc
    _ ≤ (B*(i:ℝ)^b.natDegree)*t r := by gcongr; exact hj i large
    _ ≤ (B*(C*(-Real.log (t r))^d)^b.natDegree)*t r := by gcongr
    _ = B*C^b.natDegree*((-Real.log (t r))^D*t r) := by rw [mul_pow,←pow_mul];ring
    _ ≤ δ := low.le

variable {n d:ℕ} (v:Tags G d n) (q:ℕ) {K:Set (Points n)} (compact:IsCompact K) (sep:K⊆conf n)

include H compact sep in
theorem finite (l:Filter ℝ) {t:ℝ→ℝ} (pos:∀ᶠ r in l,0<t r)
    (small:Tendsto t l (𝓝 0)) (D:ℕ) (J:ℝ) {δ:ℝ} (hδ:0<δ) :
    ∃ i₀:ℕ, ∀ᶠ r in l, ∀ i≥i₀,
      (i:ℝ)≤J*(-Real.log (t r))^D → ∀ {B} (P:Handoff.Directory Z i B),
      Handoff.Directory.budget G n d+q≤B → ∀ s:Sample n,s.F=Z.run.step i →
      welcome s → familiar s∈K → ∀u:ℝ, |u|≤8*t r →
      ‖drawValue Z v q P u s.layout - WilsonPositionOriginalEpochQuadrature.point P d v s.layout 0‖ ≤ δ := by
  obtain ⟨C,hC,fees⟩ := remainder Z H v q compact sep
  obtain ⟨i₀,hi⟩ := eventually_atTop.mp fees
  obtain ⟨j,funded⟩:=mass Z H q D J l pos small (δ:=δ/(8*(1+C))) (by positivity)
  refine ⟨max j i₀,?_⟩
  filter_upwards [funded,pos,small.eventually (gt_mem_nhds (show (0:ℝ)<1/8 by norm_num))] with r wages positive low i ge le B P cover s hs hc hK u hu
  let A:=(1+WilsonPositionRawMesh.mass Z (Z.run.step i) q)^q
  have h:0≤WilsonPositionRawMesh.mass Z (Z.run.step i) q := Finset.sum_nonneg fun _ _=>abs_nonneg _
  have ha:0≤A := pow_nonneg (by linarith) _
  have used:=hi i ((le_max_right j i₀).trans ge) P cover s hs hc hK u (by linarith)
  have room:= wages i ((le_max_left j i₀).trans ge) le
  rw [abs_of_pos positive] at room
  have spent:= (le_div_iff₀ (by positivity:0<8*(1+C))).mp room
  change A*t r*(8*(1+C))≤δ at spent
  change _≤C*(A*|u|) at used
  exact used.trans (by nlinarith [mul_nonneg hC (mul_nonneg ha (sub_nonneg.mpr hu)),mul_nonneg ha positive.le])

include H compact sep in
theorem original (l:Filter ℝ) {t:ℝ→ℝ} (pos:∀ᶠ r in l,0<t r)
    (small:Tendsto t l (𝓝 0)) (D:ℕ)(J:ℝ) {δ:ℝ}(hδ:0<δ) :
    ∃ i₀:ℕ, ∀ᶠ r in l, ∀ i≥i₀,
      (i:ℝ)≤J*(-Real.log (t r))^D → ∀ {B} (P:Handoff.Directory Z i B),
      Handoff.Directory.budget G n d+q≤B → ∀ s:Sample n,s.F=Z.run.step i →
      welcome s → familiar s∈K → ∀u:ℝ, |u|≤8*t r →
      ‖WilsonPositionProgramPublicDirectoryCoin.drawValue Z v q P u s.layout -
       Rose.cooked Z.scheme Z.store d s 0 v‖ ≤ δ := by
  obtain ⟨i₀,hi⟩:=eventually_atTop.mp ((goesFront (Expense.Stretched.runs Z.run)).eventually
    (Rose.usable Z.scheme Z.criterion g))
  obtain ⟨j,funded⟩:=finite Z H v q compact sep l pos small D J hδ
  refine ⟨max j i₀,?_⟩
  filter_upwards [funded] with r sal i ge le B P cover s hs hc hK u hu
  rw [←WilsonPositionProgramPublicDirectoryGround.point Z P s hs (hi i ((le_max_right j i₀).trans ge)) (by omega) v]
  exact sal i ((le_max_left j i₀).trans ge) le P cover s hs hc hK u hu
end YM.Integration.WilsonOriginalPublicPlantedGramBudget
