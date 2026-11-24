import YM.RGComparison.Core16.Astage.Layouts
import YM.Integration.WilsonMatrixTicketLanesReportedPivot
import YM.Integration.WilsonMatrixTicketLanesReportedCurrency
import YM.Integration.WilsonFundedMeasuredWindow

/-! Positive spatial order of the true identity-output OPE on the purchased near-mesh fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedSpatial
open Filter Function Real Set MeasureTheory OPE Table OPE.Orbits Spec Extraction Wilson
open RGComparison.Core16.Astage RGComparison.Core16.Astage.Panel PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) (simple : G.Simple)

include simple in
/-- Every positive spatial power purchases every power of the same genuine cutoff coupling. -/
theorem beyond {ι E : Type} [Norm E] {l : Filter ι} {m : ι → ℕ} (hm : Tendsto m l atTop)
    {e : ι → E} {σ : ℝ} (pos : 0 < σ) (h : RateLE l (ruler R.family m) e (-σ)) :
    ∀ q : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ N p, m i ≤ N →
      ‖e i‖ ≤ ε * Pert.Asymptotics.regulatorRun R.family N p (m i) ^ q := by
  intro q ε he
  let t := ruler R.family m
  let Λ := budgetLog R.family m
  have Q : 0 < (q:ℝ)+1 := by positivity
  have ratio : Tendsto (fun i => Λ i / t i) l (𝓝 0) := negligible R.family simple hm
  have allowance : 0 < σ / (4*((q:ℝ)+1)) := by positivity
  have late : Tendsto t l atTop := large_s R.family hm
  filter_upwards [h (-σ/2) (by linarith), ratio.eventually (gt_mem_nhds allowance),
    late.eventually_gt_atTop 0, late.eventually_ge_atTop (-(4*log ε)/σ)] with i hx hi ht hε
  intro N p hN
  have hΛ : 0 ≤ Λ i := (RG16.Literal.lambda_pos R.family (m i)).le
  have cost := (div_lt_div_iff₀ ht (by positivity : 0 < 4*((q:ℝ)+1))).mp hi
  have small := (div_le_iff₀ pos).mp hε
  have step : -σ/2*t i ≤ log ε + (-(q:ℝ))*Λ i := by nlinarith
  calc
    ‖e i‖ ≤ exp (-σ/2*t i) := hx
    _ ≤ exp (log ε + (-(q:ℝ))*Λ i) := exp_le_exp.mpr step
    _ = ε * exp ((-(q:ℝ))*Λ i) := by rw [exp_add, exp_log he]
    _ ≤ ε * Pert.Asymptotics.regulatorRun R.family N p (m i) ^ q :=
      mul_le_mul_of_nonneg_left (WilsonMatrixTicketLanesReportedCurrency.clock R (m i) N p q hN) he.le

variable {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
    (service : Services R.family f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def entered {I : Type} {U : Filter (ℕ × ℕ)} (A : Axle.TransferLimit R.family R.makes U)
    (d : I → ℕ) (v : ∀ j, R.family.label (d j)) (m : ℕ) : Labels S d :=
  fun j => Axle.full F (d j) A m (v j)

private def emptyPositions : Fin 0 → E4 := Fin.elim0
private def emptyFields : Labels S (fun _ : Fin 0 => 0) := Fin.elim0

/-- The literal signed physical phase correlation minus its exact identity-output OPE. -/
def difference {I K : Type} [Fintype I] {d : I → ℕ} (t : Finset K) (c : K → ℂ)
    (x : K → I → E4) (a : Labels S d) (z : Viewers F) : ℂ :=
  (∑ j ∈ t, c j * Orbits.whole (spectator F z) (x j) a emptyPositions (emptyFields (S:=S))) -
    upon (spectator F z) 0 0 emptyPositions (emptyFields (S:=S))
      (∑ j ∈ t, c j • Q.packet 0 (x j) a 0)

private def atomic {K : Type} [MeasurableSpace K] (t : Finset K) : Measure K :=
  ∑ j ∈ t, Measure.dirac j

private theorem integrable {K E : Type} [MeasurableSpace K] [MeasurableSingletonClass K]
    [NormedAddCommGroup E] (t : Finset K) (v : K → E) : Integrable v (atomic t) := by
  exact integrable_finsetSum_measure.mpr fun j _ => integrable_dirac (by simp)

private theorem amount {K E : Type} [MeasurableSpace K] [MeasurableSingletonClass K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (t : Finset K) (v : K → E) : ∫ j, v j ∂atomic t = ∑ j ∈ t, v j := by
  unfold atomic
  rw [integral_finsetSum_measure (fun _ _ => integrable_dirac (by simp))]
  simp

private theorem atomized {I K : Type} [Fintype I] [MeasurableSpace K] [MeasurableSingletonClass K]
    {d : I → ℕ} (a : Labels S d) (z : Viewers F) (t : Finset K) (c : K → ℂ) (x y : K → I → E4)
    (same : ∀ j ∈ t, y j = x j) :
    sales (atomic t) c y (spectator F z) a emptyPositions (emptyFields (S:=S)) -
        upon (spectator F z) 0 0 emptyPositions (emptyFields (S:=S))
          (sampled F Q 0 (atomic t) c y 0 a) = difference R F Q t c x a z := by
  have signed : (∑ j ∈ t, c j * Orbits.whole (spectator F z) (y j) a emptyPositions (emptyFields (S:=S))) =
      ∑ j ∈ t, c j * Orbits.whole (spectator F z) (x j) a emptyPositions (emptyFields (S:=S)) := by
    exact Finset.sum_congr rfl fun j hj => congrArg
      (fun positions => c j * Orbits.whole (spectator F z) positions a emptyPositions (emptyFields (S:=S))) (same j hj)
  have posted : (∑ j ∈ t, c j • Q.packet 0 (y j) a 0) = ∑ j ∈ t, c j • Q.packet 0 (x j) a 0 :=
    Finset.sum_congr rfl fun j hj => congrArg (fun positions => c j • Q.packet 0 positions a 0) (same j hj)
  unfold sales sampled difference
  simp only [amount, signed, posted]

include service in
/-- All signed reported rosters use the same genuine upper-cutoff inverse and the same physical final and reader. -/
theorem original {ι I K : Type} [Fintype I] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K]
    {l : Filter ι} [l.NeBot] {r : ι → ℝ} (hr : Tendsto r l (𝓝[>] 0))
    (B : ℕ) (hB : 20 < B) (pace : WilsonWindowReportingPace.Slow R.kit) (U : Ultrafilter (ℕ × ℕ)) (hu : (U : Filter (ℕ × ℕ)) ≤ f.fuse)
    (d : I → ℕ) (v : ∀ j, R.family.label (d j)) (roster : ι → Finset K)
    (occupied : ∀ i, (roster i).Nonempty) (c : ι → K → ℂ) (x : ι → K → I → E4)
    {M η : ℝ} (Mpos : 0 ≤ M) (ηpos : 0 < η)
    (geometry : ∀ᶠ i in l, ∀ j ∈ roster i, OPE.WithinRoom (r i) M η (x i j) 0)
    (paid : RateLE l (ruler R.family (fun i => WilsonMeasuredWindow.stop R.family.path.levels simple B (r i)))
      (fun i => ∑ j ∈ roster i, ‖c i j‖) 0) (z : ι → Viewers F) :
    let m := fun i => WilsonMeasuredWindow.stop R.family.path.levels simple B (r i)
    ∃ A : Axle.TransferLimit R.family R.makes U,
      (∀ h b, R.family.ref h ≤ b → ∀ v : R.family.label h,
        Tendsto (fun j : ℕ × ℕ => Axle.root R.makes h b j.1 j.2 v) U (𝓝 (A.fieldMap h b v)) ∧
        ∀ N p, b ≤ N → Next.UVStress.quota R.family h b N p (Axle.root R.makes h b N p v) ≤
          R.family.S.a b ^ h * (Axle.cost R.family h b * ‖v‖)) ∧
      let error := fun i => difference R F Q (roster i) (c i) (x i) (entered R F A d v (m i)) (z i)
      RateLE l (ruler R.family m) error (-1) ∧ ∀ q : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l,
        ∀ N p, m i ≤ N → ‖error i‖ ≤ ε * Pert.Asymptotics.regulatorRun R.family N p (m i) ^ q := by
  intro m
  have hm : Tendsto m l atTop := (WilsonMeasuredWindow.stop_tendsto R.family.path.levels simple B (by omega)).comp hr
  have radial : RateIs l (ruler R.family m) r (-1) := by
    apply Layouts.room (C:=R.family) simple hm (β:=(B:ℝ)) (by exact_mod_cast hB)
    have h0 : Tendsto r l (𝓝 0) := hr.mono_right nhdsWithin_le_nhds
    filter_upwards [hr.eventually self_mem_nhdsWithin,
      h0.eventually (ge_mem_nhds (R.family.S.a_pos 0))] with i hi hlow
    exact_mod_cast WilsonMeasuredWindow.window R.family.path.levels simple B (WilsonFundedMeasuredWindow.paced R pace) (by omega) hi hlow
  obtain ⟨A, purchased⟩ := WilsonMatrixTicketLanesReportedPivot.filed R U hu
  refine ⟨A, purchased, ?_⟩
  let a := fun i => entered R F A d v (m i)
  let y := fun i j => if j ∈ roster i then x i j else x i (occupied i).choose
  have valid (i : ι) (j : K) (h : j ∈ roster i) : y i j = x i j := if_pos h
  have legal (k : ι → K) : enveloped l (ruler R.family m) 1 (fun i => y i (k i)) 0 ∧
      Kept l (ruler R.family m) 1 (fun i => y i (k i)) := by
    apply Layouts.shape hm Mpos ηpos radial
    filter_upwards [geometry] with i h
    by_cases inside : k i ∈ roster i
    · simpa only [y, if_pos inside, Pi.zero_apply] using h (k i) inside
    · simpa only [y, if_neg inside, Pi.zero_apply] using h (occupied i).choose (occupied i).choose_spec
  have invested (j : I) : Axle.Crew (U : Filter (ℕ × ℕ)) (κ:=l) (m:=m) (fun i => a i j) :=
    Axle.on_roots F (d j) hu A service hm (fun _ => v j) (RateLE.const (v j) (large_s R.family hm))
  have flat : Intervals l (ruler R.family m) 0 (sole ∘ (0 : ι → E4)) (fun _ => emptyPositions) :=
    fun _ _ => Eventually.of_forall fun _ _ j => Fin.elim0 j
  have far : Kept l (ruler R.family m) 0 (fun _ => emptyPositions) :=
    fun _ _ => Eventually.of_forall fun _ j => Fin.elim0 j
  have size : RateLE l (ruler R.family m) (fun i => ∫ j, ‖c i j‖ ∂atomic (roster i)) 0 := by
    simpa only [amount] using paid
  have raw := true_balance F service Q hu hm 0 a invested (emptyFields (S:=S)) (x:=y)
    (o:=(0 : ι → E4)) (p:=c) (μ:=fun i => atomic (roster i)) (y:=fun _ => emptyPositions) z legal
    (Eventually.of_forall fun i => integrable _ _) size (Eventually.of_forall fun i => integrable _ _)
    flat far (Eventually.of_forall fun i => integrable _ _)
  have qualified : RateLE l (ruler R.family m)
      (fun i => difference R F Q (roster i) (c i) (x i) (a i) (z i)) (-1) := by
    apply (raw.mono (by norm_num)).congr
    apply Eventually.of_forall
    intro i
    exact atomized R F Q (a i) (z i) (roster i) (c i) (x i) (y i) (valid i)
  exact ⟨qualified, beyond R simple hm zero_lt_one qualified⟩

end YM.Integration.WilsonMatrixTicketLanesReportedSpatial
