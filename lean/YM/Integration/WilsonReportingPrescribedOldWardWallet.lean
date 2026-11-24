import YM.Integration.WilsonReportingPrescribedOldFreeArms
import YM.Integration.WilsonInvariantActionSpectatorPrices
import YM.Integration.WilsonSeparatedOriginalSlabQArms

/-! Perturbative grade-four action and spectator operands, on one registered
Wilson prescription, with their pre-cutoff source and compact-field bounds. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldWardWallet
open Function Filter Set Finset Lattice Wilson RG Tree Precision Source Labels
open PhysicalNext.Repeat.Legato RGComparison.Core16 RG17 Extraction Table Spec Climb
open MS MS.Local.Physical MS.Theater Maxwell Maxwell.Free StressFlux Trace Trace.Pilot PhysMS
open FVA2 FVA2.Register WilsonReportingPrescribedOldFreeArms WilsonInvariantActionSpectatorPrices
open WilsonPositionHomogeneousFrame
open scoped Classical Topology BigOperators
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (J:ℝ→tower S) (Z:WilsonPrescription G)
    {H:(Bel R.family.book).Hierarchy} (lead:Leading F J)
    (paid:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d) (simple:G.Simple)
    (B:Deck G)

def action : Stock B := (0,fun i=>(WilsonReportingPrescribedOldAction.weights B i:ℂ))
def spectator (r:ℝ) (v:RG17.Free R.family 4) : Stock B :=
  assignment R B simple (freeInput F J Z 4 r v)

def amount (x:Stock B) : ℝ := ‖x.1‖+∑i,‖x.2 i‖

theorem choice (r:ℝ) (v:RG17.Free R.family 4) :
    booking R B (action B)=stepField R.family ∧
    booking R B (spectator F J Z simple B r v)=freeInput F J Z 4 r v := by
  exact ⟨by simpa [booking,action] using (WilsonReportingPrescribedOldFreeArms.action R B).symm,
    assigned R B simple _⟩

include lead paid in
theorem budget (v:RG17.Free R.family 4) : ∃K:ℝ,0<K ∧ ∀ᶠr in trail,
    amount B (action B)+amount B (spectator F J Z simple B r v) ≤ K := by
  have continuous_amount : Continuous (amount B) := by unfold amount;fun_prop
  have observed : Continuous (fun x:Stock B=>amount B (action B)+amount B x) := continuous_const.add continuous_amount
  have compared : Tendsto (fun r=>amount B (action B)+amount B (spectator F J Z simple B r v))
      trail (𝓝 (amount B (action B)+amount B (assignment R B simple v))) :=
    observed.continuousAt.tendsto.comp ((assignment R B simple).continuous_of_finiteDimensional.continuousAt.tendsto.comp
      (WilsonOriginalCompensatedAnchor.field F J Z lead paid simple 4 v))
  let C:=amount B (action B)+amount B (assignment R B simple v)
  refine ⟨max 1 (C+1),zero_lt_one.trans_le (le_max_left ..),?_⟩
  filter_upwards [compared.eventually_lt_const (show C < C+1 by linarith)] with r h
  exact h.le.trans (le_max_right ..)

variable (R) {B} (Q:MS.Land.Prescription B)

def operand (z:Stock B) (clock:ℝ) (k:ℕ) (n:Side) (o:Site n) (U:Config G n) : ℂ :=
  (if k=0 then z.1 else 0)+∑i,z.2 i*ActualOriginalCalibratedColumns.weightedObservable
    R B Q (WilsonReportingPrescribedOldAction.label B i) clock n o U k

include lead paid in
theorem compact (v:RG17.Free R.family 4) (p:ℕ) (μ:ℝ) :
    ∃K:ℝ,0<K ∧ ∃e:ℕ,∀ᶠr in trail,∀(k:ℕ),k≤p→∀(s:ℝ)(n:Side)(o:Site n)(U:Config G n),
      ‖operand R Q (action B) (μ-s) k n o U‖+
      ‖operand R Q (spectator F J Z simple B r v) (μ-s) k n o U‖≤K*(1+‖s‖)^e := by
  obtain ⟨A,ap,cap⟩:=budget F J Z lead paid simple B v
  obtain ⟨C,cp,e,arms⟩:=WilsonSeparatedOriginalSlabQArms.fixed R Q
    (WilsonReportingPrescribedOldAction.label B) p μ
  let M:=max 1 C
  have one:1≤M:=le_max_left ..;have cm:C≤M:=le_max_right ..
  refine ⟨A*M,mul_pos ap (zero_lt_one.trans_le one),e,?_⟩
  filter_upwards [cap] with r money
  intro k kp s n o U
  let t:=(1+‖s‖)^e
  have tp:1≤t:=one_le_pow₀ (by linarith [norm_nonneg s])
  have mt:1≤M*t:=one_le_mul_of_one_le_of_one_le one tp
  have get (z:Stock B) : ‖operand R Q z (μ-s) k n o U‖≤amount B z*(M*t) := by
    let value:=fun i=>ActualOriginalCalibratedColumns.weightedObservable R B Q
      (WilsonReportingPrescribedOldAction.label B i) (μ-s) n o U k
    have first : ‖if k=0 then z.1 else 0‖≤‖z.1‖*(M*t) := by
      calc _ ≤ ‖z.1‖ := by split <;> simp
           _ ≤ _ := le_mul_of_one_le_right (norm_nonneg _) mt
    have paid_arm (i) : ‖z.2 i * value i‖ ≤ ‖z.2 i‖*(M*t) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left ((arms i k kp s n o U).trans
        (mul_le_mul_of_nonneg_right cm (zero_le_one.trans tp))) (norm_nonneg _)
    change ‖(if k=0 then z.1 else 0)+∑i,z.2 i*value i‖≤(‖z.1‖+∑i,‖z.2 i‖)*(M*t)
    rw [add_mul,Finset.sum_mul]
    exact (norm_add_le ..).trans (add_le_add first ((norm_sum_le ..).trans
      (Finset.sum_le_sum (fun i _=>paid_arm i))))
  calc _ ≤ amount B (action B)*(M*t)+amount B (spectator F J Z simple B r v)*(M*t) :=
      add_le_add (get _) (get _)
    _ ≤ _ := by rw [←add_mul,mul_assoc];exact mul_le_mul_of_nonneg_right money (zero_le_one.trans mt)

end YM.Integration.WilsonReportingPrescribedOldWardWallet
