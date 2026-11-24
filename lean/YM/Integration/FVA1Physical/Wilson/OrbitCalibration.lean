import YM.Integration.FVA1Physical.Wilson.OrbitLaw
import YM.MSbar.Tonic.Loan

/-! Signed local tests for the complete physical exterior average. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Lattice RG YM.Wilson Tree MSbar MSbar.Heath MSbar.Heath.Cottage MSbar.Bulk
open scoped Classical Topology
variable {G : Gauge} {c f : Side} {S : StepData c f} {R : Rep G f} {V : Config G c}
variable {F : Forest S.ratio} {X Y : Support f} {A : Set (Config G f)} {r φ : Config G f → ℝ}
variable {σ C δ Λ w a κ χ : ℝ}
local notation "I" => board F X
local notation "E" => MSbar.Bulk.expect S R V
local notation "T" => Rota.resample F I r A

lemma resample_vscale (v : ℝ) (φ : Config G f → ℝ) : T (v • φ)=v • T φ := by
  funext U
  unfold Rota.resample Rota.ghat
  change (∫ t:IV F I G,spec A U*(r (twirl F I t U)*(v*φ (twirl F I t U))) ∂fence F I G) = _
  simp_rw [show ∀t:IV F I G,spec A U*(r (twirl F I t U)*(v*φ (twirl F I t U))) =
    v*(spec A U*(r (twirl F I t U)*φ (twirl F I t U))) from fun _=>by ring]
  rw [integral_const_mul]; rfl

theorem signed_tact (adm : Admitted V R S σ C δ Λ w) (rota : Rota (S:=S) R V Y F I A r a κ)
    (tact : Tonic.Loan.Tact F X A r Y R V 1 χ) (loc : GaugeLocal S Y φ)
    (bound : ∀ U, |φ U| ≤ 1) : Envelope (T φ) ∧ |E (T φ) - E φ| ≤ 4*χ := by
  let h : Config G f → ℝ := (1/2:ℝ) • φ
  have loc' : GaugeLocal S Y h := ⟨(Envelope.const _).mul loc.currency,
    fun i hi U=>congrArg ((1/2:ℝ)*·) (loc.turn i hi U),
    fun U W same=>congrArg ((1/2:ℝ)*·) (loc.located U W same)⟩
  have b' (U : Config G f) : |h U| ≤ 1/2 := by
    change |(1/2:ℝ)*φ U| ≤ _
    rw [abs_mul,abs_of_nonneg (by norm_num : 0≤(1/2:ℝ))]
    exact (mul_le_mul_of_nonneg_left (bound U) (by norm_num)).trans_eq (mul_one _)
  have cal : Tonic.Loan.Tact F X A r Y R V (2*(1/2:ℝ)) χ := by norm_num; exact tact
  obtain ⟨_,_,err⟩ := Tonic.Loan.terms σ C Λ δ w F X Y adm rota h loc' b' cal
  have ev : Envelope (T φ) := by
    unfold Rota.resample
    exact unroll (f:=fun p:Config G f × IV F I G=>Rota.ghat r p.2 φ A p.1)
      (backdrop (Rota.stereo adm rota φ loc) measurable_swap)
  refine ⟨ev,?_⟩
  change |E (T ((1/2:ℝ) • φ))-E ((1/2:ℝ) • φ)| ≤ _ at err
  rw [resample_vscale,e_mul,e_mul,←mul_sub,abs_mul,abs_of_nonneg (by norm_num : 0≤(1/2:ℝ))] at err
  linarith only [err]

lemma expect_difference (adm : Admitted V R S σ C δ Λ w) {p q : Config G f → ℝ}
    (mq : Measurable q) (hp : Envelope p) {b : ℝ} (close : ∀ U, |q U-p U| ≤ b) :
    |E q-E p| ≤ b := by
  let d := fun U=> q U-p U
  have ed : Envelope d := ⟨mq.sub hp.meas, b, fun U=>close U⟩
  have lo := nn V adm ed (Envelope.const (-b)) (fun U=>(abs_le.mp (close U)).1)
  have hi := nn V adm (Envelope.const b) ed (fun U=>(abs_le.mp (close U)).2)
  have sum := e_sum V adm ed hp
  have id : d+p=q := funext fun U=>sub_add_cancel ..
  rw [id] at sum
  rw [e_const V adm (-b)] at lo
  rw [e_const V adm b] at hi
  rw [sum,add_sub_cancel_right]
  exact abs_le.mpr ⟨lo,hi⟩
end YM.Integration.FVA1Physical.Wilson
