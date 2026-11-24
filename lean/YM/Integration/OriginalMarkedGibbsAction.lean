import YM.Integration.OriginalMarkedConditionalAction
import YM.Integration.SelectedCofactorLocalProjection

/-! The true finite exterior marginal of the complete measured Wilson density. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedGibbsAction
open Lattice RG Wilson MeasureTheory PhysicalNext PhysicalNext.Repeat.Legato
open OriginalMarkedRunAction OriginalMarkedRunCovariance OriginalMarkedRowCovariance
open SelectedCofactorChamberMarginal
open scoped Classical
variable {G : Gauge} {n : Side}

def exterior (S : Support n) : Set (Edge (Site n)) := {e | e.1 ∉ S}

def row (S : Support n) (P : Rep G n) (f : Config G n→ℂ) : Config G n→ℂ :=
  projected (exterior S) P.eval (fun U => P.eval U • f U)

private theorem weighted {P : Config G n→ℝ} {f : Config G n→ℂ}
    (hP : Envelope P) (hf : Envelope f) : Envelope (fun U => P U • f U) := by
  obtain ⟨c,hc⟩ := hP.cost
  obtain ⟨b,hb⟩ := hf.cost
  exact ⟨hP.meas.smul hf.meas,c*b,fun U => (norm_smul_le ..).trans
    (mul_le_mul (hc U) (hb U) (norm_nonneg _) ((norm_nonneg _).trans (hc U)))⟩

private theorem integrable_complex {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] {f : X → ℂ} (h : Envelope f) : Integrable f μ :=
  Integrable.of_bound h.meas.aestronglyMeasurable h.cost.choose (ae_of_all μ h.cost.choose_spec)

/-- Exact normalized integration first over the links based in S, then under
the true exterior marginal of the specified physical representative. -/
theorem disintegration (S : Support n) (P : Rep G n) (f : Config G n→ℂ)
    (hP : Envelope P.eval) (hf : Envelope f) {b : ℝ} (hb : 0<b) (floor : ∀ U,b≤P.eval U) :
    mean P (row S P f)=mean P f := by
  unfold mean
  apply congrArg ((mass P:ℂ)⁻¹ * ·)
  simpa only [row,Complex.real_smul] using
    pairing (exterior S) hP (weighted hP hf) hb floor

variable (R : Run G) {N p m d : ℕ} (hm : m<N)
local notation "Ω" => Config G (R.family.side m p)
local notation "dst" => R.family.path.rep N p m
local notation "kept" => approximation R (p:=p) hm d
local notation "omitted" => remainder R (p:=p) hm d
local notation "B" => R.alloy.B.a.budget m
local notation "ε" => (Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N p (m+1))^(d+1)

/-- Every finite field of the retained representative has positive density.
The finite-volume floor is used to justify the integral. -/
theorem retained_floor (A : Comparison R (p:=p) hm d) :
    ∃ b : ℝ, 0<b ∧ ∀ U,b≤(kept).eval U := by
  obtain ⟨a,ha,hp⟩ := SelectedCofactorLocalProjection.floor R.makes (p:=p) hm
  have E : Envelope (fun U : Ω => (omitted).additive B U) :=
    ⟨Activities.E_measurable A.posterior.cut.regular,(Activities.ESeries A.posterior.cut).bound⟩
  obtain ⟨c,hc⟩ := E.cost
  refine ⟨a*Real.exp (-c),mul_pos ha (Real.exp_pos _),fun U => ?_⟩
  have eh : -c≤(omitted).additive B U := (abs_le.mp (hc U)).1
  calc
    _ ≤ (dst).eval U * Real.exp ((omitted).additive B U) :=
      mul_le_mul (hp U) (Real.exp_le_exp.mpr eh) (Real.exp_pos _).le (ha.le.trans (hp U))
    _ = (kept).eval U := by
      rw [factor R hm A,OriginalMarkedRunCovariance.weight,mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one]

/-- Conditional reads of the true physical and the funded retained density at
one fixed exterior, using the native Haar coordinates on all remaining links. -/
theorem local_row (A : Comparison R (p:=p) hm d) (S : Support (R.family.side m p))
    (f : Ω→ℂ) (hf : Measurable f) (M : ℝ) (hM : 0≤M) (cap : ∀ U,‖f U‖≤M) (U : Ω) :
    let a := OriginalMarkedLocalPurchase.fee R.alloy.B.a m S ε
    ‖row S (dst) f U-row S (kept) f U‖ ≤ 2*Real.exp (2*a)*a*M := by
  let A₀ := exterior S
  let u := ((cut G A₀) U).1
  let ξ (y : Fields G A₀ᶜ) : Ω := (cut G A₀).symm (u,y)
  have mx : Measurable ξ := (cut G A₀).symm.measurable.comp (measurable_const.prodMk measurable_id)
  have fixed (y) : OriginalMarkedLocalDifference.Outside S (ξ y) U := by
    intro e he
    exact congrFun (congrArg Prod.fst ((cut G A₀).apply_symm_apply (u,y))) (⟨e,he⟩ : A₀)
  have eqRow (P : Rep G (R.family.side m p)) :
      row S P f U=read (sheet G A₀ᶜ) (fun y => P.eval (ξ y)) (fun y => f (ξ y)) := by
    simp only [row,projected,marginal,OriginalMarkedRowCovariance.read,A₀,u,ξ,Complex.real_smul,Complex.ofReal_inv]
  rw [eqRow,eqRow]
  exact OriginalMarkedConditionalAction.fiber R hm (sheet G A₀ᶜ) A S U ξ mx fixed f hf M hM cap

/-- Average the marked comparison over the *actual* full exterior density.
All coarse fields and all inherited hard activities contribute to this expectation. -/
theorem physical (A : Comparison R (p:=p) hm d) (S : Support (R.family.side m p))
    (f : Ω→ℂ) (hf : Measurable f) (M : ℝ) (hM : 0≤M) (cap : ∀ U,‖f U‖≤M) :
    let a := OriginalMarkedLocalPurchase.fee R.alloy.B.a m S ε
    ‖ActualRunCoarseReadout.expectation R N p m f-
      ActualRunCoarseReadout.expectation R N p m (row S (kept) f)‖ ≤ 2*Real.exp (2*a)*a*M := by
  let P := (dst)
  let Q := (kept)
  let c := row S P f
  let k := row S Q f
  have Penv : Envelope P.eval := P.envelope (R.makes.wilson.represents N p m hm.le).good
  have Qenv : Envelope Q.eval := keep_envelope R hm A
  have test : Envelope f := ⟨hf,M,cap⟩
  obtain ⟨b,hb,lb⟩ := SelectedCofactorLocalProjection.floor R.makes (p:=p) hm
  obtain ⟨e,he,lq⟩ := retained_floor R hm A
  have ce : Envelope c := projected_env (exterior S) Penv (weighted Penv test) hb lb
  have ke : Envelope k := projected_env (exterior S) Qenv (weighted Qenv test) he lq
  let μ := prior G (R.family.side m p)
  have ci : Integrable (fun U => (P.eval U : ℂ)*c U) μ := by
    simpa only [Complex.real_smul] using integrable_complex μ (weighted Penv ce)
  have ki : Integrable (fun U => (P.eval U : ℂ)*k U) μ := by
    simpa only [Complex.real_smul] using integrable_complex μ (weighted Penv ke)
  have linear : mean P c-mean P k=mean P (fun U => c U-k U) := by
    unfold mean
    rw [←mul_sub,←integral_sub ci ki]
    apply congrArg ((mass P:ℂ)⁻¹ * ·)
    exact integral_congr_ae (ae_of_all μ fun U => (mul_sub (P.eval U:ℂ) (c U) (k U)).symm)
  have ref := ActualCoveredNormalization.same_run_reference R N p m hm.le
  have hp : 0 < mass P := by
    unfold mass
    rw [ref.2.2]
    exact partition_pos _
  rw [actual_mean R hm f,actual_mean R hm (row S Q f),←disintegration S P f Penv test hb lb]
  change ‖mean P c-mean P k‖≤_
  rw [linear]
  exact bounded ref.2.1 (fun U => (ref.1 U).le) hp _ _
    (local_row R hm A S f hf M hM cap)

end YM.Integration.OriginalMarkedGibbsAction

