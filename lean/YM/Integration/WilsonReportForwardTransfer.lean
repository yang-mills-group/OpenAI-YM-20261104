import YM.Integration.WilsonReportExteriorTail

/-! The exact separately scheduled fine spectator in the full nonlinear Wilson block law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportForwardTransfer
open Function Filter Finset Set MeasureTheory Lattice Wilson RG OPE OPE.Therm Push.GridApprox
open scoped ENNReal BigOperators Classical
variable {G : Gauge} {C : Family G} {N p k i : ℕ}

/-- The top scene of this actual history is its very same normalized Wilson law. -/
theorem top (hC : C.Makes) (N p : ℕ) :
    scene C.path N p N = law G (C.side N p) (C.beta N p) := by
  unfold scene law dose weight
  rw [(hC.wilson.starts N p).2]

private theorem one {c f : Side} {S : StepData c f} {b : ℝ} (K : S.IsKernel b G)
    (g : Config G f→ℂ) (ig : Integrable g (prior G f)) :
    (∫ V, ‖S.push b g V‖ ∂prior G c) ≤ ∫ U, ‖g U‖ ∂prior G f := by
  have each (V : Config G c) : ‖S.push b g V‖≤S.push b (fun U => ‖g U‖) V := by
    change ‖∫ U,S.density b U V • g U ∂prior G f‖ ≤ ∫ U,S.density b U V • ‖g U‖ ∂prior G f
    refine (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae (Eventually.of_forall fun U => ?_))
    dsimp only
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (K.positive U V),smul_eq_mul]
  exact (integral_mono (S.push_integrable K g ig).norm (S.push_integrable K _ ig.norm) each).trans_eq
    (S.push_integral K _ ig.norm)

private theorem many (ki : k ≤ i) (g : Config G (C.side i p)→ℂ) (ig : Integrable g (prior G (C.side i p))) :
    (∫ V,‖pushTo C.path N p ki g V‖ ∂prior G (C.side k p)) ≤ ∫ U,‖g U‖ ∂prior G (C.side i p) := by
  induction i,ki using Nat.le_induction with
  | base => simp
  | succ i ki ih =>
    let K := C.path.levels.transition_mass i p (C.path.β N p (i+1))
    rw [pushTo_next]
    exact (ih _ (StepData.push_integrable K g ig)).trans (one K g ig)

/-- The true signed fine density, in the fixed original Haar coordinates. -/
def weighted (X : Config G (C.side i p)→ℂ) (U : Config G (C.side i p)) : ℂ :=
  (dose (H:=C.path) (p:=p) i U N : ℂ)*X U

private theorem admissible (hC : C.Makes) (hi : i ≤ N) (X : Config G (C.side i p)→ℂ) :
    Integrable X (scene C.path N p i) ↔ Integrable (weighted (N:=N) X) (prior G (C.side i p)) := by
  unfold scene weighted
  rw [integrable_withDensity_iff_integrable_smul' (dose_env hC.wilson hi).meas.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (dose_positive hC.wilson hi _).le,Complex.real_smul]

private theorem norm_mass (hC : C.Makes) (hi : i ≤ N) (X : Config G (C.side i p)→ℂ) :
    (∫ U, ‖weighted (N:=N) X U‖ ∂prior G (C.side i p))=∫ U, ‖X U‖ ∂scene C.path N p i := by
  rw [account hC.wilson hi]
  apply integral_congr_ae
  filter_upwards with U
  rw [weighted,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (dose_positive hC.wilson hi U).le,smul_eq_mul]

/-- The separately filed fine insertion is propagated as ONE signed numerator
through all intermediate nonlinear kernels. It is normalized only against this
physical run's actual coarse vacuum. -/
def exterior (ki : k ≤ i) (X : Config G (C.side i p)→ℂ) (U : Config G (C.side k p)) : ℂ :=
  pushTo C.path N p ki (weighted (N:=N) X) U / (dose (H:=C.path) (p:=p) k U N : ℂ)

private theorem cancel (hC : C.Makes) (ki : k ≤ i) (hi : i ≤ N) (X : Config G (C.side i p)→ℂ) :
    weighted (N:=N) (exterior (N:=N) ki X)=pushTo C.path N p ki (weighted (N:=N) X) := by
  funext U
  have nz : (dose (H:=C.path) (p:=p) k U N : ℂ)≠0 := by exact_mod_cast (dose_positive hC.wilson (ki.trans hi) U).ne'
  change _*(_/_) = _
  field_simp

/-- The total variation of the transported actual, possibly signed or complex,
microscopic insertion only decreases under the original finite Wilson kernels. -/
theorem contract (hC : C.Makes) (ki : k ≤ i) (hi : i ≤ N) (X : Config G (C.side i p)→ℂ)
    (iX : Integrable X (scene C.path N p i)) :
    Integrable (exterior (N:=N) ki X) (scene C.path N p k) ∧
    (∫ U, ‖exterior (N:=N) ki X U‖ ∂scene C.path N p k)≤∫ U,‖X U‖ ∂scene C.path N p i := by
  have fine := (admissible hC hi X).mp iX
  constructor
  · apply (admissible hC (ki.trans hi) _).mpr
    rw [cancel hC ki hi]
    exact pushTo_integrable C.path N p ki _ fine
  · rw [←norm_mass hC (ki.trans hi),cancel hC ki hi,←norm_mass hC hi]
    exact many ki _ fine

/-- Exact adjoint identity on the same physical finite joint law. The common
coarse function is evaluated on ONE sampled gauge field for all its markers. -/
theorem joint (hC : C.Makes) (ki : k ≤ i) (hi : i ≤ N) (X : Config G (C.side i p)→ℂ)
    (iX : Integrable X (scene C.path N p i)) (F : Config G (C.side k p)→ℂ) (hF : Envelope F) :
    (∫ U, exterior (N:=N) ki X U*F U ∂scene C.path N p k) =
      ∫ Z,X Z*backTo C.path N p ki F Z ∂scene C.path N p i := by
  rw [account hC.wilson (ki.trans hi),account hC.wilson hi]
  simp only [Complex.real_smul,←mul_assoc]
  change (∫ U, weighted (N:=N) (exterior (N:=N) ki X) U*F U ∂_) =
      ∫ Z,weighted (N:=N) X Z*backTo C.path N p ki F Z ∂_
  rw [cancel hC ki hi]
  exact pushTo_dual C.path N p ki hF _ ((admissible hC hi X).mp iX)

end YM.Integration.WilsonReportForwardTransfer
end

