import YM.Integration.WilsonPositionOriginalDiagnosticRightPrimitive

/-! The two prescribed clocks read the actual calibrated incoming Q sources
in one finite signed Wilson test, with its original subcell quadrature. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDiagnosticRightReading
open Finset Filter MeasureTheory Lattice Wilson RG PhysicalNext.Repeat.Legato MS MS.Land MS.Menus MS.Local.Physical
open WilsonMatrixOriginalDeckRawMoment WilsonMatrixOriginalDeckPrescriptionFields
open WilsonPositionOriginalDiagnosticRightSeries WilsonPositionOriginalDiagnosticRightAssay
open WilsonPositionProgramReporterBand Spec Table Extraction Extraction.Order Push.GridApprox Next.UVStress OPE.Therm
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {B:Deck G}(Q:MS.Land.Prescription B)(h:ℕ)
local notation "I"=>Glyph B h

def submitted (μ:ℝ)(p:ℕ)(x:ℂ)(N per:ℕ)(a:I):SiteField R N per:=fun o U=>
  ∑k∈range (p+1),x^k*ActualOriginalCalibratedColumns.weightedObservable R B Q
    (WilsonMatrixOriginalDeckRawPanel.name h a) μ (R.family.side N per) o U k

theorem fields (μ:ℝ)(p:ℕ)(x:ℂ)(N per:ℕ)(a:I) :
    submitted R Q h μ p x N per a=posted R Q h μ p x N per a:=by
  funext o U
  have priced(k:ℕ):ActualOriginalCalibratedColumns.weightedObservable R B Q
      (WilsonMatrixOriginalDeckRawPanel.name h a) μ (R.family.side N per) o U k =
      ∑b:I,WilsonMatrixOriginalDeckPrescription.fees Q h μ k b a*raw R h N per o U b :=
    (WilsonMacroscopicRichOriginalPortfolio.observed R Q _ _ _ _ _ _ _).trans
      (WilsonMatrixOriginalDeckPrescriptionFields.observed R Q h μ k N per o U a)
  simp only [submitted,posted,sources,trunc,Polynomial.eval_finsetSum,Polynomial.eval_monomial,priced,mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl;intro b _
  apply sum_congr rfl;intro k _
  ring

def remainder (μ ν:ℝ)(p:ℕ)(g:ℂ)(N per:ℕ)(a:I):SiteField R N per:=fun o U=>
   (∑b:I,submitted R Q h μ p g N per b o U*(change Q h μ ν p b a).eval g)
     - submitted R Q h ν p g N per a o U

/-- The original signed discretized test hears the error against every bounded
left field on this same Wilson density. The estimate includes the complete
two physical group insertions. -/
theorem original {D:XSpace.Run}{stage:ℕ}(T:Band R D stage)(simple:G.Simple){A:ℝ}(pos:0≤A):
    ∃C:ℝ,0≤C ∧ ∀p:ℕ,∀ᶠt:ℕ in atTop,∀N per,T.reporter+t≤N→
      ∀θ ψ:ℝ,‖θ‖+‖ψ‖≤A→∀a:I,∀φ:Test 2,∀X:SiteField R N per,∀b:ℝ,
      0≤b→(∀o U,‖X o U‖≤b)→
      let τ:=R.family.S.scale (T.reporter+t+T.upper t)-R.family.S.scale (T.reporter+t)
      let y:=Pert.Asymptotics.regulatorRun R.family N per (T.reporter+t)
      ‖joint R φ N per (scene R.family.path N per N) X
        (remainder R Q h (θ-τ) (ψ-τ) (p+2) (y:ℂ) N per a)‖ ≤
        (∑x:Var R.family.S 2 N per,‖WilsonExternalMeshMass.charge R.family φ x‖)*b*C*y^(p+1):=by
  obtain ⟨C,cpos,paid⟩:=WilsonPositionOriginalDiagnosticRightPrimitive.original R Q h T simple A pos
  refine ⟨C,cpos,?_⟩
  intro p
  filter_upwards [paid p] with t priced
  intro N per alive θ ψ room a φ X b bp bound τ y
  let ρ:=scene R.family.path N per N
  letI:IsProbabilityMeasure ρ:=probability R.makes.wilson le_rfl
  let W:=remainder R Q h (θ-τ) (ψ-τ) (p+2) (y:ℂ) N per a
  have fair(o U):‖W o U‖≤C*y^(p+1):=by
    dsimp only [W,remainder]
    simp_rw [fields]
    exact priced N per alive θ ψ room a o U
  have heard(x:Var R.family.S 2 N per): ‖∫U, X (x 0) U*W (x 1) U ∂ρ‖≤ b*(C*y^(p+1)):=by
    have every(U:Config G (R.family.side N per)): ‖X (x 0) U * W (x 1) U‖≤b*(C*y^(p+1)):=by
      rw [norm_mul]
      exact mul_le_mul (bound (x 0) U) (fair (x 1) U) (norm_nonneg _) bp
    simpa using norm_integral_le_of_norm_le_const (μ:=ρ) (ae_of_all _ every)
  unfold joint
  apply (norm_sum_le _ _).trans
  rw [show (∑x:Var R.family.S 2 N per,‖WilsonExternalMeshMass.charge R.family φ x‖)*b*C*y^(p+1)=
      ∑x:Var R.family.S 2 N per,‖WilsonExternalMeshMass.charge R.family φ x‖*(b*(C*y^(p+1))) by rw [←sum_mul];ring]
  apply sum_le_sum;intro x _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (heard x) (norm_nonneg _)

end YM.Integration.WilsonPositionOriginalDiagnosticRightReading
