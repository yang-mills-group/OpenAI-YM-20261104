import YM.Integration.WilsonOrdinaryUltravioletGram

/-! The actual measured reflected Gram on the already extracted field theory
decodes an arbitrary finite set of mixed *numerical* readings on its own
original homogeneous probes. This recovery precedes a choice of new frame. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryPositionDecoder
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table Spec
open Next.Rank Next.UVStress OPE OPE.Orbits OPE.Strobe RG12 RG17 RG17.Panoramic SharpGram Climb PhysMS
open OPE.Levy Push.FiniteDetection.Free Trace.Pilot
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonReportRegularMoments WilsonReportReflectedGram WilsonReportEarlySmearing WilsonReportColumnCut
open WilsonOrdinaryMixedGram WilsonOrdinaryNormalizedStep WilsonOrdinaryFourGram
open WilsonOrdinaryHomogeneousDetectors WilsonOrdinaryMeasuredMarch
open Cells Push.GridApprox
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}

open WilsonOrdinaryHomogeneousDetectors

private def forget {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (E→L[ℝ]ℝ) →ₗ[ℝ] Module.Dual ℝ E where
  toFun p := p.toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem invert {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T : RealForm E E) {δ : ℝ} (positive : 0<δ) (funded : coercive T δ) :
    ∃ D : (E→L[ℝ]ℝ)→ₗ[ℝ]E,
      (∀ p y,T (D p) y=p y) ∧ (∀ p,δ*‖D p‖≤‖p‖) ∧
      (∀ p x,(∀ y,T x y=p y) → x=D p) := by
  let A := (forget (E:=E)).comp T.toLinearMap
  have inj : Function.Injective A := by
    intro x y equal
    have zero : T (x-y) (x-y)=0 := by
      have vanishes : A (x-y)=0 := by rw [map_sub,equal,sub_self]
      exact DFunLike.congr_fun vanishes (x-y)
    by_contra h
    have nonzero : 0<δ*‖x-y‖^2 := mul_pos positive (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h)))
    linarith only [funded (x-y),zero,nonzero]
  have sur : Function.Surjective A := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by change Module.finrank ℝ E=Module.finrank ℝ (Module.Dual ℝ E); rw [Subspace.dual_finrank_eq])).1 inj
  let B := LinearEquiv.ofBijective A ⟨inj,sur⟩
  let D := B.symm.toLinearMap.comp forget
  have same (p : E→L[ℝ]ℝ) : A (D p)=p.toLinearMap := B.apply_symm_apply _
  refine ⟨D,fun p y=>DFunLike.congr_fun (same p) y,?_,?_⟩
  · intro p
    have live := funded (D p)
    have apply := DFunLike.congr_fun (same p) (D p)
    change T (D p) (D p)=p (D p) at apply
    have bound : p (D p)≤‖p‖*‖D p‖ :=
      (le_abs_self _).trans (p.le_opNorm _)
    by_cases hz : ‖D p‖=0
    · rw [hz,mul_zero]; exact norm_nonneg _
    · have nonzero := (norm_nonneg _).lt_of_ne (Ne.symm hz)
      have paid : (δ*‖D p‖)*‖D p‖≤‖p‖*‖D p‖ := by
        rw [mul_assoc,←sq]; exact live.trans (apply.le.trans bound)
      exact (le_of_mul_le_mul_right paid nonzero)
  · intro p x read
    apply inj
    rw [same]
    ext y
    exact read y

variable (F : Final R.family f S) (d : ℕ)
local notation "E₀" => RG17.Free R.family d

def record (k : Handle F d→ℝ) : E₀→L[ℝ]ℝ :=
  ∑ i,k i • LinearMap.toContinuousLinearMap ((WilsonOrdinaryHomogeneousDetectors.basis F d).coord i)

theorem entry (k : Handle F d→ℝ) (i : Handle F d) : record F d k (WilsonOrdinaryHomogeneousDetectors.basis F d i)=k i := by
  classical
  simp [record,_root_.sum_apply,Module.Basis.coord_apply,Finsupp.single_apply,mul_ite]

/-- The immutable detector roster makes the reconstruction linear in all
independently named measured scores. -/
def recordLinear : (Handle F d→ℝ)→ₗ[ℝ](E₀→L[ℝ]ℝ) where
  toFun := record F d
  map_add' k l := by simp only [record,Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' a k := by
    change (∑i,(a*k i) • LinearMap.toContinuousLinearMap ((WilsonOrdinaryHomogeneousDetectors.basis F d).coord i)) =
      a • ∑i,k i • LinearMap.toContinuousLinearMap ((WilsonOrdinaryHomogeneousDetectors.basis F d).coord i)
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _=>mul_smul _ _ _

/-- This fixed fee precedes the choice of every input and physical radius. -/
def tariff : ℝ := ∑ i : Handle F d,‖LinearMap.toContinuousLinearMap ((WilsonOrdinaryHomogeneousDetectors.basis F d).coord i)‖

private theorem cash {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (c : ι→V) (k : ι→ℝ) (M : ℝ) (funded : ∀ i,|k i|≤M) :
    ‖∑ i,k i • c i‖ ≤ M*∑ i,‖c i‖ := by
  calc
    _ ≤ ∑ i,‖k i • c i‖ := norm_sum_le _ _
    _ ≤ ∑ i,M*‖c i‖ := Finset.sum_le_sum fun i _=>by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (funded i) (norm_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem numerical (k : Handle F d→ℝ) (M : ℝ) (funded : ∀ i,|k i|≤M) :
    ‖record F d k‖ ≤ M*tariff F d :=
  cash (fun i=>LinearMap.toContinuousLinearMap ((WilsonOrdinaryHomogeneousDetectors.basis F d).coord i)) k M funded

/-- A single original lower Gram margin and decoder, bought before any
newly named source or its mixed numeric rows. Every such true/proposed
reading gives one actual field, reads back exactly, and the measured
relative norm obeys the genuine reciprocal-margin estimate. -/
theorem original (J : ℝ→tower S) (P : Pier.Lair.Present F J) :
    ∃ δ : ℝ,0<δ ∧ ∀ᶠ r in trail,
      ∃ D : (E₀→L[ℝ]ℝ)→ₗ[ℝ] S.Field d,
        (∀ p y,mixed F J d r r ((J r d).symm (D p)) y = p y) ∧
        (∀ p,δ*‖(J r d).symm (D p)‖≤‖p‖) ∧
        (∀ p x,(∀ y,mixed F J d r r ((J r d).symm x) y=p y) → x=D p) := by
  let δ := Lenses.margin R.family d/2
  have positive : 0<δ := half_pos (Weak.Portfolio.freely (C:=R.family) d).choose_spec.1
  refine ⟨δ,positive,?_⟩
  filter_upwards [Pier.Lair.heights F P d] with r paid
  obtain ⟨D,read,price,unique⟩ := invert (mixed F J d r r) positive paid.1
  let U := ((J r d).toLinearMap.restrictScalars ℝ).comp D
  refine ⟨U,?_,?_,?_⟩
  · intro p y; exact (J r d).symm_apply_apply (D p) ▸ read p y
  · intro p; exact (J r d).symm_apply_apply (D p) ▸ price p
  · intro p x hx
    change x=J r d (D p)
    exact (J r d).apply_symm_apply x ▸ congrArg (J r d) (unique p ((J r d).symm x) hx)

/-- No fitting or linearity is assumed on the finite incoming numerical
scores: the original actual $F$ alone realizes every such entire row by a
unique physical field, using one decoder and one margin for all of them. -/
theorem finite_rows (J : ℝ→tower S) (P : Pier.Lair.Present F J) :
    ∃ δ : ℝ,0<δ ∧ ∀ᶠ r in trail,
      ∃ X : (Handle F d→ℝ)→ₗ[ℝ]S.Field d,
        (∀ k i,mixed F J d r r ((J r d).symm (X k)) (WilsonOrdinaryHomogeneousDetectors.basis F d i)=k i) ∧
        (∀ k,δ*‖(J r d).symm (X k)‖≤‖record F d k‖) ∧
        (∀ k x,(∀ i,mixed F J d r r ((J r d).symm x) (WilsonOrdinaryHomogeneousDetectors.basis F d i)=k i) → x=X k) := by
  obtain ⟨δ,hd,ready⟩ := original F d J P
  refine ⟨δ,hd,?_⟩
  filter_upwards [ready] with r quoted
  obtain ⟨D,read,bill,unique⟩ := quoted
  refine ⟨D.comp (recordLinear F d),fun k i=>(read _ _).trans (entry F d k i),fun k=>bill _,?_⟩
  intro k x measured
  apply unique
  have same : (mixed F J d r r ((J r d).symm x)).toLinearMap = (record F d k).toLinearMap := by
    apply (WilsonOrdinaryHomogeneousDetectors.basis F d).ext
    intro i
    exact (measured i).trans (entry F d k i).symm
  exact fun y=>DFunLike.congr_fun same y

end YM.Integration.WilsonOrdinaryPositionDecoder
