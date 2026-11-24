import YM.Integration.WilsonReportingPrescribedOldCoordinates
import YM.Integration.WilsonMacroscopicRichFlatPosteriorLaw

/-! The entire marked section discrepancy is contracted with the Gram of
the original simultaneous Wilson conditional, including the signed cross terms. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldGram
open Function Set MeasureTheory Lattice Wilson RG Tree Precision Source Labels
open PhysicalNext.Repeat.Legato RGComparison.Core16 RG17 Extraction Table Spec MS MS.Menus MS.Local.Physical
open WilsonReportingPrescribedOldCoordinates
open scoped Classical BigOperators ComplexConjugate

variable {G : Gauge} (R : Run G) {h N per : ℕ} (o : Site (R.family.side N per))

abbrev Axis (h : ℕ) := (a : Fin (h+1)) × (R.family.labels.level a.val).Index

def atom (e : Axis R h) (U : Config G (R.family.side N per)) : ℂ :=
  slot R o U e.1.val (Pi.single e.2 1)

theorem stencil (v : Panel R h) (U : Config G (R.family.side N per)) :
    read R o U v=∑e : Axis R h,v e.1 e.2 * atom R o e U := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  have total : v a=∑b,v a b • Pi.single b (1:ℂ) := by
    ext i
    simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
  change (slot R o U a.val) (v a)=_
  conv_lhs => rw [total,map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [map_smul]
  rfl

private theorem atom_cont (e : Axis R h) : Continuous (atom R o e) :=
  (R.family.localSection e.1.val).continuous_places _ o

private theorem read_cont (v : Panel R h) : Continuous (fun U=>read R o U v) :=
  continuous_finsetSum _ fun a _=>(R.family.localSection a.val).continuous_places (v a) o

variable {j:ℕ} (jn:j+1≤N) (V:Config G (R.family.side j per))
local notation "K" => WilsonMacroscopicRichFlatPosteriorLaw.law R N per jn V

/-- Uncentered Hermitian matrix on the actual held Wilson fibre at V. -/
def matrix (a b : Axis R h) : ℂ := ∫U,atom R o a U * conj (atom R o b U) ∂K

def contracted (v w : Panel R h) : ℂ :=
  ∑a : Axis R h,∑b : Axis R h,(v a.1 a.2 * conj (w b.1 b.2)) * matrix R o jn V a b

private theorem finite {α:Type} [Fintype α] (f:α → Config G (R.family.side N per)→ℂ)
    (z:α→ℂ) (good:∀a,Continuous (f a)) :
    (∫U,∑a,z a*f a U ∂K)=∑a,z a*(∫U,f a U ∂K) := by
  letI := WilsonMacroscopicRichFlatPosteriorLaw.prob R jn (le_refl N) V
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · intro a _
    exact (continuous_const.mul (good a)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem pairing (v w : Panel R h) : (∫U,read R o U v*conj (read R o U w) ∂K)=
    contracted R o jn V v w := by
  let I := Axis R h
  let z := fun b : I×I=>v b.1.1 b.1.2 * conj (w b.2.1 b.2.2)
  let f := fun (b : I×I) (U:Config G (R.family.side N per))=>atom R o b.1 U * conj (atom R o b.2 U)
  calc
    _ = ∫U,∑b : I×I,z b*f b U ∂K := by
      apply integral_congr_ae
      filter_upwards [] with U
      rw [stencil R o v U,stencil R o w U,map_sum,Fintype.sum_prod_type,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [map_mul]
      dsimp [z,f]
      ring
    _ = ∑b : I×I,z b*∫U,f b U ∂K := finite R jn V f z fun b=>
      (atom_cont R o b.1).mul (Complex.continuous_conj.comp (atom_cont R o b.2))
    _ = _ := by rw [Fintype.sum_prod_type]; rfl

/-- Original conditional mean-square, with the two cross contractions retained. -/
theorem squared (v : Panel R h) :
    (↑(∫U,‖read R o U v‖^2 ∂K):ℂ)=contracted R o jn V v v := by
  rw [←pairing R o jn V,←integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [] with U
  rw [Complex.mul_conj']
  push_cast
  rfl

private theorem read_sub (v w:Panel R h) (U:Config G (R.family.side N per)) :
    read R o U (v-w)=read R o U v-read R o U w := by
  unfold WilsonReportingPrescribedOldCoordinates.read
  rw [←Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _=>map_sub (slot R o U a.val) _ _

theorem cross (v w : Panel R h) :
    contracted R o jn V (v-w) (v-w)=
        contracted R o jn V v v-contracted R o jn V v w-contracted R o jn V w v+
        contracted R o jn V w w := by
  unfold contracted
  simp only [Pi.sub_apply,map_sub,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

variable {B:Deck G} (Q:MS.Land.Prescription B) (u:MS.Rake.Label B)
  {f:Extraction.Order} {S:Table R.family.book} {F:Spec.Final R.family f S} (L:Layout F)

/-- The financial target uses the original reported column and the original
prescribed source, on every retained size of both. -/
theorem original (r μ:ℝ) (k:ℕ) (w:Panel R u.h) (α:Fin (u.h+1)→ℂ) :
    let report := reported R L r N per w α
    let source := prescribed R Q u μ k
    (↑(∫U,‖(∑a,α a*R.family.O N per (atRef L a.val r (N,per) (w a)) o U)-
      ActualOriginalCalibratedColumns.weightedObservable R B Q u μ (R.family.side N per) o U k‖^2 ∂K):ℂ)=
      contracted R o jn V report report-contracted R o jn V report source-
        contracted R o jn V source report+contracted R o jn V source source := by
  dsimp only
  simp_rw [WilsonReportingPrescribedOldCoordinates.original R Q u L o]
  rw [squared R o jn V,cross R o jn V]

end YM.Integration.WilsonReportingPrescribedOldGram
