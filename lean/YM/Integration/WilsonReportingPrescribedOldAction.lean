import YM.Integration.WilsonReportingPrescribedOldSignedPanel
import YM.TraceExtension.Pith.Campus
import YM.UVNext.FREE_STRESS_CERTIFICATE.Low
import YangMills.WilsonProof.NativeSupport.YM.MS.Theater.Horizon

/-! The original reduced action polynomial fixes actual independent quadratic
source weights. At order zero the full calibrated column has exactly the same
connected reading as this signed combination of original Wilson cylinders. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldAction
open Function Finset Filter Lattice Wilson RG Source Labels MeasureTheory Maxwell StressFlux Gauge Trace Climb
open MS MS.Local.Physical MS.Theater MS.Land MS.Menus MS.Rake UVNext.FreeStress
open PhysicalNext.Repeat.Legato ActualOriginalDictionary
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) (B : Deck G)
private theorem allowed : (square4 G).val∈Film0 G 4 2 := by
  have pair_mem (a b : Axis) : (pair G a b a b).val∈Film0 G 4 2 :=
    (cinema _).mpr ⟨productPol_grade _ _,(pair G a b a b).property.2,
      congrArg Subtype.val (pair_real (G:=G) a b a b)⟩
  change ((1/4:ℝ) • ∑ a : Axis,∑ b : Axis,(pair G a b a b).val)∈Film0 G 4 2
  exact (Film0 G 4 2).smul_mem _ (Submodule.sum_mem _ fun a _=>
    Submodule.sum_mem _ fun b _=>pair_mem a b)


private def squareSection (G:Gauge) : IvSpace G 4 2 :=
  let p : Film0 G 4 2 := ⟨(square4 G).val,allowed⟩
  ⟨stageM G 4 2 p,⟨p,rfl⟩⟩

/-- These real coefficients are fixed by the original action, before a scale,
perturbation order, or arbitrary prescription is chosen. -/
def weights (i : B.BIndex (4:ℤ) 2) : ℝ := (Indigo B 4 2).repr (squareSection G) i

theorem reduced : reduceEq (square4 G).val=
    ∑i : B.BIndex (4:ℤ) 2,weights B i • reduceEq (film B i (h:=4)) := by
  have law := congrArg Subtype.val ((Indigo B 4 2).sum_repr (squareSection G))
  have atoms (i:B.BIndex (4:ℤ) 2) : (Indigo B 4 2 i).val=reduceEq (film B i (h:=4)) :=
    (letS B (⟨4,by decide⟩:Fin 5) (⟨2,by decide⟩:Fin 5) i).symm
  simp only [Submodule.coe_sum,SetLike.val_smul,atoms] at law
  exact law.symm

private theorem mono_degree {j:ℕ} (p : Place j) (a : G.ColorIndex) :
    MvPolynomial.IsWeightedHomogeneous Labels.bidegree (mono p a) (j+2,1) :=
  MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun (t : Fin (Labels.dim G j)) _ =>
    (MvPolynomial.isWeightedHomogeneous_X ℂ Labels.bidegree (⟨j,t⟩ : Key G)).C_mul _)

private theorem tape_degree {j l:ℕ} (p : Place j) (q : Place l) :
    MvPolynomial.IsWeightedHomogeneous Labels.bidegree (tape (G := G) p q) ((j+2,1)+(l+2,1) : ℕ × ℕ) :=
  MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun a _ => (mono_degree p a).mul (mono_degree q a))

private theorem one_zero (hG : G.Simple) {d : ℕ} (hd : d≤4) (i : B.BIndex (d:ℤ) 1) : False := by
  let z := filmLabel B d 1 i
  let p : Labels.Label G 4 := Labels.raiseLabel G hd z
  have hp : p ∈ Labels.Grade (d,1) := (filmW (h:=d) B i).2
  obtain ⟨c,v,hh⟩ := span_four hG p
  have hb (a b : Place 0) :
      Labels.gradePart (d,1) (bond (G:=G) a b (d:=4) le_rfl)=0 :=
    Labels.gradePart_zero _ (d,1) (4,2) (by simp)
      (tape_degree a b)
  have hu : Labels.gradePart (d,1) (Labels.unit G 4)=0 :=
    Labels.gradePart_zero _ _ (0,0) (by simp) (Labels.unit_grade (G:=G) 4)
  have hz := congrArg (Labels.gradePart (G:=G) (d:=4) (d,1)) hh
  simp only [Labels.gradePart_self p _ hp,map_add,map_sum,map_smul,hu,hb,smul_zero,
    Finset.sum_const_zero,zero_add] at hz
  have he : p.val=0 := congrArg (fun v:Labels.Label G 4=>v.val) hz
  have hf : film B i (h:=d)=0 := he
  have hbasis : B.raw (d:ℤ) 1 i=0 := by rw [←lamp_here (h:=d) B i,hf,map_zero]
  exact (Module.finBasis ℝ (B.carries (d:ℤ) 1)).ne_zero i (Subtype.ext hbasis)

theorem flat (d : ℕ) (i : B.BIndex (d:ℤ) 0) (n : Side) (o : Site n)
    (U V : Config G n) :
    ((dictionary R B).cylinder d 0 i).O n o U=((dictionary R B).cylinder d 0 i).O n o V := by
  rw [cylinder_observable,cylinder_observable]
  apply sum_congr rfl
  intro j _
  by_cases hj : j=0
  · subst j
    have read (A : Config G n) : ((ActualFiniteStencil.retained R d 0).O n o A : ℂ)=1 := by
      rw [ActualFiniteStencil.retained_observable,SectionData.places,
        show (Pi.single 0 1 : (R.family.labels.level d).Coeff)=(R.family.labels.level d).e0 from rfl]
      exact congrFun (R.makes.sections d).unit (expandAt o A)
    exact congrArg (fun t:ℝ=>ActualOriginalDictionary.weight R B d 0 i 0*t) (Complex.ofReal_injective ((read U).trans (read V).symm))
  · have hp := (R.family.labels.level d).factors_pos j hj
    have hz := off_grade R B d 0 i j (fun h=>hp.ne' (congrArg Prod.snd h))
    have hw : ActualOriginalDictionary.weight R B d 0 i j=0 := by rw [ActualOriginalDictionary.weight,hz]; rfl
    simp [hw]

private theorem lower_constant (hG:G.Simple) {d q:ℕ} (hd:d≤4) (lo:q<2) (b:B.BIndex (d:ℤ) q)
    (n:Side) (o:Site n) (U V:Config G n) :
    ((dictionary R B).cylinder d q b).O n o U=((dictionary R B).cylinder d q b).O n o V := by
  cases q with
  | zero => exact flat R B d b n o U V
  | succ q =>
    cases q with
    | zero => exact (one_zero B hG hd b).elim
    | succ q => omega

abbrev label (i : B.BIndex (4:ℤ) 2) : MS.Rake.Label B := ⟨4,⟨⟨2,by decide⟩,i⟩⟩

variable (Q : MS.Land.Prescription B) (i : B.BIndex (4:ℤ) 2) (μ : ℝ)

theorem upper (j : Glyph B 4) (hj : 2≤j.grade) :
    oil (Q.fees 4 (label B i).item) j 0 μ = if j=MS.Land.read (label B i).item then 1 else 0 := by
  rw [oil,(Q.init 4 (label B i).item).Single j hj]
  split_ifs <;> simp_all

def observed (n : Side) (o : Site n) (A : Config G n) :=
  ActualOriginalCalibratedColumns.weightedObservable R B Q (label B i) μ n o A 0

private theorem expansion (n : Side) (o : Site n) (U : Config G n) :
    observed R B Q i μ n o U = ∑ j : Glyph B 4,oil (Q.fees 4 (label B i).item) j 0 μ *
      (((dictionary R B).cylinder j.size j.grade j.2.2).O n o U : ℂ) := by
  unfold observed ActualOriginalCalibratedColumns.weightedObservable WilsonComparison.Finite.Dictionary.calibrated
  rw [List.map_map,←Multiset.sum_coe,←Multiset.map_coe,Finset.coe_toList,←Finset.sum]
  rfl

theorem measured (hG : G.Simple) (n : Side) (o : Site n) (U V : Config G n) :
    observed R B Q i μ n o U - observed R B Q i μ n o V =
      ((((dictionary R B).cylinder 4 2 i).O n o U -
        ((dictionary R B).cylinder 4 2 i).O n o V : ℝ) : ℂ) := by
  rw [expansion,expansion,←sum_sub_distrib]
  let j₀ := MS.Land.read (label B i).item
  rw [sum_eq_single_of_mem j₀ (mem_univ _) ?_]
  · rw [upper B Q i μ j₀ (show 2≤2 from le_refl 2),if_pos rfl,one_mul,one_mul,Complex.ofReal_sub]
    rfl
  · intro j _ hj
    by_cases high : 2≤j.grade
    · have hz := upper B Q i μ j high
      rw [if_neg hj] at hz
      rw [hz]
      simp
    · have equal := lower_constant R B hG (Nat.le_of_lt_succ j.1.isLt) (lt_of_not_ge high) j.2.2 n o U V
      rw [equal]
      exact sub_self _

/-- All original lower fees and all engineering sizes of the prescribed multiplet. -/
def column (k : ℕ) (n:Side) (o:Site n) (U:Config G n) : ℂ :=
  ∑ b : B.BIndex (4:ℤ) 2,(weights B b:ℂ)*
    ActualOriginalCalibratedColumns.weightedObservable R B Q (label B b) μ n o U k

/-- The genuinely chosen quadratic stencil, at the same site and same gauge. -/
def stencil (n:Side) (o:Site n) (U:Config G n) : ℂ :=
  ∑ b : B.BIndex (4:ℤ) 2,(weights B b:ℂ)*(((dictionary R B).cylinder 4 2 b).O n o U:ℂ)

theorem original (hG:G.Simple) (n:Side) (o:Site n) (U V:Config G n) :
    column R B Q μ 0 n o U-column R B Q μ 0 n o V=stencil R B n o U-stencil R B n o V := by
  unfold column stencil
  rw [←sum_sub_distrib,←sum_sub_distrib]
  apply sum_congr rfl
  intro b _
  rw [←mul_sub,←mul_sub]
  exact congrArg (fun t=>(weights B b:ℂ)*t) ((measured R B Q b μ hG n o U V).trans (Complex.ofReal_sub ..))

end YM.Integration.WilsonReportingPrescribedOldAction
