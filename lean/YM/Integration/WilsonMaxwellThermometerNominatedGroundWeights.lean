import YM.Integration.WilsonMaxwellThermometerNominatedEnvelope
import YM.Integration.WilsonMaxwellThermometerNominatedGroundPurse
import YM.Integration.WilsonSeparatedOriginalThermometerCells

/-! The signed continuum centering weights are counted exactly inside each
microscopic cell. One real smooth envelope covers every term, including cells
where the original signed test has zero integral. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerNominatedGroundWeights
open Set Finset Function Filter MeasureTheory Lattice Wilson Labels RG Source PhysicalNext.Repeat.Legato RG17
open OPE Table Spec PhysMS PhysMS.Frame Maxwell Maxwell.Free XSpace XSpace.Rose
open Marker QuadraticLocal Primitives.GCC.Anchor WilsonThermometerCenteredAlgebra
open WilsonMaxwellThermometerNominatedGroundPurse WilsonMaxwellThermometerNominatedDelta
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G)
local notation "J₀" => Stock.census (Fin 3)

theorem regular (s:(J₀).Mode):ContinuousOn (fun x=>weight (policy R x) s) (conf 3):=by
  have h:ContinuousOn (policy R) (conf 3):=by
    apply continuousOn_pi.mpr
    intro t
    by_cases non:t=(J₀).quiet
    · change ContinuousOn (fun x=>if t=(J₀).quiet then (1:ℂ) else _) _
      simpa only [if_pos non] using (continuousOn_const (c:=(1:ℂ)) : ContinuousOn _ (conf 3))
    · change ContinuousOn (fun x=>if t=(J₀).quiet then (1:ℂ) else WilsonMaxwellThermometerNominatedProperFaces.ground R x t.val) _
      simp only [if_neg non]
      exact fun x hx=>(WickGoal_tied (C:=R.family) (WilsonPositionThermometerGradedSource.source R.family t.val) hx).continuousAt.continuousWithinAt
  have c:ContinuousOn (fun x=>1-policy R x) (conf 3):=continuousOn_const.sub h
  have ih:ContinuousOn (fun x=>1+(1-policy R x)+(1-policy R x)^2+(1-policy R x)^3) (conf 3):=
    ((continuousOn_const.add c).add (c.pow 2)).add (c.pow 3)
  have same:ContinuousOn (fun x=>inverseMass (policy R x)) (conf 3):=
    ih.congr (fun x _=>inverse _ (unit _))
  exact (Poly.part_cont (complement s)).comp_continuousOn same

def payment (φ:Test 3) {T:Type} (χ:Points 3→T) (o:T) (s:(J₀).Mode):ℂ:=
  ∫ x:Points 3,(χ ⁻¹' {o}).indicator (fun x=>φ x*weight (policy R x) s) x

def ratio (φ ψ:Test 3) {T:Type} (χ:Points 3→T) (o:T) (s:(J₀).Mode):ℂ:=
  payment R φ χ o s/WilsonSeparatedOriginalThermometerCells.weight ψ χ o

private theorem score (φ ψ:Test 3) (cover:∀x:Points 3,ψ x=(‖ψ x‖:ℂ) ∧ ‖φ x‖≤‖ψ x‖)
    {T:Type} [MeasurableSpace T] [MeasurableSingletonClass T] (χ:Points 3→T) (meas:Measurable χ)
    (B:ℝ) (pos:0≤B) (limit:∀x∈tsupport (fun x=>φ x),rent (inverseMass (policy R x))≤B)
    (o:T) (s:(J₀).Mode):
    ‖payment R φ χ o s‖≤B*‖WilsonSeparatedOriginalThermometerCells.weight ψ χ o‖:=by
  let E:=χ ⁻¹' {o}
  have eh:MeasurableSet E:=meas (measurableSet_singleton _)
  let z:=fun x:Points 3=>E.indicator (fun t=>‖ψ t‖) x
  have zi:Integrable z:=(ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).norm.indicator eh
  have positive (x:Points 3):0≤z x:=Set.indicator_nonneg (fun y _=>norm_nonneg _) x
  have total:‖WilsonSeparatedOriginalThermometerCells.weight ψ χ o‖=∫x,z x:=by
    have eq:(fun x=>E.indicator (fun t=>ψ t) x)=fun x=>(z x:ℂ):=by
      funext x
      by_cases hx:x∈E
      · simpa [z,hx] using (cover x).1
      · simp [z,hx]
    change ‖∫x,E.indicator (fun t=>ψ t) x‖=_
    rw [eq,integral_complex_ofReal,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg positive)]
  have ok:Integrable (E.indicator (fun x=>φ x*weight (policy R x) s)):= (φ.smearing (regular R s)).indicator eh
  rw [total,←integral_const_mul]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono ok.norm (zi.const_mul B)
  intro x
  by_cases hx:x∈E
  · simp only [Set.indicator_of_mem hx,z,norm_mul]
    by_cases hφ:φ x=0
    · rw [hφ,norm_zero,zero_mul];exact mul_nonneg pos (norm_nonneg _)
    · have norm:‖weight (policy R x) s‖≤rent (inverseMass (policy R x)):=by
        simpa [rent,WilsonThermometerCenteredAlgebra.weight,Poly.toll] using Poly.member (fun _:Fin 3=>zero_lt_one) (complement s) (inverseMass (policy R x))
      exact (mul_le_mul (cover x).2 (norm.trans (limit _ (subset_tsupport _ hφ))) (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm ..)
  · simp [z,hx]

theorem original (φ:Test 3):
    ∃ψ:Test 3,∃B:ℝ,1≤B ∧ (∀x:Points 3,ψ x=(‖ψ x‖:ℂ) ∧ ‖φ x‖≤‖ψ x‖) ∧
      ∀{T:Type} [MeasurableSpace T] [MeasurableSingletonClass T] (χ:Points 3→T),Measurable χ→∀o:T,
        (∀s:(J₀).Mode,WilsonSeparatedOriginalThermometerCells.weight ψ χ o*ratio R φ ψ χ o s=payment R φ χ o s) ∧
        (∑s:(J₀).Mode,‖ratio R φ ψ χ o s‖)≤8*B:=by
  obtain ⟨ψ,cover⟩:=WilsonMaxwellThermometerNominatedEnvelope.original φ
  obtain ⟨B,one,covered⟩:=budget R φ.hasCompactSupport φ.tsupport_subset
  refine ⟨ψ,B,one,cover,?_⟩
  intro T inst sets χ h o
  let w:=WilsonSeparatedOriginalThermometerCells.weight ψ χ o
  let c:=ratio R φ ψ χ o
  have cash (s:(J₀).Mode):‖payment R φ χ o s‖≤B*‖w‖:=score R φ ψ cover χ h B (zero_le_one.trans one) covered o s
  refine ⟨fun s=>?_,?_⟩
  · by_cases off:w=0
    · have z:payment R φ χ o s=0:=norm_le_zero_iff.mp (by simpa [off] using cash s)
      simp [ratio,z]
    · exact mul_div_cancel₀ _ off
  · have single (s:(J₀).Mode):‖c s‖≤B:=by
      change ‖payment R φ χ o s/w‖≤B
      rw [norm_div]
      by_cases off:w=0
      · simpa [off] using zero_le_one.trans one
      · exact (div_le_iff₀ (norm_pos_iff.mpr off)).mpr (cash s)
    calc
      _≤∑s:(J₀).Mode,B:=Finset.sum_le_sum fun s _=>single s
      _=_:=by
        have n:Fintype.card (J₀).Mode=8:=by decide
        rw [Finset.sum_const,Finset.card_univ,n,nsmul_eq_mul]
        norm_num

end YM.Integration.WilsonMaxwellThermometerNominatedGroundWeights
