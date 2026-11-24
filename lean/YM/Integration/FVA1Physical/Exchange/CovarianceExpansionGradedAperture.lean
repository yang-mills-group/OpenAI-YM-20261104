import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionThreeTestCost
import YM.Next.MULTISOURCE.Stencil

/-! The same numerical seven-face thermometer uses the actual physical field
basis and grading. Each of its three engineering weights is charged once.
The source supports and complex coordinates stay common between the laws. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open MeasureTheory Finset Filter RG Wilson Gauge Lattice Source Multi.Maquette Labels Comparison.RG02
open YM.Integration.FVA1Physical.OriginalMixedWilson
open scoped Classical BigOperators
variable {G:Gauge}{f:Side}{X:Type*}[MeasurableSpace X]

def gradedPhysicalField (A:Family G)(d:ℕ)(w:(A.labels.level d).Coeff)(g:ℝ)(o:Site f)
    (U:Config G f):ℂ:=
  ∑i:(A.labels.level d).Index,(g^((A.labels.level d).grades i).2)⁻¹ •
    ((w i)*(A.localSection d).places (Pi.single i 1) o U)

def gradedPhysicalCost (A:Family G)(d:ℕ)(w:(A.labels.level d).Coeff)(g:ℝ):ℝ:=
  ∑i:(A.labels.level d).Index,‖(g^((A.labels.level d).grades i).2)⁻¹‖ * ‖w i‖*upper (A.localSection d)

theorem graded_field_funded (A:Family G)(d:ℕ)(w:(A.labels.level d).Coeff)(g:ℝ)(o:Site f):
    0≤gradedPhysicalCost A d w g ∧ Continuous (gradedPhysicalField A d w g o) ∧
    ∀U,‖gradedPhysicalField A d w g o U‖≤gradedPhysicalCost A d w g:=by
  refine ⟨sum_nonneg fun i _=>mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (zero_le_one.trans (purposes (A.localSection d) i).1),?_,?_⟩
  · apply continuous_finsetSum
    intro i _
    have wh:Continuous (fun U:Config G f=>w i*(A.localSection d).places (Pi.single i 1) o U):=
      continuous_const.mul ((A.localSection d).continuous_places _ _)
    exact wh.const_smul ((g^((A.labels.level d).grades i).2)⁻¹:ℝ)
  intro U
  apply (norm_sum_le ..).trans
  apply sum_le_sum;intro i _
  rw [norm_smul,norm_mul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((purposes (A.localSection d) i).2 o U)
    (norm_nonneg _)) (norm_nonneg _)

/-- Each source is a measured-coupling finite field on its original torus.
The conditional space may be either the entire held forest or an arbitrary
chosen set of bonds with the exterior fixed. The only remaining exceptional
fee is the original mass outside its specified regular aperture. -/
theorem original_graded_seven_aperture (A:Family G){N n j:ℕ} (_step:j<N)
    (d:Fin 3→ℕ)(w:(i:Fin 3)→(A.labels.level (d i)).Coeff)(o:Fin 3→Site (A.side (j+1) n))
    (make:X → Config G (A.side (j+1) n))(mm:Measurable make)
    (μ:Measure X)[SFinite μ] (B:Set X)(bm:MeasurableSet B)
    (k vref:X→ℝ)(km:Measurable k)(vm:Measurable vref)(kn:∀x,0≤k x)(vp:∀x,0<vref x)
    (t:ℝ)(tn:0≤t):
    let H:=A.path;let P:=H.rep N n (j+1);let g:=measuredCoupling P.beta
    let a:=fun x=>P.eval (make x);let r:=fun x=>Real.log (a x)-Real.log (vref x)
    let u:=fun x=>k x*a x;let v:=fun x=>k x*vref x;let ν:=μ.restrict B
    let h:=fun (i:Fin 3) (x:X)=>gradedPhysicalField A (d i) (w i) g (o i) (make x)
    let U:=fun s=>FrozenRead.meanOn μ u (physicalProperRows h s)
    let V:=fun s=>FrozenRead.meanOn ν v (physicalProperRows h s)
    let L:=fun i=>gradedPhysicalCost A (d i) (w i) g
    H.Selected→Integrable u μ→Integrable v ν→0<(∫x,u x ∂μ)→0<(∫x,u x ∂ν)→0<(∫x,v x ∂ν)→
    (∀x∈B,∀y∈B,Replica.cap (r x-r y)≤t)→
    (∫x,u x ∂μ)*‖properThree U-properThree V‖≤26*L 0*L 1*L 2*((∫x,u x ∂ν)*t+∫x in Bᶜ,u x ∂μ):=by
  intro H P g a r u v ν h U V L sel ui vi up ub ip fee
  have am:Measurable a:=(P.envelope (sel.represents N n (j+1) _step).good).meas.comp mm
  have ap(x):0<a x:=SectorNext.Vacuum.strictly H sel N n (j+1) _step _
  have field(i:Fin 3):=graded_field_funded A (d i) (w i) g (o i)
  have eh(i:Fin 3):Envelope (h i):=⟨(field i).2.1.measurable.comp mm,L i,fun x=>(field i).2.2 (make x)⟩
  exact (funded_seven_aperture (μ:=μ) B bm km am vm kn ap vp (am.log.sub vm.log) 0
    (fun _=>by simp only [add_zero];rfl) t tn fee h eh L (fun i=>(field i).1)
    (fun i x=>(field i).2.2 (make x)) ui vi up ub ip).2

end YM.Integration.FVA1Physical.Exchange.RoseCut
