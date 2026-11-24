import YM.Integration.WilsonSurveyedColorMeeting

/-! Integrate the phase-weighted two-source row on its own position-space
kernel with both actual derivative legs and the original real measure. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorContact
open Function Set Finset MeasureTheory
open MS
open Plane Koszul Heat Flux Landau Detect Tone City Latch Latch.Job Rake Arts
open WilsonSurveyedColorQuotient WilsonSurveyedColorPilot WilsonSurveyedColorMeeting
open scoped Classical BigOperators
variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color)
local notation "CI" => G.ColorIndex
local notation "Ψ" => field (Landau.parity (A:=Axis) (C:=G.ColorIndex))
local notation "Words" => Legs (Lane4 G)

private def nativeRow (A q : QP) (K : City.YMflow Axis) (F H : Law G)
    (l r : Words) : ℂ :=
  Tone.bill A (net l) * ∑ i : BH G, ∑ j : BH G,
    Tone.bill A q * meshZ (Landau.choir K id) i j F H l r q

private theorem asRow (A q : QP) (K : City.YMflow Axis) (F H : Law G)
    (w : Words) : incoming A q K F H w = scatter Ψ w (nativeRow A q K F H) := by
  let head (a b : Atom Axis) (c : CI) : Shared (Lane4 G) ℂ := fun l r =>
    phased A (sign Ψ (Landau.p b) (Koszul.D ((a,c),q) F)) l * Koszul.D ((b,c),-q) H r
  let total : Shared (Lane4 G) ℂ :=
    ∑ a, ∑ b, (Tone.bill A q * (2*K a b q)) • ∑ c : CI,head a b c
  have first : incoming A q K F H w = allocate Ψ w total := by
    simp only [total,map_sum,map_smul,incoming,pair,Finset.sum_apply,Pi.smul_apply]
    simp only [vertex,LinearMap.comp_apply,scattered]
    rfl
  rw [first]
  change allocate Ψ w total = allocate Ψ w (nativeRow A q K F H)
  congr 1
  funext l r
  unfold nativeRow
  simp only [total,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,head,phased,LinearMap.coe_mk,
    AddHom.coe_mk,at_sign,at_D,Fintype.sum_prod_type,meshZ,Landau.choir,id_eq]
  simp only [mul_ite,ite_mul,zero_mul,mul_zero]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => ?_
  refine Finset.sum_congr rfl fun _ _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  refine Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem priced (A : QP) (K : City.YMflow Axis) (F H : Law G) (μ : Measure QP)
    (paid : SatP μ (Landau.choir K id) F H A) (w : Words) :
    Integrable (fun q => incoming A q K F H w) μ ∧
      Cabin A (Landau.choir K id) μ F H w = ∫ q, incoming A q K F H w ∂μ := by
  have port (l r : Words) : Integrable (fun q => nativeRow A q K F H l r) μ :=
    (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      paid i j l r))).const_mul _
  let L (f : Words × Words → ℂ) := scatter Ψ w (fun l r => f (l,r))
  have finite : L ∈ Centre _ := cent_gather Ψ w (fun v l r => v (l,r))
    (fun l r _ => centroid (l,r))
  have pre := cent_arguments μ finite (f:=fun q t => nativeRow A q K F H t.1 t.2)
    (fun t => port t.1 t.2)
  simp_rw [asRow]
  refine ⟨pre.1,?_⟩
  change _ = ∫ q, L (fun t => nativeRow A q K F H t.1 t.2) ∂μ
  rw [pre.2]
  change allocate Ψ w _ = allocate Ψ w _
  apply congrArg (allocate Ψ w)
  funext l r
  simp only [nativeRow,integral_const_mul]
  congr 1
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => paid i j l r))]
  exact Finset.sum_congr rfl fun i _ => (integral_finsetSum _ (fun j _ => paid i j l r)).symm

theorem contact (A : QP) (K : City.YMflow Axis) (F H : Law G) (μ : Measure QP)
    (paid : SatP μ (Landau.choir K id) F H A)
    (paidTurn : SatP μ (Landau.choir K id) (turn U F) (turn U H) A) :
    turn U (Cabin A (Landau.choir K id) μ F H) =
      Cabin A (Landau.choir K id) μ (turn U F) (turn U H) := by
  have cl := priced A K F H μ paid
  have cr := priced A K (turn U F) (turn U H) μ paidTurn
  have eqh : Cabin A (Landau.choir K id) μ F H = (fun w => ∫ q, incoming A q K F H w ∂μ) :=
    funext fun w => (cl w).2
  funext w
  have pick := (cent_arguments μ ((pilot (D:=Axis) (P:=QP) U).sense.reaches w)
    (f:=fun q => incoming A q K F H) (fun l => (cl l).1)).2
  simp_rw [emits,incomingColor U] at pick
  exact (congrArg (fun F : Law G => turn U F w) eqh).trans (pick.symm.trans (cr w).2.symm)

end YM.Integration.WilsonSurveyedColorContact
end
