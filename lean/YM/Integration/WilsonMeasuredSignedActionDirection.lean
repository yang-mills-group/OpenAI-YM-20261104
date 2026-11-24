import YM.Integration.WilsonMeasuredPublicEntranceMarkedQuadratics
import YM.TraceExtension.Atlas.Horns
import YM.Next.MAXWELL.System

/-! The Ward action on the free limit of the original Wilson fields uses one quarter
of the sum of the ordered squared curls. The color test uses each of the six
plaquette orientations once. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace YM.Integration.WilsonMeasuredSignedActionDirection
open Function Finset Climb Maxwell Maxwell.Free XSpace.Stab Trace Trace.Pilot
open StressFlux Labels
open WilsonMeasuredPublicEntranceMarkedQuadratics WilsonMeasuredPublicEntranceQuadraticGrid
open scoped Classical BigOperators Topology InnerProductSpace
variable {G:Gauge}

private theorem native_pair (a b:Axis):
    reduceEq (StressFlux.pair G a b a b).val = team G (Maxwell.Free.cell a b) (Maxwell.Free.cell a b):=by
  apply Maxwell.equalPol
  intro X
  rw [Maxwell.jet_value,StressFlux.pair_value,Maxwell.Free.basicTeam]
  have he:curl0 a b (Maxwell.gaugeJet (X 0))=Tensor.diagonal ((X 0).val a b) 0:=
    congrArg (fun Q:Maxwell.TwoJet G.Color 0=>Tensor.diagonal (Q a b) 0) (Maxwell.match_leg (X 0))
  rw [he]
  rfl

private theorem swap (a b:Axis): StressFlux.pair G a b a b=StressFlux.pair G b a b a:=by
  apply StressFlux.label_ext
  intro J
  rw [pair_value,pair_value,show curl0 a b (J 0) = -curl0 b a (J 0) from curled_swap ..]
  simp

private theorem zero_pair (a:Axis): StressFlux.pair G a a a a=0:=by
  apply StressFlux.label_ext
  intro J
  rw [pair_value]
  have hz:curl0 a a (J 0)=0:=by
    simp [curl0_value]
  simp [hz]

private theorem six (G:Gauge):
    (∑ a:Axis,∑ b:Axis,StressFlux.pair G a b a b)=
    (2:ℝ) • ∑ i:Fin 6,StressFlux.pair G (edge i).1 (edge i).2 (edge i).1 (edge i).2:=by
  rw [Fin.sum_univ_six]
  simp only [Fin.sum_univ_four,zero_pair,edge,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,
    zero_add,add_zero]
  rw [swap (G:=G) 1 0,swap (G:=G) 2 0,swap (G:=G) 2 1,swap (G:=G) 3 0,
    swap (G:=G) 3 1,swap (G:=G) 3 2,two_smul]
  abel

theorem direct (C:Family G):
    (2:ℝ) • (fields C.labels 4 (stepField C))=marked G (le_refl 4) 1:=by
  apply Subtype.ext
  change (2:ℝ) • (fields C.labels 4 ((Bel C.book).project 4 ((C.labels.level 4).coords (square4 G)))).val=_
  rw [fields_eval]
  change (2:ℝ) • reduceEq (((C.labels.level 4).coords.symm ((C.labels.level 4).coords (square4 G))).val)=_
  rw [LinearEquiv.symm_apply_apply]
  have half:square4 G=(1/2:ℝ) • ∑ i:Fin 6,StressFlux.pair G (edge i).1 (edge i).2 (edge i).1 (edge i).2:=by
    unfold square4
    rw [six,smul_smul]
    norm_num
  rw [half]
  change (2:ℝ) • reduceEq ((1/2:ℝ) • _)=_
  rw [show ∀w:Pol G,reduceEq ((1/2:ℝ) • w)=(1/2:ℝ) • reduceEq w from fun w=>
    (reduceEq.toLinearMap.restrictScalars ℝ).map_smul _ w,smul_smul]
  norm_num
  simp only [AddSubmonoidClass.coe_finsetSum,map_sum,native_pair]
  change _=(∑i:Fin 6,∑j:Fin 6,((1:Plane ℝ) i j) • tile (G:=G) (le_refl 4) i j).val
  simp only [Matrix.one_apply,ite_smul,one_smul,zero_smul,Finset.sum_ite_eq,Finset.mem_univ,
    if_true,AddSubmonoidClass.coe_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [native_axes]
  rfl

end YM.Integration.WilsonMeasuredSignedActionDirection
