import YM.Integration.WilsonOriginalAffineAngularRay
import YM.Integration.PhysicalForestMarkedRay

/-! Curved radial substitution of a funded marked field, using its own
vanishing grade to clear the physical pole once. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalClearedAngularRead
open Function Filter Matrix Finset PowerSeries WilsonCoeffUV WilsonCoeffUV.Blue
open PositionX.Jet AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Fire
open AllOrder.Laplace PertExtension.Series Radial AllOrder.Laplace.SigmaP Response
open Comparison.RG02
open scoped ContDiff Topology BigOperators Classical
variable {I X:Type}[Fintype I][NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]

private theorem smooth_eval (a:ℝ→Lawn I)(ha:ContDiffAt ℝ ω a 0)(P:MvPolynomial I ℝ):
    ContDiffAt ℝ ω (fun t=>MvPolynomial.eval (a t) P) 0:=by
  induction P using MvPolynomial.induction_on with
  | C c=>simpa only [MvPolynomial.eval_C] using (contDiffAt_const:ContDiffAt ℝ ω (fun _:ℝ=>c) 0)
  | add p q hp hq=>simpa only [map_add] using hp.add hq
  | mul_X p i hp=>
    have hi:ContDiffAt ℝ ω (fun t=>a t i) 0:=(contDiffAt_apply ..).comp 0 ha
    simpa only [map_mul,MvPolynomial.eval_X] using hp.mul hi

variable {K:ℕ}(F:X→ℂ)(graded:Assembly.GradeAt K F)
variable (u:ℝ→X)(hu:ContDiffAt ℝ ω u 0)(a:ℝ→Lawn I)(ha:ContDiffAt ℝ ω a 0)
variable (w:ℂ)(P:Ink I)(j:ℕ)
variable (row:∀ i≤j,∀ t:ℝ, Assembly.jet F (K+i) (u t)=w*Complex.ofReal (MvPolynomial.eval (a t) (coeff i P)))
include graded hu ha row

private theorem component (L:ℂ→L[ℝ]ℝ):
    someJ (L ∘ F ∘ echo u) (K+j)=L w*weigh a (fun i A=>MvPolynomial.eval A (coeff i P)) j:=by
  have hf:ContDiffAt ℝ ω (L ∘ F) 0:=L.contDiff.contDiffAt.comp 0 graded.smooth
  have zeroLow (i:ℕ)(hi:i<K):Radial.jet (L ∘ F) i=0:=by
    funext x
    change Assembly.jet (L ∘ F) i x=0
    rw [←Assembly.jet_apply_left L F i (graded.smooth.of_le le_top),graded.jet_z x hi,map_zero]
  change someJ ((L ∘ F) ∘ echo u) (K+j)=_
  rw [weigh_curved hf hu,add_comm K j,weigh_higher zeroLow,weigh,weigh,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hit:=Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  let p:=fun t:ℝ=>MvPolynomial.eval (a t) (coeff i P)
  have smoothP:ContDiffAt ℝ ω p 0:=smooth_eval a ha _
  have one:(Radial.jet (L ∘ F) (i+K) ∘ u)=L w • p:=by
    funext t
    change Assembly.jet (L ∘ F) (i+K) (u t)=L w*p t
    rw [←Assembly.jet_apply_left L F _ (graded.smooth.of_le le_top),
      add_comm i K,row i hit]
    change L (w*↑(p t))=_
    rw [mul_comm,←Complex.real_smul,map_smul,smul_eq_mul,mul_comm]
  rw [one]
  exact ((eo_Act (j-i) smoothP).smul (L w)).writes (j-i) le_rfl

theorem original :
    PhysicalForestMarkedRay.readJet (K+j) (F ∘ echo u)=
      w*Complex.ofReal (weigh a (fun i A=>MvPolynomial.eval A (coeff i P)) j):=by
  obtain h:=component F graded u hu a ha w P j row Complex.reCLM
  obtain k:=component F graded u hu a ha w P j row Complex.imCLM
  have hr: (⇑Complex.reCLM:ℂ→ℝ)=Complex.re:=funext fun _=>rfl
  have hi: (⇑Complex.imCLM:ℂ→ℝ)=Complex.im:=funext fun _=>rfl
  rw [hr] at h
  rw [hi] at k
  apply Complex.ext
  · simpa [PhysicalForestMarkedRay.readJet,someJ,Complex.mul_re] using h
  · simpa [PhysicalForestMarkedRay.readJet,someJ,Complex.mul_im] using k

end YM.Integration.WilsonOriginalClearedAngularRead
end
