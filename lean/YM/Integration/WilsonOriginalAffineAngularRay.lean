import YM.Integration.ForestRaySeries
import YM.Integration.WilsonOriginalPrimerCourseRead
import YM.AllOrder.Laplace.Price

/-! The original affine source substitution on an arbitrary full angular
ink. Its coefficient is evaluated on the analytic velocity of the same
nonlinear forest curve, including its nonzero initial velocity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAffineAngularRay
open Function Filter Finset Matrix PowerSeries Laurent WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonCoeffUV.Blue.Cameo Integration.OriginalRadialSeries
open PositionX.Jet AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Fire
open AllOrder.Laplace PertExtension.Series Radial AllOrder.Laplace.SigmaP Response
open scoped Topology ContDiff BigOperators Classical
variable {U V Y:Type}[Fintype U][Fintype V][Fintype Y]
variable (θ:Lawn (U⊕V)→Lawn U)(D:Matrix Y (U⊕V) ℝ)(v:Lawn (U⊕V))

def image :Ink Y→+*PowerSeries ℝ:=(OriginalRadialSeries.observed v).comp ((retool θ).comp (loom D))
def pathAt (t:ℝ) :Lawn Y:=D *ᵥ spider θ (t • v)
def direction :ℝ→Lawn Y:=dslope (pathAt θ D v) 0

omit [Fintype Y] in
theorem origin (h0:θ 0=0):pathAt θ D v 0=0:=by simp [pathAt,spider_zero h0]

theorem regular (ht:Green θ)(h0:θ 0=0):ContDiffAt ℝ ω (pathAt θ D v) 0:=by
  have a : ContDiffAt ℝ ω (fun t:ℝ=>t • v) 0:=contDiffAt_id.smul contDiffAt_const
  apply ContDiffAt.comp 0 (g:=fun x=>D *ᵥ x) (by simpa only [zero_smul,spider_zero h0] using board D)
  exact ContDiffAt.comp 0 (by simpa only [zero_smul] using spider_green ht) a

theorem smooth (ht:Green θ)(h0:θ 0=0):ContDiffAt ℝ ω (direction θ D v) 0:= shifty (regular θ D v ht h0)

theorem raw (h0:θ 0=0)(t:ℝ):pathAt θ D v t=t • direction θ D v t:=shift_start (origin θ D v h0) t

omit [Fintype Y] in
private theorem parameter : image θ D v X=X:=by
  simp [image,OriginalRadialSeries.observed,retool,loom,reroll_X]

private theorem x_scalar :
    OriginalRadialSeries.scalar (fun t:ℝ=>t)=X:=by
  have q:=(ForestRaySeries.powers (fun _:Unit=>1) 1).read
  simpa only [pow_one,OriginalRadialSeries.observed,PowerSeries.map_X] using q.symm

include θ D v in
private theorem coordinate (ht:Green θ)(h0:θ 0=0)(i:Y):
    ForestRaySeries.Reads v (retool θ (loom D (PowerSeries.C (MvPolynomial.X i))))
      (fun t=>direction θ D v t i):=by
  have hs:ContDiffAt ℝ ω (fun t=>direction θ D v t i) 0:=
    (contDiffAt_apply ..).comp 0 (smooth θ D v ht h0)
  refine ⟨hs,?_⟩
  change image θ D v (path i)=_
  apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R:=ℝ))
  have htau:=ForestRaySeries.linear θ ht h0 v D (fun y:Lawn Y=>y i) (contDiffAt_apply ..)
  have h: image θ D v (jet (fun y:Lawn Y=>y i))=OriginalRadialSeries.scalar (fun t=>pathAt θ D v t i):=htau.read
  rw [jet_arg,map_mul,parameter] at h
  rw [h,←x_scalar,←OriginalRadialSeries.mul (f:=fun t:ℝ=>t) contDiffAt_id hs]
  apply congrArg OriginalRadialSeries.scalar
  funext t
  exact congrFun (raw θ D v h0 t) i

private theorem polynomial (ht:Green θ)(h0:θ 0=0)(p:MvPolynomial Y ℝ):
    ForestRaySeries.Reads v (retool θ (loom D (PowerSeries.C p)))
      (fun t=>MvPolynomial.eval (direction θ D v t) p):=by
  induction p using MvPolynomial.induction_on with
  | C c=>
    simpa only [jet_const,realS,RingHom.comp_apply,MvPolynomial.eval_C] using
      ForestRaySeries.linear θ ht h0 v D (fun _:Lawn Y=>c) contDiffAt_const
  | add p q hp hq=>simpa only [map_add] using ForestRaySeries.add hp hq
  | mul_X p i hp=>simpa only [map_mul,MvPolynomial.eval_X] using ForestRaySeries.mul hp (coordinate θ D v ht h0 i)

theorem coefficient (ht:Green θ)(h0:θ 0=0)(P:Ink Y)(k:ℕ):
    coeff k (image θ D v P)=weigh (direction θ D v) (fun j A=>MvPolynomial.eval A (coeff j P)) k:=by
  have fixed:=parameter θ D v
  have paid:=filtered (ξ:=image θ D v) (by rw [fixed,constantCoeff_X]) (shave P (k+1)) k (Nat.lt_succ_self k)
  rw [paid]
  simp only [map_sum,map_mul,map_pow,fixed,coeff_mul_X_pow']
  unfold weigh
  apply Finset.sum_congr rfl
  intro j hj
  have fit:=polynomial θ D v ht h0 (coeff j P)
  rw [if_pos (Nat.lt_succ_iff.mp (mem_range.mp hj)),show image θ D v (PowerSeries.C (coeff j P))=_ from fit.read,
    OriginalRadialSeries.numeric _ fit.regular]
  rfl

end YM.Integration.WilsonOriginalAffineAngularRay
end
