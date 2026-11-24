import YM.FVAAlt2.Rescaled
import YM.FVAAlt2.AnalyticJets

/-!
# Remove ghosts. Expand contour Jacobian. Bose scalar PS
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2
open SchemeRG11.Sway Lattice Function MS MS.Book MS.Koszul MS.Native MS.Native.Wilsonian MS.Cylinder MS.Cylinder.Taylor
open MS.Orbit MS.Orbit.LogReal MS.Orbit.Cog MS.Cylinder.Lab Finset Filter Topology Pert.Orb PertExtension.Series.Radial
open MeasureTheory MS.Puff MS.Swirl AnalyticJets Lam
open scoped ContDiff PowerSeries
variable {G:Gauge}{n:Side}{ι κ:Type}[Fintype ι][DecidableEq ι][Fintype κ][DecidableEq κ]
variable (A : Module.Basis ι ℝ (Land G n))(b: Module.Basis κ ℝ (ScalarGhost G n))
local notation "E"=> Com (isOdd (ι:=ι) (κ:=κ))
local notation "K"=> propagator (κ:=κ) A
local notation "B"=> Bos ι
local notation "T"=> PowerSeries (Com (isOdd (ι:=ι) (κ:=κ)))
local notation "𝑩"=>PowerSeries (Bos ι)
local notation "V"=> Land G n
local notation "p"=> isOdd (ι:=ι) (κ:=κ)
local notation "μ"=> chosen G n
local notation "L"=>embeddingM A b
local notation "f!"=> Com.forget p
local notation "T'"=> PowerSeries ℂ
local notation "C"=> PowerSeries.C (R:=ℂ)
local notation "mℂ"=> Bos.μC G n
set_option quotPrecheck false
local notation "🜂"=> (radiant A b).map (Bos.upS (κ:=κ))
set_option linter.unusedSectionVars false

def valS4 (x:V):𝑩→+* T':= PowerSeries.map ((Bos.value A x).toRingHom)

lemma value_bob (u:Land G n)(f:Land G n→ℝ)(hf:germ f)(i:ℕ): Bos.value A u (Bos.bob A f hf i)=(↑(jet f i u):ℂ):= by unfold Bos.value; have hx:= @Bos.sphere ι _ (Land G n) _ _ A u f hf i; exact hx
lemma valSeriesInk(f:Land G n→ℝ)(h:germ f)(x:Land G n): valS4 A x (Bos.seriesInk A f h)=fitR f x:= by ext1 i; rw [val_at]; unfold valS4; rw [Bos.seriesInk,PowerSeries.coeff_map,PowerSeries.coeff_mk]; exact value_bob A x f h i
lemma exp_price_land(x:V): valS4 A x (formExp (priceMat A))= expR (baseR (LAND (G:=G) (n:=n))) x := by
  rw [valS4,←formExp_map]
  change formExp (valS4 A x _) = formExp (baseR LAND x)
  congr 1; ext i; rw [valS4,priceMat,baseR,cscale,PowerSeries.coeff_map,PowerSeries.coeff_mk,PowerSeries.coeff_mk]; unfold PertExtension.Series.Radial.layers; split_ifs
  · rw [map_zero]; simp [*]
  rw [add_zero,map_neg, Complex.ofReal_neg]; exact congrArg Neg.neg (value_bob A x (LAND (G:=G) (n:=n)) LANDsmooth (i+2))
lemma exp_haar_land(x:V): valS4 A x (formExp (hrMat A))= fitR (fun y:Land G n=> Jacob y.val) x:=by
 let f(y:Land G n):= Jacob y.val
 have he:Real.exp ∘ (hrLog (G:=G) (n:=n))=ᶠ[𝓝 0] f := ((hJac (G:=G) (n:=n)).continuousAt.eventually (lt_mem_nhds (show 0<f 0 from by simp [f]))).mono fun i h=>Real.exp_log h
 rw [valS4,← formExp_map]; change formExp (valS4 A x _) = _
 rw [hrMat,valSeriesInk,← expCanon x hLog (by simp [hrLog]),valGerm x he]

section detg
variable {X J : Type}[Fintype J][DecidableEq J][NormedAddCommGroup X][NormedSpace ℝ X]
open Matrix
lemma valDet (F:J→J→X→ℝ)(x:X)(h:∀ i j,germ (F i j)) : (Matrix.of fun i j=> fitR (F i j) x).det= fitR (fun y=> (Matrix.of fun i j=> F i j y).det) x:= by
 simp_rw [Matrix.det_apply']; let t (σ: Equiv.Perm J) : ℝ:= (↑(Equiv.Perm.sign σ):ℤ)
 have hu(σ): germ (fun y=> t σ * ∏ i:J,F (σ i) i y):=contDiffAt_const.mul (contDiffAt_prod (fun i _=> h _ _))
 simp only [Matrix.of_apply]; rw [valSum x _ (fun σ y=> t σ * ∏ i:J,F (σ i) i y) (fun i _=>hu i) ]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [valMul x (f:=fun _=>t i) contDiffAt_const (contDiffAt_prod (fun j _=>h (i j) j)),valConst,valProd x univ _ (fun j _=> h _ _)]
 unfold t; push_cast; rw [map_intCast]
end detg

def fullP (x:Land G n): Matrix κ κ ℝ:= fun j k=> -fpLetter b j k x
lemma full_cost : ∀ᶠ x:Land G n in 𝓝 0,(fullP b x).det=((paneLap G n).symm.toContinuousLinearMap ∘L paneGhost G n x).det:=by
 filter_upwards [eventually_all.mpr (fun x:κ=>eventually_all.mpr (fun y=>ghost_matrix b x y))] with x hx
 let L' : (↥(Flow G n)) →L[ℝ] ↥(Flow G n):=(paneLap G n).symm.toContinuousLinearMap ∘L paneGhost G n x
 have ht:fullP b x= LinearMap.toMatrix b b L'.toLinearMap:= by ext i j; rw [LinearMap.toMatrix_apply]; change -fpLetter b i j x=_; rw [show fpLetter _ _ _ x=_ from hx i j,neg_neg]; rfl
 rw [ht,LinearMap.det_toMatrix]
lemma matrix_expensive (x:V) : valS4 A x (1+radiant A b).det= fitR (fun y=> (fullP b y).det) x:= by
 let F:Matrix κ κ 𝑩:=radiant A b -- fix
 have he: (valS4 A x).mapMatrix (1+radiant A b)=Matrix.of fun i j=> fitR (fun y=> -fpLetter b i j y) x:=by
   ext i j : 1; change valS4 A x ((1+F) i j) =_ ; rw [show 1+F= Matrix.of (FPInk A b) from by unfold F radiant; abel, Matrix.of_apply, Matrix.of_apply,valNeg x (barTree ..),FPInk,map_neg,valSeriesInk]
 rw [RingHom.map_det, he,valDet (fun i j y=> - fpLetter b i j y) x (fun i j=> (barTree b i j).neg)]; -- rfl
 rfl

def effective : 𝑩:= formExp (priceMat A+hrMat A)*(1+radiant A b).det
lemma valuation_body (x:V): valS4 A x (effective A b) = Lam.fibers LAND LANDweight x:= by
 let J(y:V):= Jacob y.val
 let Z(y:V):= (fullP b y).det
 unfold effective; rw [Com.exponent_add (by rw [PowerSeries.coeff_zero_eq_constantCoeff,price0]) (by rw [PowerSeries.coeff_zero_eq_constantCoeff,hr0]), map_mul,map_mul, matrix_expensive,exp_haar_land,exp_price_land]
 change expR _ x * Lam.fitR J x * Lam.fitR Z x=_*_
 have hu:germ Z:=by
   unfold Z fullP; simp_rw [Matrix.det_apply']; apply ContDiffAt.sum; intro i _; exact contDiffAt_const.mul (contDiffAt_prod (fun j _=> (barTree b _ _).neg))
 rw [mul_assoc, ← valMul x (show germ J from hJac) hu]; apply congrArg _; apply valGerm; exact (full_cost b).mono fun i ht=> congrArg (J i*·) ht
end YM.FVAAlt2
