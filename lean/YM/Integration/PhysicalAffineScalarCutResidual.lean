import YM.Integration.PhysicalAffineScalarUncut

/-! The actual finite-aperture scalar versus the independently prescribed
uncut stationary scalar, with every retained and changed row at its original
translation root. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarCutResidual
open Function Matrix Lattice Wilson RG RG.Shoot Precision Exterior Tree
open Pressure Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent.Affine
open PhysicalAffineScalarAperture (noHole)
open PhysicalAffineScalarUncut (remaining)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

section algebra
variable {α ι : Type} [Fintype α] [Fintype ι] [DecidableEq ι]
    (D E : Matrix α ι ℝ)
local notation "C" => (D.transpose*D)⁻¹
local notation "K" => (E.transpose*E)⁻¹

private theorem difference : remaining D - remaining E =
    -((D-E)*C*D.transpose + E*(C-K)*D.transpose + E*K*(D-E).transpose) := by
  unfold remaining
  simp only [Matrix.transpose_sub,Matrix.sub_mul,Matrix.mul_sub]
  abel

private theorem telescope (f h : Gaussian.Vec α) : remaining D *ᵥ f - remaining E *ᵥ h =
    remaining D *ᵥ (f-h) - ((D-E)*C*D.transpose) *ᵥ h - (E*(C-K)*D.transpose) *ᵥ h -
      (E*K*(D-E).transpose) *ᵥ h := by
  calc
    _ = remaining D *ᵥ (f-h) + (remaining D - remaining E) *ᵥ h := by
      rw [Matrix.mulVec_sub,Matrix.sub_mulVec]; abel
    _ = _ := by rw [difference,Matrix.neg_mulVec,Matrix.add_mulVec,Matrix.add_mulVec]; abel

private theorem annihilates (hD : (D.transpose*D).PosDef) : remaining D * D = 0 := by
  calc
    _ = D - D*(C*(D.transpose*D)) := by simp only [remaining,Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc]
    _ = _ := by rw [Matrix.nonsing_inv_mul _ (IsUnit.mk0 _ hD.det_pos.ne'),Matrix.mul_one,sub_self]

private theorem normal (h : Gaussian.Vec α) (hE : (E.transpose*E).PosDef) :
    E.transpose *ᵥ (E *ᵥ PhysicalAffineScalarUncut.minimizer E h + h) = 0 := by
  rw [PhysicalAffineScalarUncut.minimizer,Matrix.mulVec_add,Matrix.mulVec_mulVec,Matrix.mulVec_neg,
    Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ hE.det_pos.ne'),Matrix.one_mulVec,neg_add_cancel]

/-- The exact least-squares perturbation uses one removed source or row
in every summand, with ordinary physical inverse bounds on either side. -/
private theorem perturb (f h : Gaussian.Vec α) (hD : (D.transpose*D).PosDef) (hE : (E.transpose*E).PosDef) :
    let a := PhysicalAffineScalarUncut.minimizer E h
    let r := E *ᵥ a + h
    remaining D *ᵥ f - r = remaining D *ᵥ ((f-h)+(D-E) *ᵥ a) - D *ᵥ (C *ᵥ ((D-E).transpose *ᵥ r)) := by
  intro a r
  let v := (f-h)+(D-E) *ᵥ a
  have hf : f = v+r-D *ᵥ a := by
    change _ = ((f-h)+(D-E) *ᵥ a)+(E *ᵥ a+h)-D *ᵥ a
    rw [Matrix.sub_mulVec]
    abel
  have hz : remaining D *ᵥ (D *ᵥ a) = 0 := by rw [Matrix.mulVec_mulVec,annihilates D hD,Matrix.zero_mulVec]
  have ht : D.transpose *ᵥ r = (D-E).transpose *ᵥ r := by
    rw [Matrix.transpose_sub,Matrix.sub_mulVec,show E.transpose *ᵥ r = 0 from normal E h hE,sub_zero]
  have hr : remaining D *ᵥ r = r - D *ᵥ (C *ᵥ ((D-E).transpose *ᵥ r)) := by
    rw [remaining,Matrix.sub_mulVec,Matrix.one_mulVec,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,ht]
  calc
    _ = remaining D *ᵥ (v+r-D *ᵥ a)-r := congrArg (fun z => remaining D *ᵥ z-r) hf
    _ = remaining D *ᵥ v + remaining D *ᵥ r - r := by rw [Matrix.mulVec_sub,Matrix.mulVec_add,hz,sub_zero]
    _ = _ := by rw [hr]; abel
end algebra

variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S) (x : ℝ) (k : S.Choices)
    (F : Forest S.ratio) (q : Chi) (d : ℝ) {p : Clip} {σ E Λ : ℝ}
local notation "A" => noHole S
local notation "W" => shots S x
local notation "Coarse" => Gaussian.Vec (Raw G c)
local notation "V" => fun B : Coarse => represent (decode B)
local notation "keys" => Rows.In (G:=G) x A F
local notation "Dc" => fun B : Coarse => Rows.move T x (V B) k W A F
local notation "Du" => PhysicalAffineScalarUncut.columns T x k F
local notation "Qc" => fun B : Coarse => Rows.gram T x (V B) k W A F
local notation "Qu" => PhysicalAffineScalarUncut.gram T x k F
local notation "fc" => fun (Y : LinkArray G (Frozen A x F)) (B : Coarse) => Rows.source T x (V B) k W A F q d Y
local notation "fu" => PhysicalAffineScalarUncut.offset T k
local notation "ru" => PhysicalAffineScalarUncut.sourceResidual T x k F

/-- This is the unmasked, physically normalized finite-radius source. -/
def shortSource (B : Coarse) : Prices G (Slots S) := tape.symm (slip • Rows.base T x (V B) k)

def sourceGuard (B : Coarse) := tape.symm (Rows.restrict x W A F (Rows.base T x (V B) k)) - shortSource T x k B

def sourceRoutes (B : Coarse) := shortSource T x k B - fu B

def sourceGap (Y : LinkArray G (Frozen A x F)) (B : Coarse) := fc Y B - fu B

/-- The genuine no-hole chart has no frozen direction, for every original
Haar value Y and every coarse background. -/
theorem frozen_zero (Y : LinkArray G (Frozen A x F)) (B : Coarse) (hT : T.up.Bounds p σ E Λ) :
    fc Y B = tape.symm (Rows.restrict x W A F (Rows.base T x (V B) k)) := by
  have hb : Rows.bump T x (V B) k 0 = 0 := by
    simpa only [zero_smul] using Rows.bump_smul T x (V B) k hT (0:Directions G f) (0:ℝ)
  change Rows.source T x (V B) k W A F q d Y = _
  unfold Rows.source
  rw [PhysicalAffineScalarAperture.no_frozen x F,hb,add_zero]

theorem source_parts (Y : LinkArray G (Frozen A x F)) (B : Coarse) (hT : T.up.Bounds p σ E Λ) :
    sourceGap T x k F q d Y B = sourceGuard T x k F B + sourceRoutes T x k B := by
  unfold sourceGap sourceGuard sourceRoutes
  rw [frozen_zero T x k F q d Y B hT]
  abel

theorem source_guard_zero (B : Coarse) (h : ∀ i : Slots S, Rows.keep x W A F i) :
    sourceGuard T x k F B = 0 := by
  have hh : Rows.restrict x W A F (Rows.base T x (V B) k) = slip • Rows.base T x (V B) k := by
    funext i
    simp only [Rows.restrict,h i,if_true,Pi.smul_apply]
  rw [sourceGuard,hh,shortSource,sub_self]

/-- Thus the actual tail is exactly the physical finite-minus-infinite
source on each signed component after the row guard has been discharged. -/
theorem source_read (B : Coarse) (i : Slots S) :
    tape (sourceRoutes T x k B) i = slip • PhysicalAffineScalarJets.offset T x k B i - tape (fu B) i := by
  change gaugeCount (gaugeCount.symm (slip • Rows.base T x (V B) k) - fu B) i = _
  rw [map_sub,ContinuousLinearEquiv.apply_symm_apply,PhysicalAffineScalarJets.offset_eq]
  rfl

def shortColumns (B : Coarse) : Matrix (Rows.Receipt G S) keys ℝ := Matrix.of fun i j =>
  tape.symm (slip • Rows.bump T x (V B) k (Rows.fresh x W A F (axisPrice j))) i

def columnGuard (B : Coarse) := Dc B - shortColumns T x k F B

def columnRoutes (B : Coarse) := shortColumns T x k F B - Du B

def columnGap (B : Coarse) := Dc B - Du B

theorem column_guard_zero (B : Coarse) (h : S.patch.Branches S.kernel G) : columnGuard T x k F B = 0 := by
  have hh (j : keys) : Rows.restrict x W A F (Rows.bump T x (V B) k (Rows.fresh x W A F (axisPrice j))) =
      slip • Rows.bump T x (V B) k (Rows.fresh x W A F (axisPrice j)) := by
    funext i
    rcases i with ⟨s,i⟩
    by_cases hi : Rows.keep x W A F (s,i)
    · simp only [Rows.restrict,hi,if_true,Pi.smul_apply]
    · simp only [Rows.restrict,hi,if_false,Pi.smul_apply,Next.SectorChange.skip_bump T x (V B) k A F s i (axisPrice j) h hi,smul_zero]
  ext i j
  change tape.symm (Rows.restrict x W A F (Rows.bump T x (V B) k (Rows.fresh x W A F (axisPrice j)))) i -
    tape.symm (slip • Rows.bump T x (V B) k (Rows.fresh x W A F (axisPrice j))) i = 0
  rw [hh,sub_self]

theorem column_parts (B : Coarse) (h : S.patch.Branches S.kernel G) :
    columnGap T x k F B = columnRoutes T x k F B := by
  have hh := sub_eq_zero.mp (column_guard_zero T x k F B h)
  exact congrArg (fun J => J - Du B) hh

def cutResidual (Y : LinkArray G (Frozen A x F)) (B : Coarse) := Rows.direct T x (V B) k W A F q d Y
  (PhysicalAffineScalarComparison.stationary T x (V B) k W A F q d Y)

def offsetAction (Y : LinkArray G (Frozen A x F)) (B : Coarse) := remaining (Dc B) *ᵥ sourceGap T x k F q d Y B

def leftAction (B : Coarse) := ((columnGap T x k F B)*(Qc B)⁻¹*(Dc B).transpose) *ᵥ fu B

def covarianceAction (B : Coarse) := (Du B*((Qc B)⁻¹-(Qu B)⁻¹)*(Dc B).transpose) *ᵥ fu B

def rightAction (B : Coarse) := (Du B*(Qu B)⁻¹*(columnGap T x k F B).transpose) *ᵥ fu B

def displacement (Y : LinkArray G (Frozen A x F)) (B : Coarse) := offsetAction T x k F q d Y B -
  leftAction T x k F B - covarianceAction T x k F B - rightAction T x k F B

/-- Four physical terms compare the full vector of *actual* stationary
residuals. This identity is algebraic, even before a positivity assumption. -/
theorem original (Y : LinkArray G (Frozen A x F)) (B : Coarse) :
    cutResidual T x k F q d Y B - ru B = displacement T x k F q d Y B := by
  have hc : cutResidual T x k F q d Y B = remaining (Dc B) *ᵥ fc Y B :=
    PhysicalAffineScalarUncut.residual_projection (Dc B) (fc Y B)
  rw [hc,PhysicalAffineScalarUncut.projected_residual]
  exact telescope (Dc B) (Du B) (fc Y B) (fu B)

/-- No small inverse-difference hypothesis enters this sharper expression:
all offending factors are the actual removed source or removed columns. -/
def forcingGap (Y : LinkArray G (Frozen A x F)) (B : Coarse) := sourceGap T x k F q d Y B +
  columnGap T x k F B *ᵥ PhysicalAffineScalarUncut.center T x k F B

def perturbation (Y : LinkArray G (Frozen A x F)) (B : Coarse) :=
  remaining (Dc B) *ᵥ forcingGap T x k F q d Y B -
    Dc B *ᵥ ((Qc B)⁻¹ *ᵥ ((columnGap T x k F B).transpose *ᵥ ru B))

theorem reduced (Y : LinkArray G (Frozen A x F)) (B : Coarse) (hC : (Qc B).PosDef) (hU : (Qu B).PosDef) :
    displacement T x k F q d Y B = perturbation T x k F q d Y B := by
  rw [←original]
  have hc : cutResidual T x k F q d Y B = remaining (Dc B) *ᵥ fc Y B :=
    PhysicalAffineScalarUncut.residual_projection (Dc B) (fc Y B)
  rw [hc]
  exact perturb (Dc B) (Du B) (fc Y B) (fu B) hC hU

theorem inverse_gap (B : Coarse) (hC : (Qc B).PosDef) (hU : (Qu B).PosDef) :
    (Qc B)⁻¹ - (Qu B)⁻¹ = -((Qc B)⁻¹ * ((columnGap T x k F B).transpose * Dc B +
      (Du B).transpose * columnGap T x k F B) * (Qu B)⁻¹) := by
  have hg : Qc B - Qu B = (columnGap T x k F B).transpose * Dc B + (Du B).transpose * columnGap T x k F B := by
    unfold Rows.gram PhysicalAffineScalarUncut.gram columnGap
    rw [Matrix.transpose_sub,Matrix.sub_mul,Matrix.mul_sub]
    abel
  rw [←hg,Matrix.mul_sub,Matrix.sub_mul,Matrix.nonsing_inv_mul _ (IsUnit.mk0 _ hC.det_pos.ne'),
    Matrix.one_mul,Matrix.mul_assoc,Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ hU.det_pos.ne'),Matrix.mul_one]
  abel

def halfLog (o : Site c) (H₀ H : Gaussian.Table keys) : ℝ :=
  ∑ j : keys, if S.ratio.parent j.1.val.val.1=o then (AnalyticBridge.RelativeLogdet.logKernel H₀ j j-
    AnalyticBridge.RelativeLogdet.logKernel H j j)/2 else 0

def logGap (o : Site c) (B : Coarse) := halfLog (x:=x) (F:=F) o (Qc 0) (Qc B) -
  halfLog (x:=x) (F:=F) o (Qu 0) (Qu B)

def squareGap (Y : LinkArray G (Frozen A x F)) (g : ℝ) (o : Site c) (B : Coarse) : ℝ :=
  ∑ i : Rows.Receipt G S, if PhysicalAffineScalarComparison.rowRoot S i=o then
    -(displacement T x k F q d Y B i * (cutResidual T x k F q d Y B i + ru B i))/(2*g^2) else 0

/-- The real stored root, carrying both its original diagonal logarithm and
actual stationary square, compared to the independent uncut-root calculation. -/
theorem root (Y : LinkArray G (Frozen A x F)) (g : ℝ) (o : Site c) (B : Coarse) :
    PhysicalAffineScalarJets.actualRoot T x k A F q d Y g o B - PhysicalAffineScalarUncut.scalarAt T x k F g o B =
      logGap T x k F o B + squareGap T x k F q d Y g o B := by
  let P (r : Prices G (Slots S)) := ∑ i : Rows.Receipt G S,
    if PhysicalAffineScalarComparison.rowRoot S i=o then -(r i)^2/(2*g^2) else 0
  have hp : P (cutResidual T x k F q d Y B) - P (ru B) = squareGap T x k F q d Y g o B := by
    unfold P squareGap
    rw [←Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : PhysicalAffineScalarComparison.rowRoot S i=o
    · simp only [h,if_true]
      have hh := congrFun (original T x k F q d Y B) i
      change cutResidual T x k F q d Y B i - ru B i = displacement T x k F q d Y B i at hh
      rw [←hh]
      ring
    · simp only [h,if_false,sub_self]
  change (halfLog (x:=x) (F:=F) o (Qc 0) (Qc B) + P (cutResidual T x k F q d Y B)) -
    (halfLog (x:=x) (F:=F) o (Qu 0) (Qu B) + P (ru B)) = _
  rw [←hp,logGap]
  ring

theorem mixed (Y : LinkArray G (Frozen A x F)) (g : ℝ) (o : Site c) (B : Coarse) (j : ℕ) (v : Fin j → Coarse) :
    iteratedFDeriv ℝ j (fun b : Coarse => PhysicalAffineScalarJets.actualRoot T x k A F q d Y g o b -
      PhysicalAffineScalarUncut.scalarAt T x k F g o b) B v =
    iteratedFDeriv ℝ j (fun b : Coarse => logGap T x k F o b + squareGap T x k F q d Y g o b) B v := by
  rw [funext (root T x k F q d Y g o)]

/-- The actual marked-tree switch can change the active coordinate space.
The compared one-tag scalar is on a common signed row root for both draws. -/
theorem one_tree (tag : Site c) (F' : {U : Forest S.ratio // FreeResolvent.Affine.changed S F U tag})
    (Y : LinkArray G (Frozen A x F)) (Y' : LinkArray G (Frozen A x F'.val)) (g : ℝ) (o : Site c) (B : Coarse) :
    (PhysicalAffineScalarJets.actualRoot T x k A F'.val q d Y' g o B - PhysicalAffineScalarJets.actualRoot T x k A F q d Y g o B) -
      (PhysicalAffineScalarUncut.scalarAt T x k F'.val g o B - PhysicalAffineScalarUncut.scalarAt T x k F g o B) =
    (logGap T x k F'.val o B - logGap T x k F o B) +
      (squareGap T x k F'.val q d Y' g o B - squareGap T x k F q d Y g o B) := by
  linarith only [root T x k F'.val q d Y' g o B,root T x k F q d Y g o B]

theorem changed_jet (tag : Site c) (F' : {U : Forest S.ratio // FreeResolvent.Affine.changed S F U tag})
    (Y : LinkArray G (Frozen A x F)) (Y' : LinkArray G (Frozen A x F'.val)) (g : ℝ) (o : Site c)
    (B : Coarse) (j : ℕ) (v : Fin j → Coarse) :
    iteratedFDeriv ℝ j (fun t : Coarse =>
      (PhysicalAffineScalarJets.actualRoot T x k A F'.val q d Y' g o t - PhysicalAffineScalarJets.actualRoot T x k A F q d Y g o t) -
        (PhysicalAffineScalarUncut.scalarAt T x k F'.val g o t - PhysicalAffineScalarUncut.scalarAt T x k F g o t)) B v =
    iteratedFDeriv ℝ j (fun t : Coarse => (logGap T x k F'.val o t - logGap T x k F o t) +
      (squareGap T x k F'.val q d Y' g o t - squareGap T x k F q d Y g o t)) B v := by
  rw [funext (one_tree T x k F q d tag F' Y Y' g o)]

end YM.Integration.PhysicalAffineScalarCutResidual
