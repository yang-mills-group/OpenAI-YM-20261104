import YM.Integration.PhysicalAffineScalarCutResidual
import YM.Integration.PhysicalAffineScalarMetric
import YM.Integration.ConditionalAffineActiveInverse
import YM.Integration.ConditionalAffineForcing

/-! Original inputs to the no-hole residual perturbation. The physical row
mask and frozen input both disappear. The remaining changed forcing is the
actual transported path tail, and every changed affine column is a genuinely
priced signed Jacobian entry. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarCutInputs
open Function Filter Matrix Lattice Wilson RG RG.Shoot Precision Exterior Tree
open Pressure Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD
open PhysicalNext.Repeat.Greenbelt ConditionalTreeCovarianceJets
open PhysicalAffineScalarAperture (noHole)
open PhysicalAffineScalarCutResidual
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S) (x : ℝ) (k : S.Choices)
    (F : Forest S.ratio) (q : Chi) (d : ℝ) {σ K Λ : ℝ}
local notation "A" => noHole S
local notation "W" => shots S x
local notation "Coarse" => Gaussian.Vec (Raw G c)
local notation "V" => fun B : Coarse => represent (decode B)
local notation "short" => shorter (till x)
local notation "keys" => Rows.In (G:=G) x A F
local notation "addr" => address (G:=G) A F x
local notation "Qc" => fun B : Coarse => Rows.gram T x (V B) k W A F
local notation "Qu" => PhysicalAffineScalarUncut.gram T x k F

/-- All base-row guards are actually discharged on this one no-hole forest,
for every selector, every signed channel and every background. -/
theorem guard (B : Coarse) : sourceGuard T x k F B = 0 :=
  source_guard_zero T x k F B (ConditionalNoHoleRows.kept F x)

theorem source (Y : LinkArray G (Frozen A x F)) (B : Coarse) (hT : T.up.Bounds T.high σ K Λ) (i : Slots S) :
    tape (sourceGap T x k F q d Y B) i = -(slip • ConditionalAffineSourceSplit.difference T x B i) := by
  rw [source_parts T x k F q d Y B hT,guard,zero_add,source_read,
    ←ConditionalAffineSourceSplit.original T x k B i]
  abel

/-- Both physically stored Grams have the independently supplied true active
inverse at their own path selection on the same raw-field neighbourhood. -/
theorem covariance (_Y : LinkArray G (Frozen A x F)) (h : S.patch.Branches S.kernel G)
    (hT : T.up.Bounds T.high σ K Λ) :
    (fun B : Coarse => (Qc B)⁻¹ - (Qu B)⁻¹) =ᶠ[𝓝 0] fun B : Coarse =>
      ((primary S F k T.high T.up short B)⁻¹ - (primary S F k T.high T.up all B)⁻¹).submatrix
        (live (G:=G) A F x) (live A F x) := by
  let e : keys ≃ Precision.Key F G := (Native.lineEquiv F x).symm
  filter_upwards [affine_near A F x T k h hT] with B hB
  change (Rows.gram T x (V B) k W A F)⁻¹ - (Qu B)⁻¹ = _
  rw [hB,PhysicalAffineScalarMetric.uncut]
  change ((primary S F k T.high T.up short B).submatrix e e)⁻¹ -
    ((primary S F k T.high T.up all B).submatrix e e)⁻¹ = _
  rw [Matrix.inv_submatrix_equiv,Matrix.inv_submatrix_equiv]
  rfl

/-- The sole retained matrix error is the actual transported Jacobian tail,
restricted to the genuine active column addresses of the chosen tree. -/
theorem columns (h : S.patch.Branches S.kernel G) (hT : T.up.Bounds T.high σ K Λ) :
    (fun B : Coarse => columnGap T x k F B) =ᶠ[𝓝 0] fun B : Coarse =>
      (ConditionalAffineForcing.rawRows T k short B - ConditionalAffineForcing.rawRows T k all B).submatrix id addr := by
  filter_upwards [near_whole k h] with B hB
  have hh (z : LogArray G (Slots S)) : Rows.restrict x W A F z = slip • z := ConditionalNoHoleRows.all F x z
  have hc : Rows.move T x (V B) k W A F = (ConditionalAffineForcing.rawRows T k short B).submatrix id addr := by
    ext i j
    change tape.symm (Rows.restrict x W A F (Rows.bump T x (V B) k (Rows.fresh x W A F (axisPrice j)))) i = _
    rw [hh,PhysicalAffineScalarJets.slope_eq T x k h hT B hB,axisPrice,←relative_input A F x,
      ContinuousLinearEquiv.symm_apply_apply,ConditionalAffineForcing.insertion_single]
    rfl
  change Rows.move T x (V B) k W A F - PhysicalAffineScalarUncut.columns T x k F B = _
  rw [hc,ConditionalAffineForcing.original_column T k F x B]
  rfl

theorem transported (h : S.patch.Branches S.kernel G) (hT : T.up.Bounds T.high σ K Λ)
    (s : Signed) (i : tile G f) (j : keys) :
    (fun B : Coarse => -columnGap T x k F B (ConditionalAffineRowDifference.row (S:=S) s i) j) =ᶠ[𝓝 0]
    fun B : Coarse => ConditionalAffineRowDifference.difference T k s (till x) B i (addr j) := by
  filter_upwards [columns T x k F h hT] with B hB
  rw [hB]
  exact neg_sub (ConditionalAffineForcing.rawRows T k short B (ConditionalAffineRowDifference.row (S:=S) s i) (addr j))
    (ConditionalAffineForcing.rawRows T k all B (ConditionalAffineRowDifference.row (S:=S) s i) (addr j))

/-- Genuine charged entry of the physical column in the stationary
perturbation, for independently chosen coarse field bonds and colors. -/
theorem transported_price (h : S.patch.Branches S.kernel G) (hT : T.up.Bounds T.high σ K Λ)
    (s : Signed) (i : tile G f) (j : keys) (n : ℕ) {a t δ : ℝ} (hc : 1<c.val) (ht : 0<t) (ha : 0≤a)
    (hp : Sheet T.up t a) (hd : 0≤δ) (he : δ≤tier t n) (l : List (raw G c)) (hl : l.length≤n) :
    (marks G c δ).pay l (named S s i) * ((native c).weight (wider t n) (named S s i) (home S (addr j)) *
     |jet (ray G c) (fun B : Coarse => -columnGap T x k F B (ConditionalAffineRowDifference.row (S:=S) s i) j) l 0|) ≤
      |slip| * (Real.exp (-(t/4)*(till x))*phasePrice G S.patch S.kernel n a t) := by
  have H := ConditionalAffineRowDifference.price T k s (till x) n hc ht ha hp hd he
  have hx := (transported T x k F h hT s i j).iteratedFDeriv (𝕜:=ℝ) l.length
  change _ * (_ * |iteratedFDeriv ℝ l.length _ 0 (ray G c ∘ l.get)|) ≤ _
  rw [hx.self_of_nhds]
  change _ * (_ * |jet (ray G c) (fun B : Coarse => ConditionalAffineRowDifference.difference T k s (till x) B i (addr j)) l 0|) ≤ _
  rw [FreeResolvent.TestD.entry (ray G c) l (H.smooth.of_le (by exact_mod_cast hl))]
  exact ((H.bound l hl).row.entry i (addr j))

end YM.Integration.PhysicalAffineScalarCutInputs
end

/-! Dual root weights for the genuine no-hole scalar error. Both actual
draws share the raw removed forcing and columns, with the one-tree change
carried entirely by computed Gaussian weights. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarCutWeights
open Function Filter Matrix Lattice Wilson RG RG.Shoot Precision Exterior Tree
open Pressure Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD
open PhysicalNext.Repeat.Greenbelt ConditionalTreeCovarianceJets PhysicalAffineScalarCutResidual
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

section algebra
variable {α ι κ : Type} [Fintype α] [Fintype ι] [Fintype κ]

private theorem row_identity (P : Gaussian.Table α) (D J : Matrix α ι ℝ) (f r : Gaussian.Vec α)
    (a : Gaussian.Vec ι) (i : α) :
    (P *ᵥ (f+J *ᵥ a) - D *ᵥ (J.transpose *ᵥ r)) i =
      (∑ z : α, P i z * f z) + ∑ z : α, ∑ j : ι, (P i z*a j-D i j*r z)*J z j := by
  have hp : (P *ᵥ (J *ᵥ a)) i = ∑ z : α, ∑ j : ι, (P i z*a j)*J z j := by
    change (∑ z, P i z*(∑ j, J z j*a j)) = _
    simp only [Finset.mul_sum,mul_comm,mul_left_comm]
  have hd : (D *ᵥ (J.transpose *ᵥ r)) i = ∑ z : α, ∑ j : ι, (D i j*r z)*J z j := by
    change (∑ j, D i j*(∑ z, J z j*r z)) = _
    rw [Finset.sum_comm (f:=fun z j => D i j*r z*J z j)]
    simp only [Finset.mul_sum,mul_comm,mul_left_comm]
  rw [Pi.sub_apply,Matrix.mulVec_add,Pi.add_apply,hp,hd]
  simp only [sub_mul,Finset.sum_sub_distrib,Matrix.mulVec,dotProduct]
  ring

omit [Fintype α] in
private theorem collect (s : Finset α) (w : α → ℝ) (M : α → κ → ℝ) (N : α → κ → ι → ℝ)
    (f : κ → ℝ) (A : κ → ι → ℝ) :
    (∑ i ∈ s, w i*((∑ r : κ, M i r*f r) + ∑ r : κ, ∑ j : ι, N i r j*A r j)) =
    (∑ r : κ, f r*(∑ i ∈ s, w i*M i r)) + ∑ r : κ, ∑ j : ι, A r j*(∑ i ∈ s, w i*N i r j) := by
  simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    simp only [mul_comm,mul_left_comm]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_comm]
    simp only [mul_comm,mul_left_comm]

private theorem deposit [DecidableEq κ] (e : ι → κ) (T : κ → ℝ) (W : ι → ℝ) :
    (∑ j : κ, T j*(∑ a : ι, if e a=j then W a else 0)) = ∑ a : ι, T (e a)*W a := by
  classical
  simp only [Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
end algebra

variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S) (x : ℝ) (k : S.Choices)
    (F : Forest S.ratio) (q : Chi) (d : ℝ) {σ K Λ : ℝ}
local notation "A" => noHole S
local notation "W" => shots S x
local notation "Coarse" => Gaussian.Vec (Raw G c)
local notation "V" => fun B : Coarse => represent (decode B)
local notation "keys" => Rows.In (G:=G) x A F
local notation "rows" => Rows.Receipt G S
local notation "rawKey" => Raw G f
local notation "addr" => address (G:=G) A F x
local notation "Dc" => fun B : Coarse => Rows.move T x (V B) k W A F
local notation "Qc" => fun B : Coarse => Rows.gram T x (V B) k W A F
local notation "Qu" => PhysicalAffineScalarUncut.gram T x k F
local notation "P" => fun B : Coarse => PhysicalAffineScalarUncut.remaining (Dc B)
local notation "m" => PhysicalAffineScalarUncut.center T x k F
local notation "r₀" => PhysicalAffineScalarUncut.sourceResidual T x k F

def held (o : Site c) : Finset rows := Finset.univ.filter fun i => PhysicalAffineScalarComparison.rowRoot S i=o
def multiplier (Y : LinkArray G (Frozen A x F)) (g : ℝ) (i : rows) (B : Coarse) :=
  -(cutResidual T x k F q d Y B i+r₀ B i)/(2*g^2)

/-- Each signed root row sees its own actual stationary residual sum. -/
def rowWeight (Y : LinkArray G (Frozen A x F)) (g : ℝ) (o : Site c) (z : rows) (B : Coarse) : ℝ :=
  ∑ i ∈ held (G:=G) (S:=S) o, multiplier T x k F q d Y g i B * P B i z

def liveWeight (Y : LinkArray G (Frozen A x F)) (g : ℝ) (o : Site c) (z : rows) (j : keys) (B : Coarse) : ℝ :=
  ∑ i ∈ held (G:=G) (S:=S) o, multiplier T x k F q d Y g i B *
    (P B i z * m B j - (Dc B*(Qc B)⁻¹) i j*r₀ B z)

/-- Zero extension from the genuinely active keys onto the same raw input
space for every actual tree draw. -/
def columnWeight (Y : LinkArray G (Frozen A x F)) (g : ℝ) (o : Site c) (z : rows) (j : rawKey) (B : Coarse) : ℝ :=
  ∑ a : keys, if addr a=j then liveWeight T x k F q d Y g o z a B else 0

/-- The source and Jacobian cutoff errors are independent of the tree on
this no-hole stage. The total rooted scalar price is linear in them. -/
def sourceTail (B : Coarse) : Gaussian.Vec rows := tape.symm fun i => -(slip • ConditionalAffineSourceSplit.difference T x B i)

def columnTail (B : Coarse) : Matrix rows rawKey ℝ := ConditionalAffineForcing.rawRows T k (shorter (till x)) B -
  ConditionalAffineForcing.rawRows T k all B

private theorem stationary_sum (Y : LinkArray G (Frozen A x F)) (g : ℝ) (o : Site c) (B : Coarse)
    (hC : (Qc B).PosDef) (hU : (Qu B).PosDef) :
    squareGap T x k F q d Y g o B = (∑ z : rows, sourceGap T x k F q d Y B z*rowWeight T x k F q d Y g o z B) +
      ∑ z : rows, ∑ j : keys, columnGap T x k F B z j*liveWeight T x k F q d Y g o z j B := by
  let I := held (G:=G) (S:=S) o
  let u := multiplier T x k F q d Y g
  let J := columnGap T x k F B
  let f₀ := sourceGap T x k F q d Y B
  let H := Dc B*(Qc B)⁻¹
  have hh : squareGap T x k F q d Y g o B = ∑ i ∈ I, u i B * perturbation T x k F q d Y B i := by
    unfold squareGap I held
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : PhysicalAffineScalarComparison.rowRoot S i=o
    · simp only [hi,if_true,u,multiplier,reduced T x k F q d Y B hC hU]
      ring
    · simp only [hi,if_false]
  have hp (i : rows) : perturbation T x k F q d Y B i =
      (∑ z : rows, P B i z*f₀ z) + ∑ z : rows, ∑ j : keys, (P B i z*m B j-H i j*r₀ B z)*J z j := by
    unfold perturbation forcingGap
    rw [Matrix.mulVec_mulVec (J.transpose *ᵥ r₀ B) (Dc B) (Qc B)⁻¹]
    exact row_identity (P B) H J f₀ (r₀ B) (m B) i
  rw [hh]
  simp_rw [hp]
  exact collect I (fun i => u i B) (P B) (fun i z j => P B i z*m B j-H i j*r₀ B z) f₀ J

set_option maxHeartbeats 1800000 in
/-- A complete scalar on a common original coarse-field neighbourhood. Only
actual positive Gram germs are used in the stationary normal equations. -/
theorem original (Y : LinkArray G (Frozen A x F)) (g : ℝ) (o : Site c)
    (h : S.patch.Branches S.kernel G) (hT : T.up.Bounds T.high σ K Λ)
    (hpos : ∀ᶠ B : Coarse in 𝓝 0, (Qc B).PosDef ∧ (Qu B).PosDef) :
    squareGap T x k F q d Y g o =ᶠ[𝓝 0] fun B : Coarse =>
    (∑ z : rows, sourceTail T x B z*rowWeight T x k F q d Y g o z B) +
      ∑ z : rows, ∑ j : rawKey, columnTail T x k B z j*columnWeight T x k F q d Y g o z j B := by
  filter_upwards [PhysicalAffineScalarCutInputs.columns T x k F h hT,hpos] with B hJ hB
  have hs : sourceGap T x k F q d Y B = sourceTail T x B := by
    apply (tape (G:=G) (ι:=Slots S)).injective
    funext i
    rw [sourceTail,MeasurableEquiv.apply_symm_apply]
    exact PhysicalAffineScalarCutInputs.source T x k F q d Y B hT i
  rw [stationary_sum T x k F q d Y g o B hB.1 hB.2,hs,hJ]
  apply congrArg₂ (·+·) rfl
  apply Finset.sum_congr rfl
  intro z _
  change (∑ a : keys, columnTail T x k B z (addr a)*liveWeight T x k F q d Y g o z a B) =
    ∑ j : rawKey, columnTail T x k B z j*(∑ a : keys, if addr a=j then liveWeight T x k F q d Y g o z a B else 0)
  exact (deposit addr (fun j => columnTail T x k B z j) (fun a => liveWeight T x k F q d Y g o z a B)).symm

theorem one_tree (tag : Site c) (F' : {U : Forest S.ratio // changed S F U tag})
    (Y : LinkArray G (Frozen A x F)) (Y' : LinkArray G (Frozen A x F'.val)) (g : ℝ) (o : Site c)
    (h : S.patch.Branches S.kernel G) (hT : T.up.Bounds T.high σ K Λ)
    (hpos : ∀ Z ∈ ({F,F'.val}:Finset (Forest S.ratio)), ∀ᶠ B : Coarse in 𝓝 0,
      (Rows.gram T x (V B) k W A Z).PosDef ∧ (PhysicalAffineScalarUncut.gram T x k Z B).PosDef) :
    (fun B : Coarse => squareGap T x k F'.val q d Y' g o B - squareGap T x k F q d Y g o B) =ᶠ[𝓝 0]
    fun B : Coarse => (∑ z : rows, sourceTail T x B z*(rowWeight T x k F'.val q d Y' g o z B -
      rowWeight T x k F q d Y g o z B)) + ∑ z : rows, ∑ j : rawKey, columnTail T x k B z j *
      (columnWeight T x k F'.val q d Y' g o z j B - columnWeight T x k F q d Y g o z j B) := by
  filter_upwards [original T x k F'.val q d Y' g o h hT (hpos F'.val (by simp)),
    original T x k F q d Y g o h hT (hpos F (by simp))] with B h' h₀
  rw [h',h₀]
  simp only [mul_sub,Finset.sum_sub_distrib]
  abel

end YM.Integration.PhysicalAffineScalarCutWeights
end

/-! The computed ordinary weights of both actual drawn forests are functions
only of two true zero-extended Gaussian covariances on common fine-link keys. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarGaussianWeights
open Function Filter Matrix Lattice Wilson RG RG.Shoot Precision Exterior Tree
open Pressure Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD
open PhysicalNext.Repeat.Greenbelt ConditionalTreeCovarianceJets PhysicalAffineScalarCutResidual PhysicalAffineScalarCutWeights
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

section algebra
variable {α β ι : Type} [Fintype α] [Fintype β] [Fintype ι] [DecidableEq α] [DecidableEq β]

def project (J : Matrix α β ℝ) (C : Gaussian.Table β) := (1:Gaussian.Table α)-J*C*J.transpose

def forceCenter (J : Matrix α β ℝ) (C : Gaussian.Table β) (f : Gaussian.Vec α) := -(C *ᵥ (J.transpose *ᵥ f))

omit [DecidableEq β] in
private theorem project_extension [DecidableEq ι] (D : Matrix α ι ℝ) (J : Matrix α β ℝ) (E : Matrix β ι ℝ)
    (Q : Gaussian.Table ι) (C : Gaussian.Table β) (hd : D=J*E) (hq : D.transpose*D=Q)
    (hc : E*Q⁻¹*E.transpose=C) :
    PhysicalAffineScalarUncut.remaining D=project J C := by
  have hmul : D*(D.transpose*D)⁻¹*D.transpose=J*C*J.transpose := by
    rw [hq]
    calc D*Q⁻¹*D.transpose = (J*E)*Q⁻¹*(J*E).transpose := congrArg (fun X : Matrix α ι ℝ => X*Q⁻¹*X.transpose) hd
         _ = J*(E*Q⁻¹*E.transpose)*J.transpose := by simp only [Matrix.transpose_mul,Matrix.mul_assoc]
         _ = _ := congrArg (fun M : Gaussian.Table β => J*M*J.transpose) hc
  ext i j
  simp only [PhysicalAffineScalarUncut.remaining,project,Matrix.sub_apply]
  apply congrArg₂ (fun (a₁ a₂ : ℝ) => a₁-a₂)
  · by_cases hij : i=j <;> simp [Matrix.one_apply,hij]
  · exact congrFun (congrFun hmul i) j

omit [DecidableEq α] [DecidableEq β] in
private theorem center_extension (J : Matrix α β ℝ) (E : Matrix β ι ℝ) (C : Gaussian.Table ι) (f : Gaussian.Vec α) :
    E *ᵥ (-(C *ᵥ ((J*E).transpose *ᵥ f))) = forceCenter J (E*C*E.transpose) f := by
  simp only [forceCenter,Matrix.mulVec_neg,Matrix.transpose_mul,Matrix.mulVec_mulVec,Matrix.mul_assoc]

omit [Fintype α] [Fintype β] [DecidableEq α] in
private theorem weight_extension (e : ι → β) (s : Finset α) (a p : α → ℝ) (L : Matrix α ι ℝ)
    (m : Gaussian.Vec ι) (v : ℝ) (j : β) :
    (∑ z : ι, if e z=j then ∑ i ∈ s, a i*(p i*m z -L i z*v) else 0) =
      ∑ i ∈ s, a i*(p i*(insertion e *ᵥ m) j -(L*(insertion e).transpose) i j*v) := by
  let E := insertion e
  have hh (z : ι) : (if e z=j then ∑ i ∈ s, a i*(p i*m z-L i z*v) else 0) =
      ∑ i ∈ s, a i*(p i*(E j z*m z) - (L i z*E j z)*v) := by
    by_cases hz : e z=j <;> simp [E,insertion,hz]
  simp_rw [hh]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ z : ι, a i*(p i*(E j z*m z)-(L i z*E j z)*v)) =
    a i*(p i*(∑ z : ι, E j z*m z)-(∑ z : ι, L i z*E j z)*v)
  simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum,Finset.sum_mul]
end algebra

variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S) (x : ℝ) (k : S.Choices)
    (F : Forest S.ratio) (q : Chi) (d : ℝ) {σ K Λ : ℝ}
local notation "A" => noHole S
local notation "W" => shots S x
local notation "Coarse" => Gaussian.Vec (Raw G c)
local notation "V" => fun B : Coarse => represent (decode B)
local notation "rawKey" => Raw G f
local notation "keys" => Rows.In (G:=G) x A F
local notation "rows" => Rows.Receipt G S
local notation "addr" => address (G:=G) A F x
local notation "I" => insertion addr
local notation "short" => shorter (till x)
local notation "D" => fun B : Coarse => Rows.move T x (V B) k W A F
local notation "U" => PhysicalAffineScalarUncut.columns T x k F
local notation "Qc" => fun B : Coarse => Rows.gram T x (V B) k W A F
local notation "Qu" => PhysicalAffineScalarUncut.gram T x k F
local notation "J" => ConditionalAffineForcing.rawRows T k short
local notation "L" => ConditionalAffineForcing.rawRows T k all
local notation "u" => PhysicalAffineScalarUncut.offset T k
local notation "v" => shortSource T x k
local notation "z₀" => PhysicalAffineScalarUncut.sourceResidual T x k F

/-- Independent observed Gaussian, with exactly zero entries on actual
pinned coordinates of this physical forest. -/
def covariance (r : Admit) (B : Coarse) := ConditionalAffineActiveInverse.deposit (freeTo G S F)
  (primary S F k T.high T.up r B)⁻¹

theorem spectral (r : Admit) (B : Coarse) (h : IsUnit (primary S F k T.high T.up r B).det) :
    covariance T k F r B = action (whole S F k T.high T.up r) 0 B - Shell.off (freeTo G S F) :=
  ConditionalAffineActiveInverse.admitted S F k T.high T.up r B h

set_option maxHeartbeats 1800000 in
/-- Covariance is deposited after selecting the correct same-R Gram on its
own active keys, before multiplication by a common raw response. -/
theorem deposited (h : S.patch.Branches S.kernel G) (hT : T.up.Bounds T.high σ K Λ) :
    ∀ᶠ B : Coarse in 𝓝 0, I*(Qc B)⁻¹*(I).transpose = covariance T k F short B ∧
      I*(Qu B)⁻¹*(I).transpose = covariance T k F all B := by
  let e : keys ≃ Precision.Key F G := (Native.lineEquiv F x).symm
  let J₀ := insertion (FreeResolvent.plant F (G:=G))
  have he : I=J₀.submatrix id e := by ext i j; rfl
  filter_upwards [affine_near A F x T k h hT] with B hB
  have use (r : Admit) (H : Gaussian.Table keys)
      (hp : H=(primary S F k T.high T.up r B).submatrix e e) : I*H⁻¹*(I).transpose = covariance T k F r B := by
    rw [hp,he,Matrix.inv_submatrix_equiv]
    exact PhysicalAffineScalarFullCovariance.reindex_extension e J₀ _
  exact ⟨use short (Qc B) hB,use all (Qu B) (PhysicalAffineScalarMetric.uncut T x k F B)⟩

def rawRow (g : ℝ) (o : Site c) (i : rows) (B : Coarse) (C H : Gaussian.Table rawKey) : ℝ :=
  let P := project (J B) C
  let R := project (L B) H
  ∑ z ∈ held (G:=G) (S:=S) o, -((P *ᵥ v B) z+(R *ᵥ u B) z)/(2*g^2)*P z i

def rawColumn (g : ℝ) (o : Site c) (i : rows) (j : rawKey) (B : Coarse) (C H : Gaussian.Table rawKey) : ℝ :=
  let P := project (J B) C
  let R := project (L B) H
  let m := forceCenter (L B) H (u B)
  ∑ z ∈ held (G:=G) (S:=S) o, -((P *ᵥ v B) z+(R *ᵥ u B) z)/(2*g^2) *
    (P z i*m j - (J B*C) z j*(R *ᵥ u B) i)

/-- The true affine matrices and ordinary stored source before either active
Gaussian is applied. Both raw loads are genuinely independent of the forest. -/
theorem response (Y : LinkArray G (Frozen A x F)) (h : S.patch.Branches S.kernel G)
    (hT : T.up.Bounds T.high σ K Λ) : ∀ᶠ B : Coarse in 𝓝 0,
    D B=J B*I ∧ U B=L B*I ∧ Rows.source T x (V B) k W A F q d Y=v B := by
  filter_upwards [PhysicalAffineScalarCutInputs.columns T x k F h hT] with B hcol
  have hu : U B=L B*I := (ConditionalAffineForcing.original_column T k F x B).trans (insertion.mul addr (L B)).symm
  have hd : D B-U B=(J B-L B)*I := hcol.trans (insertion.mul addr (J B-L B)).symm
  rw [hu,Matrix.sub_mul] at hd
  exact ⟨by simpa only [sub_add_cancel] using congrArg (fun a => a+L B*I) hd,hu,
    (frozen_zero T x k F q d Y B hT).trans (congrArg tape.symm (ConditionalNoHoleRows.all F x (Rows.base T x (V B) k)))⟩

/-- The actually stored affine forcing and the independently prescribed full
forcing restrict the same pre-projection raw coordinate expressions as their
own physical forest requires. -/
theorem loads (Y : LinkArray G (Frozen A x F)) (h : S.patch.Branches S.kernel G)
    (hT : T.up.Bounds T.high σ K Λ) : ∀ᶠ B : Coarse in 𝓝 0,
    Rows.blame T x (V B) k W A F q d Y=(I).transpose *ᵥ ((J B).transpose *ᵥ v B) ∧
    (U B).transpose *ᵥ u B = (I).transpose *ᵥ ((L B).transpose *ᵥ u B) := by
  filter_upwards [response T x k F q d Y h hT] with B ⟨hd,hu,hsrc⟩
  constructor
  · simp only [Rows.blame,hd,hsrc,Matrix.transpose_mul,Matrix.mulVec_mulVec]
  · simp only [hu,Matrix.transpose_mul,Matrix.mulVec_mulVec]

set_option maxHeartbeats 1800000 in
/-- Every variable depending on a tree in these true weights has passed
through its independent, observed raw Gaussian. -/
theorem original (Y : LinkArray G (Frozen A x F)) (g : ℝ) (o : Site c)
    (h : S.patch.Branches S.kernel G) (hT : T.up.Bounds T.high σ K Λ) :
    ∀ᶠ B : Coarse in 𝓝 0, (∀ i : rows, rowWeight T x k F q d Y g o i B = rawRow T x k g o i B
      (covariance T k F short B) (covariance T k F all B)) ∧
      ∀ (i : rows) (j : rawKey), columnWeight T x k F q d Y g o i j B = rawColumn T x k g o i j B
        (covariance T k F short B) (covariance T k F all B) := by
  filter_upwards [deposited T x k F h hT,response T x k F q d Y h hT] with B hcov ⟨hd,hu,hsrc⟩
  let C := covariance T k F short B
  let H := covariance T k F all B
  have hc : PhysicalAffineScalarUncut.remaining (D B) = project (J B) C :=
    project_extension (D B) (J B) I (Qc B) C hd rfl hcov.1
  have hU : PhysicalAffineScalarUncut.remaining (U B) = project (L B) H :=
    project_extension (U B) (L B) I (Qu B) H hu rfl hcov.2
  have hrc : cutResidual T x k F q d Y B = project (J B) C *ᵥ v B := by
    rw [←hc,←hsrc]
    exact PhysicalAffineScalarUncut.residual_projection _ _
  have hru : z₀ B = project (L B) H *ᵥ u B := by
    rw [PhysicalAffineScalarUncut.projected_residual,PhysicalAffineScalarUncut.projected,hU]
  have hm : I *ᵥ PhysicalAffineScalarUncut.center T x k F B = forceCenter (L B) H (u B) := by
    change I *ᵥ (-((Qu B)⁻¹ *ᵥ ((U B).transpose *ᵥ u B))) = _
    rw [hu,←show I*(Qu B)⁻¹*(I).transpose=H from hcov.2,center_extension]
  have hL : D B*(Qc B)⁻¹*(I).transpose = J B*C := by
    calc D B*(Qc B)⁻¹*(I).transpose = (J B*I)*(Qc B)⁻¹*(I).transpose :=
            congrArg (fun M : Matrix rows keys ℝ => M*(Qc B)⁻¹*(I).transpose) hd
         _ = J B*(I*(Qc B)⁻¹*(I).transpose) := by simp only [Matrix.mul_assoc]
         _ = _ := congrArg (fun M : Gaussian.Table rawKey => J B*M) hcov.1
  refine ⟨fun i => ?_,fun i j => ?_⟩
  · simp only [rowWeight,multiplier,rawRow,hrc,hru,hc,C,H]
  · unfold columnWeight liveWeight
    rw [weight_extension]
    simp only [multiplier,rawColumn,hrc,hru,hc,hm,hL,C,H]

end YM.Integration.PhysicalAffineScalarGaussianWeights
end
