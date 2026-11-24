import YM.Integration.PhysicalAffineScalarUncut

/-! The original fully uncut signed-row Gram equals the independent
no-hole tree Hessian in the active coordinates of the physical chart.
Both coordinates of each twin plaquette and the genuine noise derivative
are included before squaring and averaging orientations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarMetric

open Function Lattice Wilson RG Precision Exterior Tree Matrix
open Pressure Pressure.Tube Pressure.Stores
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian
open AnalyticBridge.GaussianFieldAlignment FreeResolvent.Affine
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff InnerProductSpace Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

variable {G : Gauge} {c f : Side} {S : StepData c f}
  (T : Tube G S) (x : ℝ) (k : S.Choices) (F : Forest S.ratio)
local notation "Coarse" => Gaussian.Vec (Raw G c)
local notation "Fine" => Gaussian.Vec (Raw G f)
local notation "A" => noHole S
local notation "W" => shots S x
local notation "keys" => Rows.In (G:=G) x A F
local notation "short" => shorter (till x)

/-- Bilinear form of the raw responses at any original coarse field,
before selecting an active basis or taking an inverse. -/
theorem responses (r : Admit) (B : Coarse) (u v : Fine) :
    (Fintype.card Signed : ℝ)⁻¹ * ∑ s : Signed, ∑ i : Twin f ⊕ Bond c,
      inner ℝ (PhysicalAffineScalarJets.slope T k r B u (s,i))
        (PhysicalAffineScalarJets.slope T k r B v (s,i)) =
      u ⬝ᵥ (block S k T.high T.up r B *ᵥ v) := by
  rw [channels]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  let R := response S s B
  let D := tracks S s T.up r B * R
  let Q := duct S s k B
  rw [channel_qf]
  change _ = T.high.direct*((R *ᵥ u) ⬝ᵥ (R *ᵥ v)) + (D *ᵥ u) ⬝ᵥ (D *ᵥ v) +
    S.kernel.penalty*((Q *ᵥ u) ⬝ᵥ (Q *ᵥ v))
  have h {e n} (a b : FreeResolvent.Vec G n e) :
      a ⬝ᵥ b=∑ i, inner ℝ (decode a i) (decode b i) := FreeResolvent.flat_dot (decode a) (decode b)
  rw [h,h,h,← Equiv.sum_comp (Equiv.prodCongr (Equiv.refl (Site f)) plaqEquiv)
      (fun i => inner ℝ (decode (R *ᵥ u) i) (decode (R *ᵥ v) i)),
    ← Equiv.sum_comp (Equiv.prodCongr (Equiv.refl (Site f)) plaqEquiv)
      (fun i => inner ℝ (decode (D *ᵥ u) i) (decode (D *ᵥ v) i)),
    ← Equiv.sum_comp (Equiv.prodCongr (Equiv.refl (Site c)) axisEquiv)
      (fun i => inner ℝ (decode (Q *ᵥ u) i) (decode (Q *ᵥ v) i)),Finset.mul_sum]
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type,← Finset.sum_add_distrib]
  simp only [PhysicalAffineScalarJets.slope,Sum.elim_inl,Sum.elim_inr]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true,↓reduceIte,real_inner_smul_left,real_inner_smul_right,
      ← mul_assoc _ _ (inner ..),Real.mul_self_sqrt T.high.quadratic_pos.le]
    exact add_comm ..
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [inner_neg_neg,real_inner_smul_left,real_inner_smul_right,
      ← mul_assoc _ _ (inner ..),Real.mul_self_sqrt S.kernel.penalty_pos.le]
    rfl

private theorem color_sum (u v : LogArray G (Slots S)) :
    tape.symm (slip • u) ⬝ᵥ tape.symm (slip • v) =
      (Fintype.card Signed : ℝ)⁻¹ * ∑ s : Signed, ∑ i : Twin f ⊕ Bond c, inner ℝ (u (s,i)) (v (s,i)) := by
  unfold dotProduct
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type (f:=fun s : Slots S => _),Finset.mul_sum]
  simp_rw [Work.F03.inner_color,Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hs : slip * slip = (Fintype.card Signed : ℝ)⁻¹ := by
    unfold slip; rw [← mul_inv,Real.mul_self_sqrt (by positivity)]
  change (slip * u (s,i) j) * (slip * v (s,i) j) = _
  rw [← hs]
  ring

private theorem response_symmetry (r : Admit) (B : Coarse) (u v : Fine) :
    u ⬝ᵥ (block S k T.high T.up r B *ᵥ v) = v ⬝ᵥ (block S k T.high T.up r B *ᵥ u) := by
  calc
    _ = (Fintype.card Signed : ℝ)⁻¹ * ∑ s : Signed, ∑ i : Twin f ⊕ Bond c,
        inner ℝ (PhysicalAffineScalarJets.slope T k r B u (s,i))
          (PhysicalAffineScalarJets.slope T k r B v (s,i)) := (responses T k r B u v).symm
    _ = (Fintype.card Signed : ℝ)⁻¹ * ∑ s : Signed, ∑ i : Twin f ⊕ Bond c,
        inner ℝ (PhysicalAffineScalarJets.slope T k r B v (s,i))
          (PhysicalAffineScalarJets.slope T k r B u (s,i)) := by
      congr 1
      exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => real_inner_comm _ _
    _ = _ := responses T k r B v u

set_option maxHeartbeats 1200000 in
/-- Algebraic identity at the full untruncated input. It is independent
of the differentiability region needed when substituting physical rows for
the independently given responses. -/
theorem uncut (B : Coarse) :
    PhysicalAffineScalarUncut.gram T x k F B =
      (primary S F k T.high T.up FreeResolvent.Affine.all B).submatrix
        (live (G:=G) A F x) (live A F x) := by
  let D := PhysicalAffineScalarUncut.columns T x k F B
  let embed := FreeResolvent.insertion (address (G:=G) A F x)
  let a (i : keys) : Gaussian.Vec keys := Pi.single i (1:ℝ)
  let w (i : keys) := embed *ᵥ a i
  have hcol (i : keys) : D *ᵥ a i =
      tape.symm (slip • PhysicalAffineScalarJets.slope T k FreeResolvent.Affine.all B (w i)) := by
    rw [show a i = Pi.single i (1:ℝ) from rfl, Matrix.mulVec_single_one]
    funext p
    change tape.symm (slip • PhysicalAffineScalarJets.slope T k FreeResolvent.Affine.all B
      (launch.symm (Rows.fresh x W A F (axisPrice i)))) p = _
    rw [axisPrice,← relative_input A F x,ContinuousLinearEquiv.symm_apply_apply]
  ext i j
  have hi (M : Gaussian.Table keys) : a i ⬝ᵥ (M *ᵥ a j) = M i j := by simp [a]
  rw [← hi (PhysicalAffineScalarUncut.gram T x k F B),
    ← hi ((primary S F k T.high T.up FreeResolvent.Affine.all B).submatrix
      (live (G:=G) A F x) (live A F x))]
  change a i ⬝ᵥ ((D.transpose * D) *ᵥ a j) = _
  rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec,hcol i,hcol j,color_sum,
    responses T k,primary,Matrix.submatrix_submatrix,← FreeResolvent.insertion.dot_compress]
  change w j ⬝ᵥ (block S k T.high T.up FreeResolvent.Affine.all B *ᵥ w i) =
    w i ⬝ᵥ (block S k T.high T.up FreeResolvent.Affine.all B *ᵥ w j)
  exact response_symmetry T k FreeResolvent.Affine.all B (w j) (w i)

end YM.Integration.PhysicalAffineScalarMetric
end

/-! The complete signed output rows on the common raw fine-link coordinate
space. The original no-hole tree enters only through its active insertion and
its inverse Gram, which has zero extension to actual pinned tree links. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarProjection
open Function Filter Lattice Wilson RG RG.Patch Axial Bloch Laurent Precision Exterior Tree Matrix
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.SectorMeasure.Presented Next.Fluctuations.Sector
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine PhysicalAffineScalarUncut
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}
local notation "Coarse" => FreeResolvent.Vec G c 1
local notation "Fine" => FreeResolvent.Vec G f 1

private def responseMap (T : Tube G S) (k : S.Choices) (B : Coarse) : Fine →ₗ[ℝ] LogArray G (Slots S) where
  toFun := PhysicalAffineScalarJets.slope T k FreeResolvent.Affine.all B
  map_add' v w := by
    have hd {n : Side} {d : ℕ} (x y : FreeResolvent.Vec G n d) : decode (x+y)=decode x+decode y := (plain G n d).map_add _ _
    funext ⟨s,i⟩
    rcases i with p|b
    · cases hp : p.2 <;> simp [PhysicalAffineScalarJets.slope,hp,Matrix.mulVec_add,hd,smul_add]
    · simp [PhysicalAffineScalarJets.slope,Matrix.mulVec_add,hd,smul_add]
      abel
  map_smul' t v := by
    have hd {n : Side} {d : ℕ} (x : FreeResolvent.Vec G n d) : decode (t • x)=t • decode x := (plain G n d).map_smul _ _
    funext ⟨s,i⟩
    rcases i with p|b
    · cases hp : p.2 <;> simp [PhysicalAffineScalarJets.slope,hp,Matrix.mulVec_smul,hd,smul_comm (Real.sqrt _)]
    · simp [PhysicalAffineScalarJets.slope,Matrix.mulVec_smul,hd,smul_comm (Real.sqrt _)]

variable (T : Tube G S) (x : ℝ) (k : S.Choices) (F : Forest S.ratio)
local notation "store" => noHole S
local notation "keys" => Active store x F × G.ColorIndex

/-- The assembled response matrix acts on an arbitrary active field by the
complete physical response on the actual insertion of exactly those links. -/
theorem apply_columns (B : Coarse) (a : Gaussian.Vec keys) :
    PhysicalAffineScalarUncut.columns T x k F B *ᵥ a = tape.symm (slip •
      PhysicalAffineScalarJets.slope T k FreeResolvent.Affine.all B
        (launch.symm (fresh x (shots S x) store F (tape a)))) := by
  let E : Matrix (Raw G f) keys ℝ := FreeResolvent.insertion (address (G:=G) store F x)
  let L := gaugeCount.symm.toLinearEquiv.toLinearMap.comp ((slip • responseMap T k B).comp (Matrix.toLin' E))
  have he : PhysicalAffineScalarUncut.columns T x k F B=LinearMap.toMatrix' L := by
    ext i j
    rw [LinearMap.toMatrix'_apply]
    change tape.symm (slip • PhysicalAffineScalarJets.slope T k FreeResolvent.Affine.all B
        (launch.symm (fresh x (shots S x) store F (axisPrice j)))) i =
      tape.symm (slip • PhysicalAffineScalarJets.slope T k FreeResolvent.Affine.all B (E *ᵥ Pi.single j 1)) i
    rw [axisPrice,←relative_input store F x,ContinuousLinearEquiv.symm_apply_apply]
  rw [he,LinearMap.toMatrix'_mulVec,←relative_input store F x,ContinuousLinearEquiv.symm_apply_apply]
  rfl

/-- The physical fine-link Jacobian with all signed channels, prior to any
tree-coordinate removal. The coarse background and the selector are fixed. -/
def responseMatrix (B : Coarse) : Matrix (Rows.Receipt G S) (Raw G f) ℝ :=
  LinearMap.toMatrix' (gaugeCount.symm.toLinearEquiv.toLinearMap.comp (slip • responseMap T k B))

def extension : Matrix (Raw G f) keys ℝ := insertion (address store F x)

/-- Physical active covariance on common fine keys with *zero* on all pinned
links, also when those links differ between the two actual forests. -/
def embeddedCovariance (B : Coarse) : Gaussian.Table (Raw G f) :=
  let E := extension (G:=G) x F
  E * (PhysicalAffineScalarUncut.gram T x k F B)⁻¹ * E.transpose

theorem original_columns (B : Coarse) : PhysicalAffineScalarUncut.columns T x k F B =
    responseMatrix T k B * extension x F := by
  have h (a : Gaussian.Vec keys) : PhysicalAffineScalarUncut.columns T x k F B *ᵥ a =
      (responseMatrix T k B * extension x F) *ᵥ a := by
    rw [apply_columns,←relative_input store F x,ContinuousLinearEquiv.symm_apply_apply,
      ←Matrix.mulVec_mulVec,responseMatrix,LinearMap.toMatrix'_mulVec]
    rfl
  ext i j
  exact (by simpa only [Matrix.mulVec_single_one,Matrix.col,Matrix.transpose_apply] using congrFun (h (Pi.single j 1)) i)

theorem original_projection (B : Coarse) : projected T x k F B =
    1 - responseMatrix T k B * embeddedCovariance T x k F B * (responseMatrix T k B).transpose := by
  have hg : (PhysicalAffineScalarUncut.columns T x k F B).transpose * PhysicalAffineScalarUncut.columns T x k F B =
      PhysicalAffineScalarUncut.gram T x k F B := rfl
  rw [projected,PhysicalAffineScalarUncut.remaining,hg,original_columns,embeddedCovariance,Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  ext i j
  by_cases hij : i=j <;> simp [hij]

section change
variable (q : Site c)
    (F' : {t : Forest S.ratio // FreeResolvent.Affine.changed S F t q})

def changedCovariance (B : Coarse) := embeddedCovariance T x k F'.val B - embeddedCovariance T x k F B

def inputForcing (B : Coarse) : Fine := (responseMatrix T k B).transpose *ᵥ PhysicalAffineScalarUncut.offset T k B

theorem changed_projection (B : Coarse) : projected T x k F'.val B - projected T x k F B =
    -(responseMatrix T k B * changedCovariance T x k F q F' B * (responseMatrix T k B).transpose) := by
  rw [original_projection,original_projection,changedCovariance,Matrix.mul_sub,Matrix.sub_mul]
  abel

/-- Every tree change in the actual uncut minimizer's signed residual is
confined to the difference of the two original embedded physical covariances. -/
theorem changed_rows (B : Coarse) : sourceResidual T x k F'.val B - sourceResidual T x k F B =
    -(responseMatrix T k B *ᵥ (changedCovariance T x k F q F' B *ᵥ inputForcing T k B)) := by
  rw [changed_residual T x k F q F',changed_projection,Matrix.neg_mulVec,
    ←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec]
  rfl

def rootedRows (o : Site c) (B : Coarse) : Gaussian.Vec (Rows.Receipt G S) := fun i =>
  if PhysicalAffineScalarComparison.rowRoot S i=o then sourceResidual T x k F'.val B i + sourceResidual T x k F B i else 0

def rootForcing (o : Site c) (B : Coarse) : Fine := (responseMatrix T k B).transpose *ᵥ rootedRows T x k F q F' o B

/-- Exact original one-block rooted residual-square increment as a bilinear
pair against the sole changed, zero-extended, physical covariance tensor. -/
theorem changed_square (g : ℝ) (o : Site c) (B : Coarse) :
    rootSquare T x k F'.val g o B - rootSquare T x k F g o B =
    ((changedCovariance T x k F q F' B *ᵥ inputForcing T k B) ⬝ᵥ rootForcing T x k F q F' o B)/(2*g^2) := by
  let w := changedCovariance T x k F q F' B *ᵥ inputForcing T k B
  let J := responseMatrix T k B
  have hv := changed_rows T x k F q F' B
  change _ = (w ⬝ᵥ (J.transpose *ᵥ rootedRows T x k F q F' o B))/(2*g^2)
  rw [Matrix.dotProduct_transpose_mulVec]
  unfold rootSquare dotProduct
  rw [←Finset.sum_sub_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hr : PhysicalAffineScalarComparison.rowRoot S i=o
  · have h := congrFun hv i
    change sourceResidual T x k F'.val B i - sourceResidual T x k F B i = -(J *ᵥ w) i at h
    have he : (J *ᵥ w) i = sourceResidual T x k F B i - sourceResidual T x k F'.val B i := by linarith
    simp only [rootedRows,hr,if_true,he]
    ring
  · simp [rootedRows,hr]

/-- The same real tree tensor remains inside every arbitrary independent field
Taylor derivative; the active spaces of the two original forests may differ. -/
theorem mixed_square (g : ℝ) (o : Site c) (B : Coarse) (n : ℕ) (v : Fin n → Coarse) :
    iteratedFDeriv ℝ n (fun b => rootSquare T x k F'.val g o b-rootSquare T x k F g o b) B v =
      iteratedFDeriv ℝ n (fun b => ((changedCovariance T x k F q F' b *ᵥ inputForcing T k b) ⬝ᵥ
        rootForcing T x k F q F' o b)/(2*g^2)) B v := by
  rw [funext (changed_square T x k F q F' g o)]

/-- Entrywise physical charge on the unique changed covariance bracket, with
actual independently computed fine-link source and rooted dual source norms. -/
theorem root_price (g : ℝ) (o : Site c) (B : Coarse) (cost : Matrix (Raw G f) (Raw G f) ℝ)
    (paid : ∀ i j, |changedCovariance T x k F q F' B i j| ≤ cost i j) :
    |rootSquare T x k F'.val g o B-rootSquare T x k F g o B| ≤
    (∑ i, (∑ j, cost i j * |inputForcing T k B j|) * |rootForcing T x k F q F' o B i|)/(2*g^2) := by
  rw [changed_square,abs_div,abs_of_nonneg (show 0≤2*g^2 by positivity)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  let C := changedCovariance T x k F q F' B
  let a := inputForcing T k B
  let z := rootForcing T x k F q F' o B
  change |∑ i, (C *ᵥ a) i * z i| ≤ _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  change |∑ j, C i j*a j| ≤ _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (paid i j) (abs_nonneg _)
end change
end YM.Integration.PhysicalAffineScalarProjection
end

/-! The actual untruncated physical active inverse Gram on the common raw
fine-bond field is the zero extension of the independent canonical tree
inverse, including when two forests have different active coordinate sets. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarFullCovariance
open Function Filter Lattice Wilson RG Precision Exterior Tree Matrix
open Pressure Pressure.Stores Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine
open PhysicalAffineScalarAperture (noHole)
open PhysicalAffineScalarProjection
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}

theorem reindex_extension {α ι κ : Type} [Fintype α] [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (J : Matrix α κ ℝ) (M : Matrix κ κ ℝ) :
    J.submatrix id e * M.submatrix e e * (J.submatrix id e).transpose = J * M * J.transpose := by
  ext i j
  change (∑ t : ι, (∑ u : ι, J i (e u)*M (e u) (e t))*J j (e t)) =
    ∑ t : κ, (∑ u : κ, J i u*M u t)*J j t
  calc _ = ∑ t : ι, (∑ u : κ, J i u*M u (e t))*J j (e t) := by
          apply Finset.sum_congr rfl
          intro t _
          rw [e.sum_comp (fun u => J i u*M u (e t))]
       _ = _ := e.sum_comp (fun t => (∑ u : κ, J i u*M u t)*J j t)

/-- The independently specified inverse of the unrestricted affine Hessian,
extended by zero to the pinned bonds of the original no-hole forest. -/
def activeCovariance (T : Tube G S) (k : S.Choices) (F : Forest S.ratio) (b : FreeResolvent.Vec G c 1) :=
  let e := insertion (FreeResolvent.plant F (G:=G))
  e * (primary S F k T.high T.up FreeResolvent.Affine.all b)⁻¹ * e.transpose

variable (T : Tube G S) (x : ℝ) (k : S.Choices) (F : Forest S.ratio)
local notation "Coarse" => FreeResolvent.Vec G c 1

theorem original (b : Coarse) : embeddedCovariance T x k F b = activeCovariance T k F b := by
  let e : (Active (noHole S) x F × G.ColorIndex) ≃ Precision.Key F G := (Native.lineEquiv F x).symm
  let J := insertion (FreeResolvent.plant F (G:=G))
  let P := primary S F k T.high T.up FreeResolvent.Affine.all b
  have hg : PhysicalAffineScalarUncut.gram T x k F b = P.submatrix e e := by
    rw [PhysicalAffineScalarMetric.uncut]; rfl
  have hj : extension (G:=G) x F = J.submatrix id e := by
    ext i j
    rfl
  change extension (G:=G) x F * (PhysicalAffineScalarUncut.gram T x k F b)⁻¹ *
    (extension (G:=G) x F).transpose = J * P⁻¹ * J.transpose
  rw [hg,hj,Matrix.inv_submatrix_equiv]
  exact reindex_extension e J P⁻¹

/-- The actual scalar one-tree root receives the difference of the genuine
canonical zero-extended active covariances, on exactly the same raw fine keys. -/
theorem rooted (q : Site c)
    (F' : {t : Forest S.ratio // FreeResolvent.Affine.changed S F t q}) (g : ℝ) (o : Site c) (b : Coarse) :
    PhysicalAffineScalarUncut.rootSquare T x k F'.val g o b - PhysicalAffineScalarUncut.rootSquare T x k F g o b =
      (((activeCovariance T k F'.val b-activeCovariance T k F b) *ᵥ inputForcing T k b) ⬝ᵥ
        rootForcing T x k F q F' o b)/(2*g^2) := by
  rw [changed_square,changedCovariance,original,original]
end YM.Integration.PhysicalAffineScalarFullCovariance
end
