import YM.Integration.PhysicalAffineScalarComparison
import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Operators
import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Resolvent
import YM.Push.FREE_RESOLVENT.Tags

/-! Ordinary jets of the complete stationary scalar on the actual conditional
tree.  Both its Gaussian diagonal logarithm and its signed residual rows are
located at their physical coarse sites.  The independent finite matrix is
constructed from the whole predictor response and plaquette response in raw
coordinates with the true path-length cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarJets

open Function Filter Lattice Wilson RG Precision Exterior Tree Matrix
open Pressure Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian
open AnalyticBridge.GaussianFieldAlignment FreeResolvent.Affine
open PhysicalAffineScalarComparison
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f}
  (T : Tube G S) (x : ℝ) (k : S.Choices) (A : Stores S) (F : Forest S.ratio)
  (q : Chi) (d : ℝ) {σ E Λ : ℝ}
local notation "Coarse" => Gaussian.Vec (Raw G c)
local notation "Fine" => Gaussian.Vec (Raw G f)
local notation "V" => fun B : Coarse => represent (decode B)
local notation "W" => shots S x
local notation "liveKey" => live (G:=G) A F x
local notation "key" => Rows.In (G:=G) x A F
local notation "short" => shorter (till x)

/-- Independent signed raw linearized rows on the original oriented channels,
before applying the physical aperture. -/
def slope (r : Admit) (B : Coarse) (v : Fine) : LogArray G (Slots S) := fun i =>
  i.2.elim (fun p =>
    if p.2 then decode ((tracks S i.1 T.up r B * response S i.1 B) *ᵥ v)
        (p.1.1,plaquette p.1.2)
    else Real.sqrt T.high.direct • decode (response S i.1 B *ᵥ v) (p.1.1,plaquette p.1.2))
    (fun b => -(Real.sqrt S.kernel.penalty •
      decode (duct S i.1 k B *ᵥ v) (b.1,coord b.2)))

/-- The unshifted row retains the physical predictor, coarse subtraction and
original affine background at the indicated signed coordinate. -/
def offset (B : Coarse) : LogArray G (Slots S) := fun i =>
  i.2.elim (fun p => T.Xf (till x) (shone S i.1 B) p -
      T.Mv (till x) (temp x) (pull i.1 0 (V B)) p)
    (fun b => Z S (S.prediction (shone S i.1 B) (choice i.1 k))
      (pull i.1 0 (V B)) b - T.Mw (till x) (temp x) (pull i.1 0 (V B)) b)

theorem offset_eq (B : Coarse) : Rows.base T x (V B) k = offset T x k B := by
  funext i
  rcases i with ⟨s,p|b⟩
  · change Rows.faceFixed T x s (V B) p = _
    simp only [Rows.faceFixed,offset,Sum.elim_inl,fixed_facade,shone,backdrop]
  · change Rows.noiseFixed x (V B) k s b (T:=T) = _
    simp only [Rows.noiseFixed,offset,Sum.elim_inr,fixed_facade,shone,backdrop]

theorem slope_eq (h : S.patch.Branches S.kernel G) (hT : T.up.Bounds T.high σ E Λ)
    (B : Coarse) (hB : WholeNoise k B) (a : Directions G f) :
    Rows.bump T x (V B) k a = slope T k short B (launch.symm a) := by
  obtain ⟨v,rfl⟩ := launch.surjective a
  rw [ContinuousLinearEquiv.symm_apply_apply]
  funext i
  rcases i with ⟨s,p|b⟩
  · exact faceKick_columns x T B s p v hT
  · change -(Real.sqrt S.kernel.penalty • blockJet (V B) k s b (launch v)) = _
    rw [block_columns k B s b v h hB]
    rfl

def columns (r : Admit) (B : Coarse) : Matrix (Rows.Receipt G S) key ℝ := Matrix.of fun i j =>
  tape.symm (Rows.restrict x W A F (slope T k r B (launch.symm
    (Rows.fresh x W A F (axisPrice j))))) i

def affineOffset (r : Admit) (Y : LinkArray G (Frozen A x F)) (B : Coarse) :
    Prices G (Slots S) := tape.symm (Rows.restrict x W A F (offset T x k B +
      slope T k r B (launch.symm (Rows.input x A F (autoShell q d (V B) Y)))))

def gram (r : Admit) (B : Coarse) : Gaussian.Table key :=
  (primary S F k T.high T.up r B).submatrix liveKey liveKey

def center (r : Admit) (Y : LinkArray G (Frozen A x F)) (B : Coarse) : Gaussian.Vec key :=
  -((gram T x k A F r B)⁻¹ *ᵥ ((columns T x k A F r B).transpose *ᵥ affineOffset T x k A F q d r Y B))

def residual (r : Admit) (Y : LinkArray G (Frozen A x F)) (B : Coarse) : Prices G (Slots S) :=
  columns T x k A F r B *ᵥ center T x k A F q d r Y B + affineOffset T x k A F q d r Y B

/-- The independent source, row matrix, and Gram agree simultaneously in the
raw field germ, before any inverse, square or logarithm is evaluated. -/
theorem affine_germ (Y : LinkArray G (Frozen A x F)) (h : S.patch.Branches S.kernel G)
    (hT : T.up.Bounds T.high σ E Λ) :
    ∀ᶠ B : Coarse in 𝓝 0, Rows.move T x (V B) k W A F = columns T x k A F short B ∧
      Rows.source T x (V B) k W A F q d Y = affineOffset T x k A F q d short Y B ∧
      Rows.gram T x (V B) k W A F = gram T x k A F short B := by
  filter_upwards [near_whole k h,affine_near A F x T k h hT] with B hB hQ
  refine ⟨?_,?_,hQ⟩
  · ext i j
    change tape.symm (Rows.restrict x W A F (Rows.bump T x (V B) k _)) i = _
    rw [slope_eq T x k h hT B hB]
    rfl
  · unfold Rows.source affineOffset
    rw [offset_eq T x k B,slope_eq T x k h hT B hB]

/-- A diagonal-log root and a source-row root are both genuine physical coarse
sites, irrespective of the size and orientation of the original stencil. -/
def placed (g : ℝ) (s : Site c) (H₀ H : Gaussian.Table key) (v : Prices G (Slots S)) : ℝ :=
  (∑ j : key, if S.ratio.parent j.1.val.val.1=s then
    (AnalyticBridge.RelativeLogdet.logKernel H₀ j j -
      AnalyticBridge.RelativeLogdet.logKernel H j j)/2 else 0) +
    ∑ i : Rows.Receipt G S, if rowRoot S i=s then -(v i)^2/(2*g^2) else 0

def actualRoot (Y : LinkArray G (Frozen A x F)) (g : ℝ) (s : Site c) (B : Coarse) : ℝ :=
  placed x A F g s (Rows.gram T x (V 0) k W A F) (Rows.gram T x (V B) k W A F)
    (Rows.direct T x (V B) k W A F q d Y (stationary T x (V B) k W A F q d Y))

def geometricRoot (r : Admit) (Y : LinkArray G (Frozen A x F)) (g : ℝ) (s : Site c)
    (B : Coarse) : ℝ := placed x A F g s (gram T x k A F r 0) (gram T x k A F r B)
      (residual T x k A F q d r Y B)

/-- The physical density at its curved full center and paired flat Gaussian
is represented by these very root contributions. -/
theorem sum_actual (Y : LinkArray G (Frozen A x F)) (g : ℝ) (hg : 0<g) (B : Coarse)
    (h₀ : (Rows.gram T x (V 0) k W A F).PosDef) (hB : (Rows.gram T x (V B) k W A F).PosDef)
    (z : Prices G (Active A x F)) :
    let H := Rows.gram T x (V B) k W A F
    let H₀ := Rows.gram T x (V 0) k W A F
    let m := stationary T x (V B) k W A F q d Y
    Real.log (chartCost H⁻¹ g / chartCost H₀⁻¹ g) +
      Rows.adjustment T x (V B) k W A F q d Y H⁻¹ m g z =
      ∑ s : Site c, actualRoot T x k A F q d Y g s B := by
  intro H H₀ m
  rw [stationary_scalar T x (V B) k W A F q d Y H₀ h₀ hB hg z]
  unfold actualRoot placed rowSquare
  rw [Finset.sum_add_distrib]
  congr 1
  rw [AnalyticBridge.RelativeLogdet.log_trace h₀,AnalyticBridge.RelativeLogdet.log_trace hB,
    Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true,← Finset.sum_div,Finset.sum_sub_distrib]

theorem root_germ (Y : LinkArray G (Frozen A x F)) (g : ℝ) (s : Site c)
    (h : S.patch.Branches S.kernel G) (hT : T.up.Bounds T.high σ E Λ) :
    actualRoot T x k A F q d Y g s =ᶠ[𝓝 0] geometricRoot T x k A F q d short Y g s := by
  have ha := affine_germ T x k A F q d Y h hT
  have h₀ := ha.self_of_nhds.2.2
  filter_upwards [ha] with B hB
  unfold actualRoot geometricRoot residual stationary center Rows.direct Rows.blame
  rw [h₀,hB.1,hB.2.1,hB.2.2]

theorem root_jet (Y : LinkArray G (Frozen A x F)) (g : ℝ) (s : Site c)
    (h : S.patch.Branches S.kernel G) (hT : T.up.Bounds T.high σ E Λ)
    (n : ℕ) (v : Fin n → Coarse) :
    iteratedFDeriv ℝ n (actualRoot T x k A F q d Y g s) 0 v =
      iteratedFDeriv ℝ n (geometricRoot T x k A F q d short Y g s) 0 v := by
  rw [((root_germ T x k A F q d Y g s h hT).iteratedFDeriv (𝕜:=ℝ) n).self_of_nhds]

/-- The finite difference at one actual changed tree carries its original
source, active keys and frozen coordinates on each side.  This identifies the
change in every ordinary tensor at the held scalar root before estimating any
true path-length or principal-window tail. -/
theorem one_tree_jet (tag : Site c) (F' : {U : Forest S.ratio // FreeResolvent.Affine.changed S F U tag})
    (Y : LinkArray G (Frozen A x F)) (Y' : LinkArray G (Frozen A x F'.val))
    (g : ℝ) (s : Site c) (h : S.patch.Branches S.kernel G) (hT : T.up.Bounds T.high σ E Λ)
    (n : ℕ) (v : Fin n → Coarse) :
    iteratedFDeriv ℝ n (fun B => actualRoot T x k A F'.val q d Y' g s B -
      actualRoot T x k A F q d Y g s B) 0 v =
    iteratedFDeriv ℝ n (fun B => geometricRoot T x k A F'.val q d short Y' g s B -
      geometricRoot T x k A F q d short Y g s B) 0 v := by
  have h₁ := root_germ T x k A F'.val q d Y' g s h hT
  have h₂ := root_germ T x k A F q d Y g s h hT
  have hh : (fun B => actualRoot T x k A F'.val q d Y' g s B -
      actualRoot T x k A F q d Y g s B) =ᶠ[𝓝 0] fun B =>
      geometricRoot T x k A F'.val q d short Y' g s B - geometricRoot T x k A F q d short Y g s B := by
    filter_upwards [h₁,h₂] with B hB hC
    rw [hB,hC]
  rw [(hh.iteratedFDeriv (𝕜:=ℝ) n).self_of_nhds]

end YM.Integration.PhysicalAffineScalarJets
end
