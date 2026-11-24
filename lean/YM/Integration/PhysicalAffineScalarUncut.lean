import YM.Integration.PhysicalAffineScalarJets
import YM.Integration.PhysicalAffineScalarAperture
import YM.Push.STATIONARY_UNIFORM.Entries
import YM.Push.ABSOLUTE_SUMS.Basic
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Station

/-! The prescribed untruncated affine Gaussian on the *original* no-hole
active tree. The moved interaction is the true original fee less the
independent full affine energy at the same translated material input. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarUncut

open Function Filter Lattice Wilson RG RG.Patch Axial Bloch Laurent Precision Exterior Tree Matrix
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.SectorMeasure.Presented Next.Fluctuations.Sector
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian
open AnalyticBridge.GaussianFieldAlignment FreeResolvent.Affine
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

section square
variable {α ι : Type} [Fintype α] [Fintype ι] [DecidableEq ι]

def energy (D : Matrix α ι ℝ) (f : Gaussian.Vec α) (a : Gaussian.Vec ι) : ℝ :=
  let r := D *ᵥ a + f
  (r ⬝ᵥ r)/2

def minimizer (D : Matrix α ι ℝ) (f : Gaussian.Vec α) : Gaussian.Vec ι :=
  -((D.transpose * D)⁻¹ *ᵥ (D.transpose *ᵥ f))

theorem square (D : Matrix α ι ℝ) (f : Gaussian.Vec α) (h : (D.transpose * D).PosDef)
    (g : ℝ) (z : Gaussian.Vec ι) :
    let H := D.transpose * D
    let m := minimizer D f
    energy D f (m + g • z) = energy D f m + g^2 * force H⁻¹ z/2 := by
  intro H m
  let u := D *ᵥ m + f
  let v := D *ᵥ z
  have hn : D.transpose *ᵥ u = 0 := by
    change D.transpose *ᵥ (D *ᵥ (-(H⁻¹ *ᵥ (D.transpose *ᵥ f)))+f) = 0
    rw [Matrix.mulVec_add,Matrix.mulVec_mulVec,Matrix.mulVec_neg,Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ h.det_pos.ne'),Matrix.one_mulVec,neg_add_cancel]
  have h₁ : v ⬝ᵥ u=0 := by
    change (D *ᵥ z) ⬝ᵥ u=0
    rw [dotProduct_comm (D *ᵥ z) u,←Matrix.dotProduct_transpose_mulVec,hn,dotProduct_zero]
  have h₂ : u ⬝ᵥ v=0 := (dotProduct_comm u v).trans h₁
  have hq : force H⁻¹ z = v ⬝ᵥ v := by
    rw [force,Matrix.nonsing_inv_nonsing_inv _ (IsUnit.mk0 _ h.det_pos.ne')]
    rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec]
  have ha : D *ᵥ (m+g • z) + f = u + g • v := by
    rw [Matrix.mulVec_add,Matrix.mulVec_smul]; unfold u v; abel
  unfold energy
  rw [ha,hq]
  change ((u+g • v) ⬝ᵥ (u+g • v))/2 = (u ⬝ᵥ u)/2 + g^2*(v ⬝ᵥ v)/2
  simp only [add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,smul_eq_mul,h₁,h₂,mul_zero,add_zero,zero_add]
  ring
/-- Complement of the range of the full affine row operator, on the
common physical response space rather than the forest-dependent free space. -/
def remaining (D : Matrix α ι ℝ) : Gaussian.Table α := 1 - D * (D.transpose*D)⁻¹ * D.transpose

theorem residual_projection (D : Matrix α ι ℝ) (f : Gaussian.Vec α) :
    D *ᵥ minimizer D f + f = remaining D *ᵥ f := by
  rw [remaining,minimizer,Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.mulVec_neg,
    ←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec]
  abel

end square

section affine
variable {G : Gauge} {c f : Side} {S : StepData c f}
  (T : Tube G S) (x : ℝ) (k : S.Choices) (F : Forest S.ratio)
local notation "Coarse" => Gaussian.Vec (Raw G c)
local notation "V" => fun B : Coarse => represent (decode B)
local notation "A" => noHole S
local notation "W" => shots S x
local notation "keys" => Rows.In (G:=G) x A F

/-- The full transported path sum and the direct channel use the usual
even/odd label at the original plaquette. -/
def plaquetteRows {n : Side} (P : PathData G) (p : Clip) (U : Config G n) (i : Twin n) : G.Color :=
  if i.2 then P.ell U i.1 else shoot p U i.1

/-- Full fine-to-coarse stack including its residue and every true path. -/
def faceStack (v : Config G c) (i : Twin f) (j : Twin c) : Pay G := ∑' t : Cover,
  let a := mesh i
  let b := mesh j
  let r := S.ratio.residue a.1
  let w := route (lift r) (S.patch.L.val • t) 1
  if b.1=S.ratio.parent a.1+wrap c t then
    rated (replica S.ratio v) a.1 w (T.R.mf (r,a.2) b.2 t) else 0

/-- Full coarse noise-to-plaquette stack on exactly the original coarse bond. -/
def noiseStack (v : Config G c) (i : Bond c) (j : Twin c) : Pay G := ∑' t : Cover,
  let a := pole i
  let b := mesh j
  if b.1=a.1+wrap c t then rated v a.1 (route 0 t 1) (T.R.mn a.2 b.2 t) else 0

def offset (B : Coarse) : Prices G (Slots S) := tape.symm fun i =>
  let U := shone S i.1 B
  let v := pull i.1 0 (V B)
  let y := plaquetteRows T.down T.low v
  slip • i.2.elim (fun p => plaquetteRows T.up T.high U p - Pressure.zip (faceStack T v) y p)
    (fun b => Z S (S.prediction U (choice i.1 k)) v b - Pressure.zip (noiseStack T v) y b)

/-- All uncut transported offsets vanish at the same actual unit field. -/
theorem offset_zero (h : S.patch.Branches S.kernel G) : offset T k (0:Coarse)=0 := by
  have hu {n : Side} (i : Cell n) : faceValue (1:Config G n) i=1 := by simp [faceValue,travel,Lattice.square]
  have ht {n : Side} (v : Site n) (l : Slot) : l.atSite (1:Config G n) v=0 := by
    rw [Work.F03.atSite_path,hu,G.curvature_unit,map_zero]
  have hr {n : Side} (P : PathData G) (p : Clip) (i : Twin n) : plaquetteRows P p (1:Config G n) i=0 := by
    unfold plaquetteRows
    split <;> simp [PathData.ell,PathData.ellTerms,ht,shoot,hu,G.curvature_unit]
  have hv : (V (0:Coarse))=1 := by
    change represent (decode (0:Coarse))=1
    rw [show decode (0:Coarse) = 0 from (plain G c 1).map_zero,link_one]
  have hp {n : Side} (s : Signed) : pull s 0 (1:Config G n)=1 := by
    funext i
    unfold pull Step.read
    split <;> simp
  have hf (s : Signed) : shone S s (0:Coarse)=1 := by
    rw [shone,backdrop,show represent (decode (0:Coarse))=1 from hv,replica_one,hp]
  have hn (s : Signed) (i : Bond c) : Z S (S.prediction (1:Config G f) (choice s k)) 1 i=0 := by
    unfold Z
    simp [Push.settled S h i (choice s k),G.curvature_unit]
  apply (tape (G:=G) (ι:=Slots S)).injective
  rw [offset,tape.apply_symm_apply]
  change (fun i => _) = (0:LogArray G (Slots S))
  funext i
  obtain ⟨s,p|b⟩ := i
  · simp [hf,hv,hp,hr,Pressure.zip]
  · simp [hf,hv,hp,hr,hn,Pressure.zip]

/-- Count every plaquette and noise row. Input tree links are pinned by the
original physical section; no determining-stencil test is applied here. -/
def columns (B : Coarse) : Matrix (Rows.Receipt G S) keys ℝ := Matrix.of fun i j =>
  tape.symm (slip • PhysicalAffineScalarJets.slope T k FreeResolvent.Affine.all B
    (launch.symm (Rows.fresh x W A F (axisPrice j)))) i

def gram (B : Coarse) : Gaussian.Table keys := (columns T x k F B).transpose * columns T x k F B

def center (B : Coarse) := minimizer (columns T x k F B) (offset T k B)

def action (B : Coarse) := energy (columns T x k F B) (offset T k B)

/-- The original exact residual at the stationary point, on common physical
rows before any square or selection of a translation. -/
def sourceResidual (B : Coarse) : Prices G (Slots S) :=
  columns T x k F B *ᵥ center T x k F B + offset T k B

def projected (B : Coarse) := remaining (columns T x k F B)

theorem projected_residual (B : Coarse) :
    sourceResidual T x k F B = projected T x k F B *ᵥ offset T k B :=
  residual_projection _ _

/-- Same selector and all path offsets, two actual forests with separate
active indices. Only the two projected responses on physical rows change. -/
theorem changed_residual (tag : Site c) (F' : {U : Forest S.ratio // FreeResolvent.Affine.changed S F U tag})
    (B : Coarse) : sourceResidual T x k F'.val B - sourceResidual T x k F B =
      (projected T x k F'.val B - projected T x k F B) *ᵥ offset T k B := by
  rw [projected_residual,projected_residual,Matrix.sub_mulVec]

def rootSquare (g : ℝ) (o : Site c) (B : Coarse) : ℝ :=
  ∑ i : Rows.Receipt G S, if PhysicalAffineScalarComparison.rowRoot S i=o
    then -(sourceResidual T x k F B i)^2/(2*g^2) else 0

/-- The exact one-tree variation of the held squared source, with its
difference column and its sum column both evaluated on the same f. -/
theorem changed_root_square (tag : Site c)
    (F' : {U : Forest S.ratio // FreeResolvent.Affine.changed S F U tag})
    (g : ℝ) (o : Site c) (B : Coarse) :
    rootSquare T x k F'.val g o B - rootSquare T x k F g o B =
      ∑ i : Rows.Receipt G S, if PhysicalAffineScalarComparison.rowRoot S i=o then
        -(((projected T x k F'.val B - projected T x k F B) *ᵥ offset T k B) i *
          ((projected T x k F'.val B + projected T x k F B) *ᵥ offset T k B) i)/(2*g^2) else 0 := by
  unfold rootSquare
  rw [←Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : PhysicalAffineScalarComparison.rowRoot S i=o
  · simp only [h,if_true,Matrix.sub_mulVec,Matrix.add_mulVec,Pi.sub_apply,Pi.add_apply,projected_residual]
    ring
  · simp [h]

def scalar (g : ℝ) (B : Coarse) :=
  (Real.log (gram T x k F 0).det - Real.log (gram T x k F B).det)/2 -
    action T x k F B (center T x k F B)/g^2

/-- The stored exponent in the original sector with the independent reference
is the ideal paired scalar and the original nonlinear remainder after the
*same* affine action is subtracted at the material configuration. -/
theorem exponent {p : Clip} {σ E Λ : ℝ} (hT : T.up.Bounds p σ E Λ)
    (q : Chi) (d : ℝ) (Y : LinkArray G (Frozen A x F)) {β : ℝ} (hβ : 0<β)
    (B : Coarse) (h₀ : (gram T x k F 0).PosDef) (h : (gram T x k F B).PosDef)
    (z : Prices G (Active A x F)) (U : Config G f) :
    let g := coupling β
    let H₀ := gram T x k F 0
    let H := gram T x k F B
    let m := center T x k F B
    let a := m+g • z
    Real.log (chartCost H⁻¹ g / chartCost H₀⁻¹ g) +
      (-β * averaged (Rows.residual T x (V B) k W A F q d Y U a) +
        Rows.adjustment T x (V B) k W A F q d Y H⁻¹ m g z) =
    scalar T x k F g B - β*(Rows.fee T x (V B) k A U - action T x k F B a) := by
  intro g H₀ H m a
  have hg : 0<g := coupling_pos hβ
  have hg₂ : g^2 ≠ 0 := pow_ne_zero 2 hg.ne'
  have hb : (g^2)⁻¹ = β := by simpa only [g] using by_coupling hβ
  have he : action T x k F B a = action T x k F B m + g^2 * force H⁻¹ z/2 :=
    square (columns T x k F B) (offset T k B) h g z
  have hfee : Rows.fee T x (V B) k A U = averaged (Rows.residual T x (V B) k W A F q d Y U a) +
      Rows.guide T x (V B) k W A F q d Y a :=
    (Rows.exact_fee T x (V B) k A U).trans (Rows.compose_residual T x (V B) k W A F q d Y hT U a)
  rw [PhysicalAffineScalarComparison.chart_log_ratio h.inv h₀.inv hg,
    Matrix.det_nonsing_inv,Matrix.det_nonsing_inv,Ring.inverse_eq_inv,Ring.inverse_eq_inv,
    Real.log_inv,Real.log_inv,Rows.adjusted T x (V B) k W A F q d Y H⁻¹ m z hg,
    scalar,hfee,he]
  change _ + (-β * _ + (force H⁻¹ z / 2 - Rows.guide T x (V B) k W A F q d Y a / g^2)) =
    (Real.log H₀.det - Real.log H.det)/2 - action T x k F B m/g^2 -
    β*(_-(action T x k F B m+g^2*force H⁻¹ z/2))
  rw [← hb]
  field_simp [hg₂]
  ring

/-- The full signed scalar at one original coarse translation. The tested
site may also be held through all later field differentiations. -/
def scalarAt (g : ℝ) (s : Site c) (B : Coarse) :=
  PhysicalAffineScalarJets.placed x A F g s (gram T x k F 0) (gram T x k F B)
    (columns T x k F B *ᵥ center T x k F B + offset T k B)

/-- The paired determinant and stationary residual disappear separately
at each held original translation at degree zero. -/
theorem root_zero (h : S.patch.Branches S.kernel G) (g : ℝ) (s : Site c) :
    scalarAt T x k F g s (0:Coarse) = 0 := by
  simp [scalarAt,center,minimizer,offset_zero T k h,PhysicalAffineScalarJets.placed]

theorem scalar_sum (g : ℝ) (B : Coarse) (h₀ : (gram T x k F 0).PosDef)
    (h : (gram T x k F B).PosDef) :
    scalar T x k F g B = ∑ s : Site c, scalarAt T x k F g s B := by
  unfold scalar scalarAt PhysicalAffineScalarJets.placed action energy
  rw [Finset.sum_add_distrib,AnalyticBridge.RelativeLogdet.log_trace h₀,
    AnalyticBridge.RelativeLogdet.log_trace h]
  simp_rw [Finset.sum_comm (s:=Finset.univ (α:=Site c)) (t:=Finset.univ (α:=keys)),
    Finset.sum_comm (s:=Finset.univ (α:=Site c)) (t:=Finset.univ (α:=Rows.Receipt G S))]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true,← Finset.sum_div,
    Finset.sum_sub_distrib,Finset.sum_neg_distrib,dotProduct,sq]
  ring

/-- Actual chart normalization and scalar multiplier in the original
conditional numerator or quiet column, with all physical likelihoods and
selector defaults evaluated at one and the same material field. -/
theorem marked_backdrop {p : Clip} {σ E Λ w : ℝ} (hT : T.up.Bounds p σ E Λ)
    (R : Rep G f) (hβ : 0<R.beta) (D : Allocation G S x w) (q : Chi)
    (J : ChartRatio G) (d : ℝ) (Y : LinkArray G (Frozen A x F))
    (B : Coarse) (h₀ : (gram T x k F 0).PosDef) (h : (gram T x k F B).PosDef)
    (z : Prices G (Active A x F)) :
    let g := coupling R.beta
    let H₀ := gram T x k F 0
    let H := gram T x k F B
    let m := center T x k F B
    let a := m+g • z
    let y := tape a
    let U := physical A F (V B) Y y
    Marked.outside T x (V B) A R F J H⁻¹ *
        Marked.backdrop T x (V B) k A R W F D q J d H⁻¹ (fun _ => m) Y z =
      Marked.outside T x (V B) A R F J H₀⁻¹ *
        (reserve q J d y * doors q d y * D.bill A k U (V B) * S.likelihood U k *
        Real.exp (scalar T x k F g B - R.beta*(Rows.fee T x (V B) k A U - action T x k F B a))) := by
  intro g H₀ H m a y U
  let C := H⁻¹
  let C₀ := H₀⁻¹
  let L := Real.log (chartCost C g / chartCost C₀ g)
  let I := -R.beta * averaged (Rows.residual T x (V B) k W A F q d Y U a) +
    Rows.adjustment T x (V B) k W A F q d Y C m g z
  let t := reserve q J d y * doors q d y * D.bill A k U (V B) * S.likelihood U k
  have hg : 0<g := coupling_pos hβ
  have hc : 0<chartCost C g := chartCost_pos C h.inv hg
  have hc₀ : 0<chartCost C₀ g := chartCost_pos C₀ h₀.inv hg
  have hExp : Real.exp L = chartCost C g / chartCost C₀ g := Real.exp_log (div_pos hc hc₀)
  have hOutside : Marked.outside T x (V B) A R F J C =
      Marked.outside T x (V B) A R F J C₀ * Real.exp L := by
    unfold Marked.outside
    rw [hExp]
    change _ * chartCost C g = _ * chartCost C₀ g * (chartCost C g / chartCost C₀ g)
    field_simp [hc₀.ne']
  have hI : L+I=scalar T x k F g B - R.beta*(Rows.fee T x (V B) k A U - action T x k F B a) :=
    exponent T x k F hT q d Y hβ B h₀ h z U
  change Marked.outside T x (V B) A R F J C * (t * Real.exp I) =
    Marked.outside T x (V B) A R F J C₀ * (t * Real.exp _)
  rw [hOutside,← hI,Real.exp_add L I]
  ring
end affine
namespace RouteTail
open Push.AbsoluteSums Set Finset
variable {G : Gauge} {n c f : Side} {S : StepData c f} {σ C L : ℝ}

theorem route_size (x y : Cover) : (route x y 1).length = size (y-x) := by
  have ha : allAxes 1 = [0,1,2,3] := by decide
  simp [route,axisRoute,ha,size,Fin.sum_univ_succ,straight,Axis]

private theorem scaled (u : Cover) (d : ℕ) : size (d • u) = d*size u := by
  simp [size,Pi.smul_apply,Int.natAbs_mul,Finset.mul_sum]

private theorem lift_bound (L : Side) (x : Site L) : size (lift x) ≤ 4*L.val := calc
  _ ≤ ∑ _i : Axis, L.val := Finset.sum_le_sum fun i _ => by have hh := lift_centers x i; omega
  _ = _ := by simp [Axis]

theorem length_face (L : Side) (r : Site L) (u : Cover) :
    ((route (lift r) (L.val • u) 1).length:ℝ) ≤ (5*(L.val:ℝ))*(1+size u) := by
  rw [route_size,sub_eq_add_neg]
  have h1 := size_add (L.val • u) (-(lift r))
  rw [scaled,size_neg] at h1
  have h2 := h1.trans (Nat.add_le_add_left (lift_bound L r) _)
  have hc : (size (L.val • u + -(lift r)):ℝ) ≤ (L.val:ℝ)*(size u:ℝ) + 4*(L.val:ℝ) := by exact_mod_cast h2
  apply hc.trans
  nlinarith [show 0 ≤ (L.val:ℝ)*(size u:ℝ) by positivity]

end RouteTail
end YM.Integration.PhysicalAffineScalarUncut
end
