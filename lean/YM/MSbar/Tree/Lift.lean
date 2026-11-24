import YM.Next.RANK.Keys
import YM.Next.MAXWELL.Algebra

/-!
# Off-shell curl jets for separated MS coefficients

We use open-tensor components of physical Wick labels from the YM
system. This file fixes one coordinate-level convention (irrelevant for
the order-zero comparison, important for being able to specify the actual
finite-cutoff calculations). In particular we can evaluate on *raw*
covariance jets without them satisfying any dimension-four free equation. A
component index specifies a POSITIVE plaquette and an array of actual
coordinate partials. Use partial derivatives, not factorial-normalized
Taylor coefficients, on those components.

This leading-order implementation needn't resolve the spatial rotation
choice of lifts. It works without position dependence and keeps full
adjoint color invariance. See `invariant_symbol` below.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tree

open Function Set Filter Maxwell Maxwell.Wick Tensor Lattice
open scoped Topology ContDiff BigOperators Classical
open Next.Rank.CellsInt

variable {G : Gauge} {j l d : ℕ}

/-- Component basis: plane and derivative indices left open, and a color index.
Use real basis (orthonormal color metric of the defining representation).
There is no epsilon-dependent reduction of this basis. -/
abbrev Component (G : Gauge) (j : ℕ) := PlaqAxes × (Fin j → Axis) × G.ColorIndex

abbrev Raw (G : Gauge) (j : ℕ) := Component G j → ℝ

def Raw.color (v : Raw G j) (a : PlaqAxes) (i : Fin j→Axis) : G.Color :=
  WithLp.toLp 2 fun c => v (a,i,c)

def Raw.twist (L : G.Color →L[ℝ] G.Color) (v : Raw G j) : Raw G j :=
  fun i => L (Raw.color v i.1 i.2.1) i.2.2

lemma Raw.color_twist (L : G.Color →L[ℝ] G.Color) (v : Raw G j) (a i) :
    Raw.color (Raw.twist L v) a i=L (Raw.color v a i) := rfl

private def posFace (a : PlaqAxes) : Raw G j →ₗ[ℝ] Tensor.T E4 G.Color j where
  toFun v := (j.factorial:ℝ)⁻¹ • seed (Raw.color v a)
  map_add' u v := by
    rw [← smul_add]; congr 1
    apply seedEq; intro i
    rw [_root_.add_apply, fertile, fertile, fertile]
    rfl
  map_smul' r v := by
    change _ • _ = r • ((↑j.factorial:ℝ)⁻¹ • _)
    rw [smul_comm r]; congr 1
    apply seedEq; intro i
    rw [_root_.smul_apply, fertile, fertile]
    rfl

def unpack (G : Gauge) (j : ℕ) : Raw G j →ₗ[ℝ] TwoJet G.Color j :=
  LinearMap.pi fun a => LinearMap.pi fun b =>
    if h:a<b then posFace (⟨(a,b),h⟩:PlaqAxes)
    else if h:b<a then -(posFace (⟨(b,a),h⟩:PlaqAxes)) else 0

lemma unpack_pos (a : PlaqAxes) (v : Raw G j) (i) :
    unpack G j v a.val.1 a.val.2 (basis ∘ i) =
    (j.factorial:ℝ)⁻¹ • Raw.color v a i := by
  unfold unpack; simp only [LinearMap.pi_apply]; rw [dif_pos a.property];
  change ((j.factorial:ℝ)⁻¹ : ℝ) • seed (Raw.color v a) (_ ∘ i) = _
  rw [fertile]

lemma unpack_swap (a b : Axis) (v : Raw G j) :
    unpack G j v a b = - unpack G j v b a := by
  rcases lt_trichotomy a b with h|h|h
  · simp [unpack,h,h.not_gt]
  · subst b; simp [unpack]
  simp [unpack,h,h.not_gt]

def readComponent (i : Component G j) : Maxwell.Probe G j := (j.factorial:ℝ) •
  Maxwell.constrain (Maxwell.fromF G (basis ∘ i.2.1) i.2.2 i.1.val.1 i.1.val.2)

lemma readComponent_eq (i : Component G j) (v : Shell G j) :
    readComponent i v= (j.factorial:ℝ)*v.val i.1.val.1 i.1.val.2 (basis ∘ i.2.1) i.2.2 := rfl

def compileLeg (G : Gauge) (j : ℕ) := (Maxwell.Free.demark G j).comp (unpack G j)

lemma compileLeg_exact (v : Shell G j) : compileLeg G j (fun i => readComponent i v)=v := by
  let y (i) := readComponent i v
  have he : ClosedJet v.val := v.property.1
  have ht (a b) (h:a<b) : unpack G j y a b = v.val a b := by
    apply seedEq; intro i
    let e : PlaqAxes := ⟨(a,b),h⟩
    change unpack G j y e.val.1 e.val.2 _ = v.val e.val.1 e.val.2 _
    rw [unpack_pos]
    apply PiLp.ext; intro c
    change (j.factorial:ℝ)⁻¹ * ((j.factorial:ℝ) * v.val a b _ c)= _
    field_simp
    rfl
  unfold compileLeg; rw [LinearMap.comp_apply, show unpack G j y=v.val from ?_]; exact Maxwell.Free.restore v
  funext a b; rcases lt_trichotomy a b with h|h|h
  · exact ht _ _ h
  · subst b; exact (self (unpack_swap a a y)).trans (self (he.antisymmetric a a)).symm
  rw [unpack_swap a b, he.antisymmetric a b, ht b a h]
where self {w : Tensor.T E4 G.Color j} (h : w= -w) : w=0 := by
        have hz : (2:ℝ) • w=0 := by rw [two_smul]; nth_rw 1 [h]; exact neg_add_cancel _
        exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

lemma compileLeg_twist (L : G.Color →L[ℝ] G.Color) (v : Raw G j) :
    compileLeg G j (Raw.twist L v)= Maxwell.Free.faceMap j L (compileLeg G j v) := by
  let y:=Raw.twist L v; have ht (a b) (h:a<b)(i: Fin j→Axis) : unpack G j y a b (basis ∘ i)=L (unpack G j v a b (basis ∘ i)) := by
    let e:PlaqAxes:=⟨(a,b),h⟩
    change unpack G j y e.val.1 e.val.2 _=L (unpack G j v e.val.1 e.val.2 _)
    rw [unpack_pos,unpack_pos,map_smul]; rfl
  simp only [compileLeg,LinearMap.comp_apply]; rw [← Maxwell.Free.demark_cast]
  congr 1
  funext a b; apply seedEq; intro i
  change unpack G j y a b _= L (unpack G j v a b _)
  rcases lt_trichotomy a b with h|h|h
  · exact ht _ _ h i
  · subst b; simp [unpack]
  rw [unpack_swap a b y, unpack_swap a b v, _root_.neg_apply,
    _root_.neg_apply,map_neg, ht b a h i]

/-- Free off-shell symbol reading (inputs actual derivatives of curls). -/
def readSymbol (u : ∀ j, Raw G j) : WickPol G →ₐ[ℂ] ℂ :=
  probe fun j => compileLeg G j (u j)

lemma invariant_symbol (p : WickPol G) (h : p∈shellSector G d) (g : G.El) (u : ∀ j, Raw G j) :
    readSymbol (fun j => Raw.twist (G.adjoint g).toContinuousLinearMap (u j)) p = readSymbol u p := by
  unfold readSymbol; simp_rw [compileLeg_twist]; change probe (Maxwell.Free.shade g _) _ = _
  rw [← Maxwell.Free.pigment_action,(Maxwell.Free.sector.mp h).2]

/-- Finite coefficient matrix for slot-conversions, with colors treated explicitly. -/
def matrix (k : Slot G) (i : Component G k.1) := coordinateLeg k
    (compileLeg G k.1 (Pi.single i 1))

lemma matrix_at (k : Slot G) (v : Raw G k.1) : coordinateLeg k (compileLeg G _ v) = ∑ i, matrix k i * v i := by
  conv_lhs => rw [show v = ∑ i, v i • (Pi.single i (1:ℝ):Raw G k.1) by ext a; simp [Pi.single_apply] ]
  simp_rw [map_sum,map_smul,smul_eq_mul,matrix]; apply Finset.sum_congr rfl; intro i _; exact mul_comm ..

lemma lift_projects (k : Slot G) : coordinateLeg k = ∑ i, matrix k i • readComponent i := by
  apply LinearMap.ext; intro v
  rw [LinearMap.sum_apply]
  exact (congr_arg (fun p => coordinateLeg k p) (compileLeg_exact v).symm).trans (matrix_at k _)

end YM.MSbar.Tree
