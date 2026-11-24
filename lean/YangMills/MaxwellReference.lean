import YangMills.FreeFields
import YangMills.MatrixGauge
import YM.Next.MAXWELL.Stress
import YM.Next.MAXWELL.Caps

/-! The free curvature fields, their Wick moments and their metric stress tensor. -/

set_option autoImplicit false
noncomputable section
namespace YangMills
open YM YM.Maxwell YM.Maxwell.Free
open Function Filter Set
open scoped Topology BigOperators InnerProductSpace Classical

def maxwellCoordinates (g : GaugeGroup) : Maxwell.Coordinates g where
  m := g.core.lieDim
  matrix := g.core.colorMat
  colors := by
    ext m
    constructor
    · rintro ⟨v,rfl⟩
      exact (g.generates _).2 (g.core.colorMat_mem v)
    · intro hm
      let w : g.core.Alg := ⟨m,(g.generates _).1 hm⟩
      exact ⟨g.core.colorIso.symm w,congrArg Subtype.val (g.core.colorIso.apply_symm_apply w)⟩
  traceForm := g.core.trace_color
  shell j := onShell g.core.Color j
  shell_iff _ _ := ⟨fun ⟨h,e⟩ => ⟨h.coeffSym,h.antisymmetric,h.closed,e⟩,
    fun ⟨s,a,b,e⟩ => ⟨⟨s,a,b⟩,e⟩⟩
  rank := legDim g.core
  basis := frame g.core
  rotate u j := castFace (G := g.core) u j
  adjoint u _ A a b v := g.core.mat_adjoint u (A.val a b v)

private theorem wickRule (g : GaugeGroup) {n : ℕ} (x : Points n) (W : Wick.Powers g.core n) :
    Wick.moment g.core x (fun i => Wick.monBasis g.core (W i)) =
      (maxwellCoordinates g).wickMonomial x W := by
  rw [Wick.moment_basis]
  change Wick.monomial x W = ∑ᶠ s : Wick.Occ.Matching W, ∏ᶠ v : Wick.Occ W,
    if v.label < (s.val v).label then Wick.entry v.probe (s.val v).probe (x v.label) (x (s.val v).label)
    else 1
  simp only [finsum_eq_sum_of_fintype, finprod_eq_prod_of_fintype, Wick.monomial,
    Wick.Occ.graph, Wick.Occ.corners, Finset.prod_filter, Wick.Occ.edge, Wick.Occ.partner]

private theorem sectorDescription (g : GaugeGroup) (d : ℕ) (p : WickPol g.core) :
    p ∈ shellSector g.core d ↔ (maxwellCoordinates g).Admissible d p := by
  change p ∈ shellSector g.core d ↔ p ∈ lowerCap g.core d ∧
    ∀ (u : g.core.El) (A : TaylorTower g.core), probe (shade u A) p = probe A p
  rw [sector]
  apply and_congr_right
  intro _
  constructor
  · intro fixed u A
    rw [← pigment_action (G := g.core) u A p, fixed u]
  · intro fixed u
    apply equalPol (G := g.core)
    intro A
    rw [pigment_action, fixed u A]

private theorem stressReading (g : GaugeGroup) (A : TaylorTower g.core) (a b : Axis) :
    probe A (-polStress g.core a b) = (maxwellCoordinates g).stressValue A a b := by
  simp only [map_neg, polStress, sheetEnergy, map_sub, map_smul, map_sum, measure_phi,
    kr_eq, smul_eq_mul, ← Complex.ofReal_sum, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
  rfl

private theorem detectsPolynomial (g : GaugeGroup) (d : ℕ) (p : shellSector g.core d) :
    (∀ n (w : Fin n → Σ e, shellSector g.core e) (x : Points (n+1)), x ∈ separated _ →
      Wick.moment g.core x (Fin.cons p.val (fun i => (w i).2.val)) = 0) ↔ p = 0 := by
  have null_iff : p ∈ residual g.core d ↔ p = 0 := by rw [no_residual, Submodule.mem_bot]
  rw [← null_iff, YM.Maxwell.residual, LinearMap.mem_ker]
  constructor
  · intro h
    funext w
    exact (test_formula w d p).trans (h w.n (fun i => ⟨w.d i,w.exterior i⟩) w.x w.clear)
  · intro h n w x hx
    let v : ProbeFamily g.core := ⟨n,fun i => (w i).1,fun i => (w i).2,x,hx⟩
    exact (test_formula v d p).symm.trans (congrFun h v)

def maxwellReference (g : GaugeGroup) : Maxwell.Reference g where
  toCoordinates := maxwellCoordinates g
  sector := shellSector g.core
  sector_iff := sectorDescription g
  moment := Wick.moment g.core
  wick := wickRule g
  stress a b := ⟨-polStress g.core a b,Submodule.neg_mem _ (stress_label _ _ _)⟩
  stress_eval := stressReading g
  detected := detectsPolynomial g

end YangMills
