import YangMills.MaxwellReference
import YangMills.WilsonProof.NativeSupport.HierarchyBridge
import YM.Pert.FirstTarget

/-! Identify the concrete curvature shell and its separated Wick table with the
public reference, then transport the existing common-sequence theorem along that
identification. -/
set_option autoImplicit false
noncomputable section
namespace YangMills
open YM YM.Spec YM.OPE.Orbits YM.Maxwell YM.Maxwell.Free
open Function Filter Set
open scoped Topology BigOperators InnerProductSpace Classical


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
    (∀ n (w : Fin n → Σ e, shellSector g.core e) (x : Points (n+1)), x ∈ WilsonFamily.separated _ →
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


variable {g : GaugeGroup} {C : Family g.core} {p : Extraction.Order} {S : Table C.book}
variable (F : Final C p S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

/-- Use the same physical stress, mixing maps and radii as the detailed extension. -/
def publicScaling (X : Climb.Scaling S) (h : Pert.FirstExtension F X) :
    (hierarchy F Q).MaxwellScaling (maxwellReference g) where
  r := X.r
  positive := X.positive
  later := X.later
  drips := X.drips
  frame k d := (fields C.labels d).symm.trans (X.U k d)
  jets n j q marked ab K hK hsep ε hε := by
    let v (i : Fin n) : (freeTable C.labels).Tag := ⟨(q i).1,(fields C.labels _).symm (q i).2⟩
    have hh := h.jets n j v marked ab hK hsep hε
    have free (z : Points n) : Ward.disc (Pert.freeWithStress C.labels v marked ab) z =
        Wick.moment g.core z (fun i => if marked i then -polStress g.core (ab i).1 (ab i).2
          else (q i).2.val) := by
      rw [Ward.disc, display]
      congr 1
      funext i
      change supply C.labels (Pert.freeWithStress C.labels v marked ab i) = _
      unfold Pert.freeWithStress
      split_ifs with hi
      · change address C.labels 4 (-original C.labels (ab i).1 (ab i).2) = _
        rw [map_neg,inertia]
      · exact congrArg Subtype.val ((fields C.labels (q i).1).apply_symm_apply (q i).2)
    rw [funext free] at hh
    exact hh

end YangMills
