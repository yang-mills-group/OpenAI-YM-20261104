import YM.RGComparison.Core16.WilsonXLocal
import YM.Bid.Source

/-!
# Bare WILSON germs of the actual Family stencils

Each canonical section (one standard label coordinate) has a Laurent power given by the slot
rank, not the filtration degree. Use the verified `pop` property and the `C.O` construction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Descent
open Lattice RG Tree Wilson Precision Push.BetaTransport Marker Source
open Function Filter MeasureTheory Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical InnerProductSpace
open PertExtension PertExtension.Series Tested Radial Extra.Trajectories
variable {G : Gauge} {n c f : Side}

-- price exponents of top input easily read along logs, not tree-gauge coordinates of quotient by
-- constant modes. `liftEnd` linear from the joint path slice and coarse tangent (then can restrict
-- to coarse zero). Note `fine V x` didn't use near-identity logs!
private def nextEdge (S : StepData c f) (T : Forest S.ratio) (d : Descent n f) :
    (Push.In G c × Coordinates G (push S T d)) →ₗ[ℝ] (Push.In G f × Coordinates G d) where
  toFun u := (sliceCoord S T (u.2 ∘ Sum.inl), u.2 ∘ Sum.inr)
  map_add' u v := by
    apply Prod.ext
    · let x := u.2 ∘ (@Sum.inl T.Free d.Links)
      let y := v.2 ∘ (@Sum.inl T.Free d.Links)
      change sliceCoord S T (x+y) = _; exact map_add (sliceCoord S T) x y
    rfl
  map_smul' t u := by
    apply Prod.ext
    · let x := u.2 ∘ (@Sum.inl T.Free d.Links)
      change sliceCoord S T (t • x) = _; exact map_smul (sliceCoord S T) t x
    rfl

def liftEnd : {c : Side} → (d : Descent n c) → (Push.In G c × Coordinates G d) →ₗ[ℝ] Push.In G n
  | _, .nil => LinearMap.fst ..
  | _, .push S T d => (liftEnd d).comp (nextEdge S T d)

lemma path_lift (d : Descent n c) (u : Push.In G c) (x : Coordinates G d) :
    d.fine (represent u) (d.tablePath x) = represent (liftEnd d (u,x)) := by
  induction d with
  | nil => rfl
  | @push m i S T d ih =>
    have he : T.drape ((push S T d).tablePath x ∘ Sum.inl) = represent (sliceCoord S T (x ∘ Sum.inl)) := drape_coord ..
    rw [fine,he]; exact ih _ (x ∘ Sum.inr)

def topDir (d : Descent n c) := (liftEnd (G:=G) d).comp (LinearMap.inr ..)
lemma path_top (d : Descent n c) (x : Coordinates G d) : d.fine 1 (d.tablePath x) = represent (topDir d x) := by
  rw [← link_one]; exact path_lift ..

lemma smooth_test (d : Descent n c) : ContDiffAt ℝ ∞ (matrixField (G:=G) ∘ d.fine 1 ∘ d.tablePath) 0 := by
  simp_rw [Function.comp_def, path_top]; refine contDiffAt_pi.mpr fun i => ?_
  exact ((Work.F03.represent_smooth i).of_le le_top |>.contDiffAt).comp (f:=topDir (G:=G) d) _
    ((topDir d).toContinuousLinearMap.contDiff.contDiffAt)

variable {C : Family G} {p N D : ℕ} (B : C.Makes) (x : C.label D) (o : Site (C.side N p))
    (d : Descent (C.side N p) c)

include B in
lemma cyl_test : Testable d (C.O N p x o) := ⟨C.continuousO .., C.invariant B N p D x o,
  (observable_smooth C N p D x o).contDiffAt.comp (f := matrixField ∘ d.fine 1 ∘ d.tablePath) _
    (smooth_test d)⟩

-- translate to/from top section (`F` here no insertion eval by calibration expectation).
def fieldLabel (C : Family G) (N p : ℕ) {D : ℕ} (v : C.label D) : C.label D :=
    (C.factory D N p).terminal (((C.S.a N : ℂ)^D) • (C.labels.level D).scaled (C.path.levels.clock.threshold N) v)

theorem field_label_correct (v : C.label D) :
    C.O N p (fieldLabel C N p v) o = (C.localSection D).places v o := by
  let F := C.labels.level D; let r := C.path.levels.clock.threshold N
  have hr : 0 < r := (C.path.levels.budget N).threshold_pos
  unfold Family.O fieldLabel TransferData.cylinder
  rw [LinearEquiv.symm_apply_apply]
  let h := F.scaled_inv (inv_pos.mpr hr).ne' v
  rw [inv_inv] at h
  unfold initial; rw [map_smul, show F.scaled r⁻¹ (F.scaled r v)=v from h]
  funext i; simp only [SectionData.places,(C.localSection D).eval_linear.map_smul,Pi.smul_apply, smul_eq_mul]; rw [inv_mul_cancel_left₀]
  exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne')

-- directly prove lower slot order along rays
abbrev atFlat (G : Gauge) {o' : Side} (d : Descent o' c) (x : Coordinates G d) := d.fine 1 (d.tablePath x)
variable {c : Side}
private def coordinate (d : Descent n c) (s : RG.Slot) (o : Site n) (i : G.ColorIndex) (x : Coordinates G d) : ℂ :=
  Complex.ofReal ((s.atSite (atFlat G d x) o) i)

private lemma coordinate_order (d : Descent n c) (s : RG.Slot) (o : Site n) (i : G.ColorIndex) :
    RadialOrder 1 (coordinate d s o i) := by
  intro x
  obtain ⟨A,hA,h⟩ := Work.F03.slots_bound (topDir d x)
  let F (a : ℝ) := s.atSite (atFlat G d (a • x)) o
  have he : Tested.germ ≤ 𝓝[≠] 0 := nhdsWithin_mono _ fun t ht => ne_of_gt (show 0<t from ht)
  refine ⟨A,hA,?_⟩
  filter_upwards [h.filter_mono he,eventually_pos] with t ht hh
  have hi : ‖F t‖ ≤ A*t := by
    have hk: ‖t⁻¹ • F t‖ ≤ A := by
      unfold F atFlat; rw [path_top,map_smul]; exact ht o s
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hh.le, mul_comm, ← div_eq_mul_inv] at hk
    exact (div_le_iff₀ hh).mp hk
  rw [coordinate, pow_one, Complex.norm_real]
  have hf := abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ i) (F t)
  rw [OrthonormalBasis.norm_eq_one,one_mul, EuclideanSpace.basisFun_inner] at hf
  exact hf.trans hi

private lemma stencil_order (n c : Side) (d : Descent n c) {k w : ℕ} (R : Bid.Pose G k)
    (s : Fin k → RG.Slot) (h : Bid.lows R w) (o : Site n) :
    RadialOrder w (fun x => Bid.lumin R (Bid.mapped s (expandAt o (atFlat G d x)))) := by
  intro x
  let f (i : Fin k × G.ColorIndex) (t : ℝ) := coordinate d (s i.1) o i.2 (t • x)
  suffices H : Bill w (∑ j ∈ R.support, (fun t : ℝ => MvPolynomial.coeff j R * (∏ i ∈ j.support, (f i ^ j i)) t)) by
    convert! H using 1
    funext t
    dsimp only; rw [Bid.lumin,MvPolynomial.aeval_eq_eval₂Hom,MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_eq]
    simp only [Finset.sum_apply, Finset.prod_apply, Pi.pow_apply]; rfl
  apply bill_sum; intro j hj
  have H := (bill_product j.support j _ (fun i _ => (show Bill (j i) _ by
    simpa only [mul_one] using! bill_pow (coordinate_order d (s i.1) o i.2 x) (j i)))) -- metav
  exact bill_ge (bill_mul (bill_const (MvPolynomial.coeff j R)) H) (by simpa only [Nat.zero_add,Finsupp.sum] using h j hj)

-- at this point level D actual section fields
include B
theorem basis_test {c : Side} (hp : Bid.pop (C.localSection D)) (d : Descent (C.side N p) c)
    (o : Site (C.side N p)) (i : (C.labels.level D).Index) :
    d.Testable ((C.localSection D).places (Pi.single i 1) o) ∧
    d.grade ((C.localSection D).places (Pi.single i 1) o) ((C.labels.level D).grades i).2 := by
  refine ⟨?_,?_⟩
  · rw [← field_label_correct]; exact cyl_test B ..
  obtain ⟨k,S,-,R,hf,hl⟩ := hp i
  change RadialOrder _ (fun x => (C.localSection D).evaluate _ (expandAt o (atFlat G d x)))
  simp_rw [hf]; exact stencil_order _ _ d R S hl o
end YM.RGComparison.Core16.Descent
