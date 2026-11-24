import YM.Integration.WilsonReceivedAxialExtension
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! The original finitely many source locations share one small group
configuration. A connected chain of overlapping physical boxes uses a
single existing axial gauge, and different chains use disjoint link tails. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonJointAxialWindow
open Finset Lattice Wilson RG Ac Marker QuadraticLocal Source Labels MSbar.Heath
open IterationFour PhysicalNext.Repeat.Legato OPE.Therm WilsonRootedKioskOccupiedSlip
open scoped Classical BigOperators Topology
variable {n : Side} {V : Type} [Fintype V]

private def overlaps (o : V → Site n) (h : ℕ) : SimpleGraph V where
  Adj v w := v ≠ w ∧ separation (o v) (o w) ≤ 2*h
  symm := ⟨fun v w hit => ⟨hit.1.symm,(separation_comm (o v) (o w)) ▸ hit.2⟩⟩
  loopless := ⟨fun _ hit => hit.1 rfl⟩

omit [Fintype V] in
private theorem walk_bound (o : V → Site n) (h : ℕ) {v w : V} (P : (overlaps o h).Walk v w) :
    separation (o v) (o w) ≤ P.length*(2*h) := by
  induction P with
  | nil => simp
  | @cons x y z edge tail bound =>
    calc
      _ ≤ separation (o x) (o y) + separation (o y) (o z) := separation_triangle _ _ _
      _ ≤ 2*h + tail.length*(2*h) := Nat.add_le_add edge.2 bound
      _ = _ := by simp [Nat.add_mul,Nat.add_comm]

/-- The same representative is used wherever the small boxes overlap.
Every member of its component is inside one larger lifted chart. -/
private theorem representatives (o : V → Site n) (h : ℕ) :
    ∃ c : V → V,(∀ v,separation (o (c v)) (o v) ≤ Fintype.card V*(2*h)) ∧
      ∀ v w x,separation (o v) x<h → separation (o w) x<h → c v=c w := by
  let K := overlaps o h
  have onto : Function.Surjective K.connectedComponentMk := Quot.mk_surjective
  let pick (C : K.ConnectedComponent) := (onto C).choose
  let c (v : V) := pick (K.connectedComponentMk v)
  refine ⟨c,?_,?_⟩
  · intro v
    have reach : K.Reachable (c v) v :=
      SimpleGraph.ConnectedComponent.exact ((onto (K.connectedComponentMk v)).choose_spec)
    obtain ⟨P,short⟩ := reach.exists_isPath
    exact (walk_bound o h P).trans (Nat.mul_le_mul_right _ short.length_lt.le)
  · intro v w x nearV nearW
    by_cases eq : v=w
    · exact congrArg c eq
    have backward : separation x (o w)<h := (separation_comm (o w) x) ▸ nearW
    have adjacent : K.Adj v w := ⟨eq,(separation_triangle (o v) x (o w)).trans (by omega)⟩
    exact congrArg pick (SimpleGraph.ConnectedComponent.sound adjacent.reachable)

private theorem ray_healthy {G : Gauge} {p : BudgetPoint} (J : Voice G) (clear : Clear G J)
    {r z : ℝ} (hb : r*p.threshold ≤ J.r) (stay : 4*J.C*r ≤ 1) (hz : z ∈ Set.Icc (0:ℝ) r)
    (D : Directions G n) (bound : ∀ e, ‖D e‖ ≤ p.threshold) (Y : Support n) :
    Healthy p.threshold Y (increment 1 (z • D)) := by
  let W := increment (1 : Config G n) (z • D)
  have cost (e : Edge (Site n)) : G.chord (W e*((1:Config G n) e)⁻¹) ≤ J.C*(r*p.threshold) := by
    have d : ‖z • D e‖ ≤ r*p.threshold := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hz.1]
      exact mul_le_mul hz.2 (bound e) (norm_nonneg _) (hz.1.trans hz.2)
    simpa only [W,increment,Pi.one_apply,Pi.smul_apply,inv_one,mul_one] using
      ((clear.small (z • D e) (d.trans hb)).2.trans
        (mul_le_mul_of_nonneg_left d (zero_le_one.trans clear.cost)))
  apply Finset.disjoint_left.mpr
  intro x _ flag
  obtain ⟨b,_,bad⟩ := (flags_spec _ _ x).mp flag
  have ps := WilsonRegisteredAffineForest.plaquette (1 : Config G n) W cost b
  have flat : faceValue (1 : Config G n) b=1 := by simp [faceValue,square]
  rw [flat,G.chord_one,zero_add] at ps
  apply (not_lt_of_ge (ps.trans _)) bad
  calc
    _ = (4*J.C*r)*p.threshold := by ring
    _ ≤ 1*p.threshold := mul_le_mul_of_nonneg_right stay p.threshold_pos.le
    _ = _ := one_mul _

open MeasureTheory

/-- Assign overlapping boxes one common origin, using only the enrolled positions. -/
def centre (o : V → Site n) (h : ℕ) : V → V := (representatives o h).choose

/-- The global test direction is the original axially gauged link on the
union of the charged boxes. Its definition applies also on failed fields. -/
def direction {G : Gauge} (o : V → Site n) (h : ℕ) (J : Voice G) (axes : Lattice.Order)
    (r : ℝ) (U : Config G n) : Directions G n := fun e =>
  if k : ∃ v,separation (o v) e.1<h then
    r⁻¹ • J.decode ((Lattice.gauge (WilsonAxialWindow.frame axes (o (centre o h k.choose)) U) U) e)
  else 0

theorem measurable_direction {G : Gauge} (o : V → Site n) (h : ℕ) (J : Voice G)
    (clear : Clear G J) (axes : Lattice.Order) (r : ℝ) :
    Measurable (direction o h J axes r) := by
  apply measurable_pi_lambda
  intro e
  unfold direction
  split_ifs with k
  · have fr (v y : Site n) : Continuous (fun U : Config G n => WilsonAxialWindow.frame axes v U y) := by
      unfold WilsonAxialWindow.frame Axial.traveller expandAt
      fun_prop
    have gauged : Continuous (fun U : Config G n =>
        (Lattice.gauge (WilsonAxialWindow.frame axes (o (centre o h k.choose)) U) U) e) := by
      unfold Lattice.gauge
      fun_prop
    exact (clear.reads.comp gauged.measurable).const_smul r⁻¹
  · exact measurable_const

theorem selected {G : Gauge} {p : BudgetPoint} (o : V → Site n)
    (J : Voice G) (clear : Clear G J) (axes : Lattice.Order) (h H : ℕ)
    (contains : Fintype.card V*(2*h)+h ≤ H) (room : 2*H<n.val)
    {τ r : ℝ} (weak : 0 ≤ τ) (rp : 0 < r) (U : Config G n)
    (cold : ∀ v,U ∈ House.chilly (WilsonAxialWindow.cells (o v) H) τ)
    (small : (4*(H:ℝ)*Fintype.card PlaqAxes)*τ ≤ J.δ)
    (logarithm : J.C*((4*(H:ℝ)*Fintype.card PlaqAxes)*τ) ≤ r*p.threshold)
    (radius : r*p.threshold ≤ J.r) (stay : 4*J.C*r ≤ 1) :
    let ξ := direction o h J axes r U
    (∀ e, ‖ξ e‖ ≤ p.threshold) ∧
      (∀ z ∈ Set.Icc (0:ℝ) r,∀ Y : Support n,Healthy p.threshold Y (increment 1 (z • ξ))) ∧
      ∀ (v : V) {Y : Support n} {F : Config G n → ℂ},p.Regular Y F →
        (∀ x∈Y,separation (o v) x<h) → F U = F (increment 1 (r • ξ)) := by
  classical
  intro ξ
  obtain ⟨range,same⟩ := (representatives o h).choose_spec
  let c := (4*(H:ℝ)*Fintype.card PlaqAxes)*τ
  have represented (e : Edge (Site n)) (k : ∃ v,separation (o v) e.1<h) :
      G.chord ((Lattice.gauge (WilsonAxialWindow.frame axes (o (centre o h k.choose)) U) U) e) ≤ c := by
    have far : separation (o (centre o h k.choose)) e.1 < H :=
      (separation_triangle _ (o k.choose) _).trans_lt
        ((Nat.add_lt_add_of_le_of_lt (range k.choose) k.choose_spec).trans_le contains)
    exact WilsonAxialWindow.bound axes _ U H room e far weak (cold _)
  have bound (e) : ‖ξ e‖ ≤ p.threshold := by
    by_cases k : ∃ v,separation (o v) e.1<h
    · have decoded := (clear.near _ ((represented e k).trans small)).2.2
      have size := (mul_le_mul_of_nonneg_left (represented e k) (zero_le_one.trans clear.cost)).trans logarithm
      have full := decoded.trans size
      rw [show ξ e = r⁻¹ • J.decode ((Lattice.gauge (WilsonAxialWindow.frame axes
          (o (centre o h k.choose)) U) U) e) by simp only [ξ,direction,dif_pos k],
        norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr rp)]
      simpa only [←mul_assoc,inv_mul_cancel₀ rp.ne',one_mul] using mul_le_mul_of_nonneg_left full (inv_pos.mpr rp).le
    · simp only [ξ,direction,dif_neg k,norm_zero]
      exact p.threshold_pos.le
  refine ⟨bound, fun z hz => ray_healthy J clear radius stay hz ξ bound,?_⟩
  intro v Y F legal located
  rw [←legal.symmetry (WilsonAxialWindow.frame axes (o (centre o h v)) U) U]
  apply legal.sites
  intro e he _
  have k : ∃ v,separation (o v) e.1<h := ⟨v,located e.1 he⟩
  have centres : centre o h k.choose = centre o h v := same _ _ _ k.choose_spec (located e.1 he)
  have actual := (clear.near _ ((represented e k).trans small)).2.1
  change (Lattice.gauge (WilsonAxialWindow.frame axes (o (centre o h v)) U) U) e =
    G.lieExp (r • ξ e) * 1
  simp only [ξ,direction,dif_pos k,smul_smul,mul_inv_cancel₀ rp.ne',one_smul,mul_one]
  simpa only [centres] using actual.symm

/-- For the entire original roster the same capped angular field preserves
every gauge-invariant observable supported in one of the indicated boxes.
No condition is placed on the exterior of their enlarged plaquette boxes. -/
theorem chart {G : Gauge} {p : BudgetPoint} (o : V → Site n)
    (J : Voice G) (clear : Clear G J) (axes : Lattice.Order) (h H : ℕ)
    (contains : Fintype.card V*(2*h)+h ≤ H) (room : 2*H<n.val)
    {τ r : ℝ} (weak : 0 ≤ τ) (rp : 0 < r) (U : Config G n)
    (cold : ∀ v,U ∈ House.chilly (WilsonAxialWindow.cells (o v) H) τ)
    (small : (4*(H:ℝ)*Fintype.card PlaqAxes)*τ ≤ J.δ)
    (logarithm : J.C*((4*(H:ℝ)*Fintype.card PlaqAxes)*τ) ≤ r*p.threshold)
    (radius : r*p.threshold ≤ J.r) (stay : 4*J.C*r ≤ 1) :
    ∃ ξ : Directions G n,(∀ e, ‖ξ e‖ ≤ p.threshold) ∧
      (∀ z ∈ Set.Icc (0:ℝ) r,∀ Y : Support n,Healthy p.threshold Y (increment 1 (z • ξ))) ∧
      ∀ (v : V) {Y : Support n} {F : Config G n → ℂ},p.Regular Y F →
        (∀ x∈Y,separation (o v) x<h) → F U = F (increment 1 (r • ξ)) := by
  exact ⟨direction o h J axes r U,
    selected o J clear axes h H contains room weak rp U cold small logarithm radius stay⟩

end YM.Integration.WilsonJointAxialWindow
