import YM.RG3.Press.Vacuum
import YM.RG3.Letters.Orbit
/-!
# Full meridian from change-of-representation engine to Press system
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Press
open Lattice Wilson RG Overlay Extra.Trajectories Marker Finset Function MeasureTheory Ac Push.Corrected Push.AbsoluteSums
open scoped Topology BigOperators Matrix.Norms.Frobenius
open RG3.Ink
variable {n : Side} {G : Gauge} {ι μ : Type*}
variable {V : Type*} [DecidableEq V] {R : Census V} {p : BudgetPoint} {v : V → Site n}
variable {W : Shelf G n ι μ} (X : W.Stock p R v)

def stamp : Article W.Patch p G R v := ⟨Shelf.Stock.cargoAddr W p,X.cargo⟩

@[simp] theorem stamp_span (i : W.Patch) : (stamp X).span i=W.frame.ground i := rfl
@[simp] theorem stamp_inv (i : W.Patch) : (stamp X).inv i=W.frame.owns i := rfl
@[simp] theorem stamp_cluster (U) : (stamp X).cluster U=∑' s,X.pack U s := by
  rfl

-- use `[Countable ι]` from hosting not for checks; Article.Sound itself
-- addresses extratest at any α, finite individual checks.
theorem stamped (hB : ∀ i, MeasurableSet {U | (W.hard i).extraTest U})
    (hG : ∀ i t U, (W.hard i).extraTest (Lattice.gauge t U) ↔ (W.hard i).extraTest U)
    (hE : ∀ i, UsesFinal p.threshold (W.hard i).support (W.hard i).extraTest)
    (hr : ∀ i U, ((X.ink i U).part R.quiet).im=0) : (stamp X).Sound := by
  refine ⟨X.localCargo, X.cargo_eligible, fun i U => ?_,fun c => (Shelf.Stock.checks W p hB hG hE c).1,
    fun c => (Shelf.Stock.checks W p hB hG hE c).2.1, fun c => (Shelf.Stock.checks W p hB hG hE c).2.2⟩
  classical
  change ((W.frame.merged (flags p.threshold U) (fun i => X.ink i U) i).part R.quiet).im=0
  unfold Letters.Frame.merged; split
  · let q := W.frame.letters i
    have he (s : Finset (ι ⊕ μ)) : ((∏ j∈s,X.ink j U).part R.quiet).im=0 := by
      induction s using Finset.induction_on with
      | empty => simp
      | insert j s hj ih => simp only [prod_insert hj,Poly.quiet_mul,Complex.mul_im,hr j U,ih,mul_zero,zero_mul,add_zero]
    exact he q
  rfl

theorem budget {g : ι ⊕ μ → Poly R} {w γ χ} (hw : ∀ i,0 < w i) (hχ : 1 ≤ χ) (hγ : 0 ≤ γ)
    (hH : Hit W.frame.read p.B (W.frame.pump (fun i => Poly.price w (g i)) χ) (p.supportExponent+1) γ)
    (hgreen : (p.B+p.B+1:ℕ)^4*(γ:ℝ) ≤ 1) (hg : ∀ i U, Width.Covered (X.ink i U) (g i)) :
    (stamp X).Budget w ((Real.exp γ-1)/χ) := ⟨_,X.covered hg,Shelf.Stock.bought W hw p.exponent_pos.le hχ hγ hH hgreen⟩

/-- A change of unmarked presentation needs rotation/translation even at
zero entries. Carry the original eligibility tests, not just their supports.
Ingredient e/f may be arbitrary atlas key bijections (e.g. support-aggregation
classes including inert slots). -/
theorem spiral (s : Signed) (b : Site n) (e : Equiv.Perm ι) (f : Equiv.Perm μ)
    (he : ∀ i,(W.hard (e i)).support=(W.hard i).support.image (affine s b))
    (he' : ∀ i,(W.hard (e i)).inventory=(W.hard i).inventory.image (affine s b))
    (hb : ∀ i U,(W.hard (e i)).extraTest U ↔ (W.hard i).extraTest (pull s b U))
    (hf : ∀ i,W.shade (f i)=(W.shade i).image (affine s b))
    (hr : ∀ (i : ι⊕μ) U,(X.ink ((e.sumCongr f) i) U).part R.quiet=(X.ink i (pull s b U)).part R.quiet) :
    Nonempty ((stamp X).Spin s b) := by
  classical
  let u := e.sumCongr f
  let y : Equiv.Perm (Site n) := s.actEquiv.toEquiv.trans (Equiv.addRight b)
  have hy i : W.frame.read (u i) = (W.frame.read i).image y := by cases i <;> first | exact he _ | exact hf _
  have ht (i) : W.frame.need (u i) = (W.frame.need i).image y := by
    cases i with
    | inl i => exact he' _
    | inr i => exact image_empty _ |>.symm
  let j := W.frame.whirl u y hy ht
  have ha (c : W.Patch) : (stamp X).span (j c)=((stamp X).span c).image (affine s b) :=
    W.frame.spin_ground u y hy ht c
  have hk (c : W.Patch) : (stamp X).inv (j c)=((stamp X).inv c).image (affine s b) :=
    W.frame.spin_owns u y hy ht c
  have hh c : W.frame.letters (j c) = (W.frame.letters c).map u.toEmbedding := rfl
  refine ⟨j,ha,hk,fun c U => ?_,fun c U => ?_⟩
  · change (∀ i, Sum.inl i ∈ W.frame.letters (j c) → _) ↔ (∀ i, Sum.inl i ∈ W.frame.letters c → _)
    rw [hh]
    have hl i := Work.H03.eligible_send s b p.threshold U _ _ (he i) (he' i) (hb i U)
    constructor
    · intro H i hx; apply (hl i).mp
      exact H (e i) (mem_map.mpr ⟨.inl i,hx,rfl⟩)
    intro H i hi
    obtain ⟨l,hl',he⟩ := mem_map.mp hi
    rcases l with i'|i'
    swap; contradiction
    obtain rfl := Sum.inl.inj he; exact (hl i').mpr (H i' hl')
  have hs : W.frame.ground (j c)∩ flags p.threshold U = W.frame.owns (j c) ↔
      W.frame.ground c∩ flags p.threshold (pull s b U)= W.frame.owns c := by
    have haff : Injective (affine s b) := y.injective
    rw [show W.frame.ground (j c)=_ from ha c, ← Work.H03.flags_send s b p.threshold U, ← image_inter _ _ haff,
      show W.frame.owns (j c)=_ from hk c, (image_injective haff).eq_iff] -- affine vs y
    rfl
  change ((W.frame.merged (flags p.threshold U) (fun i => X.ink i U) (j c)).part R.quiet)=(W.frame.merged (flags p.threshold (pull s b U)) (fun i => X.ink i (pull s b U)) c).part R.quiet
  unfold Letters.Frame.merged; split_ifs with h h' h'
  · rw [hh,prod_map]
    let Q : Poly R →* ℂ := { toFun := fun x => x.part R.quiet, map_one' := by simp, map_mul' := fun _ _=> Poly.quiet_mul .. }
    change Q (∏ x ∈ W.frame.letters c, X.ink (u x) U)= Q (∏ x ∈ W.frame.letters c, X.ink x (pull s b U))
    simp only [map_prod]
    exact prod_congr rfl fun i _ => hr i U
  · exact (h' (hs.mp h)).elim
  · exact (h (hs.mpr h')).elim
  rfl

end YM.RG3.Press
