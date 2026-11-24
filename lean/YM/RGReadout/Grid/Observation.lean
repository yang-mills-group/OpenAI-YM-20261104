import YM.RGReadout.Grid.Prices
import YM.OPE.Orbits.Kernel

/-!
# The primary literal grid scheme in the physical hierarchy

Pick once on a mesh-then-period extraction for *all* channels and scales
of this hierarchy. Full reference inverse survives; physical null fields
not asserted to follow zero before physical limits. On every admissible k
we get the actual full right inverse with explicit crude price. Also works
off-domain with padding (don't claim OPE estimates there).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGReadout.Literal
open Finset Function Filter Set MeasureTheory Analysis Wilson Lattice RG Source Extra.Histories
open MergeProof MergeProof.Accent MergeProof.Ribbons Trace.Physical Trace.Physical.GermGraph
open Overlay Work.G08 Bid Next.Rank Next.UVStress Price OPE
open Extraction Spec Dash
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {G : Gauge} {C : Family G} (H : C.Makes) (F : Extraction.Order)
variable {i : ℕ × ℕ} {d k : ℕ}
set_option quotPrecheck false
local notation "B" => C.labels.level d

def combo (z : ℕ × ℕ) (N p : ℕ) :=
  (flow C H z.1 z.2 (N,p), inflow C H z.1 z.2 (N,p))

abbrev ReaderCoordinates (C : Family G) :=
  (z : ℕ × ℕ) → (C.label z.1 →L[ℂ] C.label z.1) × (C.label z.1 →L[ℂ] C.label z.1)

/-- Off Opened and insufficiently deep cutoffs use specified padding.
    Positive conclusions only used where points *eventually fit*. -/
structure Fitted (x : ReaderCoordinates C) : Prop where
  gauge (z) : F.limits (fun _=>True) (combo H z) (x z)

lemma read_bank : ∃ f x, Fitted H (F.refine f) x := by
  let X : ℕ × ℕ → Type := fun z=> (C.label z.1 →L[ℂ] C.label z.1) × (C.label z.1 →L[ℂ] C.label z.1)
  let Q (z : ℕ × ℕ) := 1+normAllow C z.1 z.2 + normReverse C z.1 z.2
  have hQ (z : ℕ × ℕ) : 0 ≤ Q z := add_nonneg (add_nonneg zero_le_one (allow_pos ..).le) (reverse_pos ..).le
  have he (z : ℕ × ℕ) (N p : ℕ) : ‖combo H z N p‖ ≤ Q z := by
    rw [Prod.norm_def, max_le_iff]; exact
      ⟨(toll_out C H z.1 z.2 (N,p)).trans (le_add_of_nonneg_right (reverse_pos ..).le),
       (toll_in C H z.1 z.2 (N,p)).trans (add_le_add_left (le_add_of_nonneg_right (allow_pos ..).le) _)⟩
  have hg := Next.Extract.Reserve.of_norm (A:= fun (z : ℕ × ℕ) _ => True) (X:=X) (T:=combo H)
    (f:=F) (fun i=> Eventually.of_forall (fun _=>trivial))
    (fun i p _=> ⟨Q i,hQ _,Eventually.of_forall (fun _=>he ..)⟩)
    (fun i=> ⟨Q i,hQ _,Eventually.of_forall (fun _=> Eventually.of_forall (fun _=> he ..))⟩)
  obtain ⟨f,u,v,h⟩ := hg.gather
  exact ⟨f,v, ⟨fun i=>h.limits i⟩⟩

namespace Fitted
variable {H F} {x : ReaderCoordinates C} (h : Fitted H F x) (d k : ℕ)
include h
local notation "x~" => x (d,k)
lemma reference_up : Tendsto (flow C H d k) F.fuse (𝓝 (x (d,k)).1) := by
  have hf := Order.along (h.gauge (d,k))
  exact continuous_fst.continuousAt.tendsto.comp hf
lemma reference_back : Tendsto (inflow C H d k) F.fuse (𝓝 (x (d,k)).2) := by
  have hf := Order.along (h.gauge (d,k))
  exact continuous_snd.continuousAt.tendsto.comp hf
lemma inverse_price : ‖(x (d,k)).2‖ ≤ 1+normReverse C d k :=
  le_of_tendsto ((h.reference_back d k).norm) (Eventually.of_forall (fun i=>toll_in C H d k i))
lemma inverseL : LeftInverse (x (d,k)).2 (x (d,k)).1 := by
  intro y
  have he := Dash.arcing (h.reference_back d k) (Dash.arcing (h.reference_up d k) (tendsto_const_nhds (x:=y)))
  exact tendsto_nhds_unique_of_eventuallyEq he tendsto_const_nhds
    (Eventually.of_forall (fun i=> (dialRaw C H d k i).symm_apply_apply _))
lemma inverseR : RightInverse (x (d,k)).2 (x (d,k)).1 := by
  intro y
  have he := Dash.arcing (h.reference_up d k) (Dash.arcing (h.reference_back d k) (tendsto_const_nhds (x:=y)))
  exact tendsto_nhds_unique_of_eventuallyEq he tendsto_const_nhds
    (Eventually.of_forall (fun i=> (dialRaw C H d k i).apply_symm_apply _))
end Fitted

variable {H F} {x : ReaderCoordinates C} (h : Fitted H F x) (S : Table C.book) (d k : ℕ)

/-- The true fields. Will be read in unselected and every supported phase.
    S has additionally the calibration leases. -/
def master : C.label d →L[ℂ] S.Field d :=
  LinearMap.toContinuousLinearMap (S.project d) ∘L (_root_.id (fun _ : Fitted H F x => (x (d,k)).1) h)

def liftMaster : S.Field d →L[ℂ] C.label d :=
 (_root_.id (fun _ : Fitted H F x => (x (d,k)).2) h) ∘L LinearMap.toContinuousLinearMap (S.representative d)

lemma master_apply (w : C.label d) : master h S d k w = S.project d ((x (d,k)).1 w) := rfl
lemma lifted (w : S.Field d) : master h S d k (liftMaster h S d k w) = w := by
  change S.project d ((x (d,k)).1 ((x (d,k)).2 _))= w
  rw [h.inverseR d k]; exact S.rep ..
lemma lift_price : ‖liftMaster h S d k‖ ≤ (1+normReverse C d k)*
    ‖LinearMap.toContinuousLinearMap (S.representative d)‖ :=
  ContinuousLinearMap.opNorm_comp_le .. |>.trans (mul_le_mul_of_nonneg_right (h.inverse_price d k) (norm_nonneg _))
lemma lift_price_rate {ι : Type*} {l : Filter ι} {T : ι → ℝ} {v : ι → ℕ}
    (ht : Tendsto T l atTop) (hx : Height C.S l T v 1) :
    RateLE l T (fun i=>liftMaster h S d (v i)) (d:ℝ) := by
  have hd : (0:ℝ) ≤ d := Nat.cast_nonneg _
  apply RateLE.of_norm_le (F:=fun i=>liftMaster h S d (v i)) _ (Eventually.of_forall (fun i=>lift_price h S d _))
  have hc := ((((RateIs.const ht one_pos).add (reverse_rate C d ht hx) ht).pays ht).mul
    (RateLE.const ‖LinearMap.toContinuousLinearMap (S.representative d)‖ ht))
  simpa only [max_eq_right hd,add_zero] using hc

end YM.RGReadout.Literal
