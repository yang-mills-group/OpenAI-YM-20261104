import YM.Trace.Physicalv2.GermChain
import YM.FullVolume.Cross

/-! The signed one-mark graph difference on the original Wilson representations.
The incoming and outgoing graph coordinates are the actual germ readouts of
the same factory column. The physical kernel, frame, and forced divisor are
those of that family throughout. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section

namespace YM.Integration.ActualOneMarkGraphStep

open Filter MeasureTheory Lattice Wilson RG Source Labels
open Trace.Physical Trace.Physical.GermGraph
open PhysicalNext.Repeat.Legato
open Extra.Histories Extra.Histories.Relay Bid MergeProof
open scoped Topology Matrix.Norms.Frobenius

variable {G : Gauge} {C : Family G} {d N p i : ℕ}

local notation "σ" => (C.labels.level d).coeffSize
local notation "Q" => GermGraph.store C d p
local notation "V" => GermGraph.value (C := C) d N p
local notation "Y" => GermGraph.calValues (C := C) d N p
local notation "π" => GermGraph.page (C := C) d p
local notation "X" => GermGraph.measuring C d N p
local notation "U" => GermGraph.transition (C := C) d N p i
local notation "L" => GermGraph.factor C i

/-- The exact threshold-coordinate transfer and its inverse on the original family. -/
def forward (H : C.Makes) (hc : Opened C d i p) (hf : Opened C d (i+1) p)
    (hi : i<N) : C.label d ≃ₗ[ℂ] C.label d :=
  (fitting d N p (i+1) H hf hi).symm.trans (fitting d N p i H hc hi.le)

theorem forward_apply (H : C.Makes) (hc : Opened C d i p)
    (hf : Opened C d (i+1) p) (hi : i<N) (y : C.label d) :
    forward H hc hf hi (X (i+1) y) = X i y := by
  change (fitting d N p i H hc hi.le)
    ((fitting d N p (i+1) H hf hi).symm ((fitting d N p (i+1) H hf hi) y)) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

private theorem read_add {q v : Q i} {a b : ℝ}
    (hq : reads d N p i q a) (hv : reads d N p i v b) :
    reads d N p i (beside q v) (a+b) := presentation hq.1 hq.2 hv.1 hv.2

private theorem value_add (H : C.Makes) (hi : i≤N)
    {q v : Q i} {a b : ℝ} (hq : reads d N p i q a) (hv : reads d N p i v b) :
    V i (beside q v) = V i q + V i v :=
  plus (H.wilson.represents N p i hi).good hq.2 hv.2 (C.localSection d)

/-- On all large levels of one fixed Run the native transfer contracts complete
germ-null representatives, separately paying the physical canonical feed. -/
theorem gates (R : Run G) (hG : G.Simple) (d : ℕ) {γ ε : ℝ} (hγ : 0<γ) (hε : 0<ε) :
    ∀ᶠ t : ℕ in atTop, ∀ i≥t, ∀ p N : ℕ, i<N →
      (Opened R.family d i p ∧ Opened R.family d (i+1) p) ∧
      Gate R.family d N p i γ ε := by
  let H := R.family.path
  have bought := R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors
    R.makes R.carries R.books
  obtain ⟨_, tabs, accounting, _, _, _, _⟩ := bought
  have materials : Ribbons.Materials R.family :=
    ⟨hG, R.makes, ⟨H, R.t, R.stories, rfl⟩, tabs, _, R.doors, _, _, _, accounting,
      (R.again hG).1.scrim⟩
  exact message_graph R.family d materials hγ hε

/-- The model defect is represented on the actual coarse vacuum. The output
contains the physical stable transmission, the signed model defect, and the
model applied to the difference of the formal and actual forward matrices.
The formal chart is only required to be additive on physical densities. -/
theorem local_step (H : C.Makes) (hi : i<N) (hc : Opened C d i p)
    {γ ε K r b : ℝ} (gate : Gate C d N p i γ ε) (hK : 0≤K)
    (y : C.label d) (fine : Q (i+1)) (coarse : C.label d → Q i)
    (M : C.label d →ₗ[ℂ] C.label d)
    (hcoarse : ∀ x, reads d N p i (coarse x) (K * σ x))
    (hproj : ∀ x, π i (coarse x) = x)
    (hadd : ∀ u v, V i (coarse (u+v)) = V i (coarse u) + V i (coarse v))
    (q : Q (i+1)) (hq : reads d N p (i+1) q r) (hnull : π (i+1) q = 0)
    (hinput : Y (i+1) y = V (i+1) fine + V (i+1) q)
    (e : Q i) (he : reads d N p i e b) (hec : σ e.x ≤ b)
    (hdef : U (V (i+1) fine) = V i (coarse (M (X (i+1) y))) + V i e) :
    let u := X (i+1) y
    let x := X i y
    let loss := L ^ (-GermGraph.rate)
    σ (x-M u) ≤ ε*r*loss + 2*b ∧
    ∃ s : Q i, reads d N p i s
        (loss*r + 2*stock C i*(ε*r*loss) + b + K*(ε*r*loss + 2*b)) ∧
      π i s = 0 ∧
      V i s = U (V (i+1) q) + V i e + V i (coarse (M u-x)) ∧
      Y i y = V i (coarse x) + V i s := by
  intro u x loss
  obtain ⟨v, z, hv, hv0, hz, htrans⟩ := gate.2 q r hq hnull
  let f := (C.factory d N p).entries i z
  have hf := graph_cost d N p i H hc hi.le z
  have hgain : 0 < L ^ GermGraph.rate :=
    Real.rpow_pos_of_pos (zero_lt_one.trans (factor_positive C i)) _
  have hfeed : σ (X i z) ≤ ε*r*loss := by
    rw [show loss = (L^GermGraph.rate)⁻¹ from
      Real.rpow_neg (zero_lt_one.trans (factor_positive C i)).le _, ← div_eq_mul_inv]
    exact (le_div_iff₀ hgain).mpr (by simpa only [mul_comm (σ (X i z))] using hz)
  let a := beside v f
  have ha := read_add hv hf
  have hval : V i a = U (V (i+1) q) := (value_add H hi.le hv hf).trans htrans.symm
  have hpage : π i a = X i z := by
    rw [show a = beside v f from rfl, addPage d N p i v f H hc.post hi.le hv hf, hv0,
      zero_add]
  let total := beside (beside (coarse (M u)) e) a
  have hclaim := read_add (read_add (hcoarse (M u)) he) ha
  have hqi := message d N p (i+1) H (hc.post.trans i.le_succ) hi hq
  have hyi := message d N p (i+1) H (hc.post.trans i.le_succ) hi
    (entryOk d N p (i+1) H (hc.post.trans i.le_succ) hi y)
  have hfi : Integrable (V (i+1) fine) (prior G _) := by
    have hsub : Y (i+1) y - V (i+1) q = V (i+1) fine := by rw [hinput]; abel
    rw [← hsub]
    exact hyi.sub hqi
  have htotal : Y i y = V i total := by
    rw [factory_eq d N p i H hc.post hi y, hinput, transition_add d N p hfi hqi, hdef,
      ← hval]
    exact ((value_add H hi.le (read_add (hcoarse (M u)) he) ha).trans
      (congrArg (· + V i a) (value_add H hi.le (hcoarse (M u)) he))).symm
  have hp := same_page H hi.le hc.post (entryOk d N p i H hc.post hi.le y) hclaim
    (Filter.EventuallyEq.of_eq htotal)
  change x = π i (beside (beside (coarse (M u)) e) a) at hp
  rw [addPage d N p i _ _ H hc.post hi.le (read_add (hcoarse (M u)) he) ha,
    addPage d N p i _ _ H hc.post hi.le (hcoarse (M u)) he, hproj, hpage] at hp
  have hm : x-M u = π i e + X i z := by rw [hp]; abel
  have hmatrix : σ (x-M u) ≤ ε*r*loss + 2*b := by
    rw [hm]
    exact (Size.add _ _ _).trans ((add_le_add (control_page H hc hi.le e he hec)
      hfeed).trans_eq (add_comm _ _))
  let w := M u-x
  let s := beside (beside a e) (coarse w)
  have hws : σ w ≤ ε*r*loss + 2*b := by
    rw [show w = -(x-M u) from (neg_sub x (M u)).symm, count_neg]
    exact hmatrix
  have hs := read_add (read_add ha he) (hcoarse w)
  have hbill : reads d N p i s
      (loss*r + 2*stock C i*(ε*r*loss) + b + K*(ε*r*loss + 2*b)) := by
    have stock_nonneg : 0 ≤ 2*stock C i :=
      mul_nonneg zero_le_two (zero_le_one.trans (stage C i).columns_ge)
    have hcost := mul_le_mul_of_nonneg_left hfeed stock_nonneg
    refine ⟨hs.1, rem_increase d hs.2 ?_⟩
    exact add_le_add (add_le_add (add_le_add le_rfl hcost) le_rfl)
      (mul_le_mul_of_nonneg_left hws hK)
  have hs0 : π i s = 0 := by
    rw [show s = beside (beside a e) (coarse w) from rfl,
      addPage d N p i _ _ H hc.post hi.le (read_add ha he) (hcoarse w),
      addPage d N p i _ _ H hc.post hi.le ha he, hproj, hpage]
    dsimp only [w]
    rw [hp]
    abel
  have hsv : V i s = U (V (i+1) q) + V i e + V i (coarse w) := by
    rw [show s = beside (beside a e) (coarse w) from rfl,
      value_add H hi.le (read_add ha he) (hcoarse w), value_add H hi.le ha he, hval]
  refine ⟨hmatrix, s, hbill, hs0, hsv, ?_⟩
  have hvw : V i (coarse (M u)) = V i (coarse x) + V i (coarse w) := by
    rw [← hadd, show x+w = M u from add_sub_cancel x (M u)]
  rw [htotal, show total = beside (beside (coarse (M u)) e) a from rfl,
    value_add H hi.le (read_add (hcoarse (M u)) he) ha, value_add H hi.le (hcoarse (M u)) he,
    hval, hsv, hvw]
  abel

end YM.Integration.ActualOneMarkGraphStep
end
