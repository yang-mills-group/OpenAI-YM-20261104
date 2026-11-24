import YM.FormalOPE.RG10.Ward.Quotient
import YM.FormalOPE.RG10.Ward.Rotation

/-! # Symmetry action on the PT census before choosing any measuring frames

Construction labels and grades. Don't assert equality on separately chosen representatives even
if canonical projections match. Include all actual derivative/profile operands (when taking
combinations, transport them with these fields). This proof doesn't extend signed axes to an O4
group on the lattice or the quotient torus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.InversionWard
open Gauge Lattice RG Wilson MeasureTheory Metric Finset
open PertExtension PertExtension.Chart PertExtension.Orb Function Filter InversionTop PowerSeries BRST
open YM.PertExtension.Series YM.PertExtension.Series.Radial YM.PertExtension.Series.Tested
open Marker Extra.Trajectories
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {n : Side} (hn : Even n.val) (s : Signed) {u : Site n} (hu : -u=u)
namespace Rotation

local notation "F" => feed (G:=G) hn
local notation "W" => vertices G n

include hu hn in
lemma phase {A B : Config G n → ℝ} (hA : PreTest A) (hB : PreTest B) (h : B=A ∘ pull s u) :
    replyCoeff B = replyCoeff A := by
  unfold replyCoeff; rw [show diag (restrictedO B) = diag (restrictedO A) from
    unique_wilson (u:=preExpectation B) (v:=preExpectation A)
      (.of_eq (by rw [h, beforeTurn hn s hu hA.continuous]))
      (before_tree_formula hn (traySpec G) hB) (before_tree_formula hn (traySpec G) hA)]

variable {V : Type*} {A B : V → Stamp G n}
include hu hn in
lemma transports (v : Finset V) (h : ∀ i∈v, (B i).stencil = (A i).stencil ∘ pull s u)
    (hp : ∀ i∈v, (B i).slots=(A i).slots) :
    (F).ordinary W v (Stamp.factors B) = (F).ordinary W v (Stamp.factors A) := by
  rw [Stamp.orbit_coeff, Stamp.orbit_coeff, show Stamp.degrees B v = Stamp.degrees A v from
    Finset.sum_congr rfl hp]
  exact congr_arg (lower _) (phase hn s hu (Stamp.pre_all A _) (Stamp.pre_all B _) (by
    funext U; unfold Stamp.shafts; simp only [Function.comp_apply, Finset.prod_apply];
    exact Finset.prod_congr rfl fun i hi => congr_fun (h i hi) U))

include hu hn in
lemma commute_turn {V : Type} [Fintype V] [DecidableEq V] (R : Census V) (A B : V→Stamp G n)
    (h : ∀ i, (B i).stencil = (A i).stencil ∘ pull s u) (hp : ∀ i, (B i).slots=(A i).slots) :
    (F).contraction W (publish R B) = (F).contraction W (publish R A) := by
  apply congr_arg Word.logWord; apply Word.observe_ext; intro m
  exact ((F).closing_emission W R (Stamp.factors B) m).trans ((transports hn s hu m.val (fun i _=>h i)
    (fun i _=>hp i)).trans ((F).closing_emission W R _ m).symm)

open Source Labels PertExtension.Orb.SlotEvaluation
variable {k : ℕ} {R : Labels.Frame G k} {S : SectionData R} {H : Hol G}
lemma compare {i j : R.Index} (h : R.grades i ≠ R.grades j) :
    R.act s.ortho (Pi.single i 1) j = 0 := by
  have hp : Labels.tensor s.ortho (R.basis i) ∈ Grade (R.grades i) := by
    have hx := gradePart_mem (R.grades i) (Labels.tensor s.ortho (R.basis i));
    rwa [gradePart_turn, gradePart_self (R.basis i) _ (R.pure i)] at hx
  rw [← R.coords_basis i, R.act_coords]; exact R.power_coefficient j h hp

variable (u) in
def pullField (S : SectionData R) (i : R.Index) (o : Site n) := SlotEvaluation.fieldAt S i o ∘ pull s u

private lemma basis_series (o : Site n) (v : R.Coeff) (S : SectionData R) :
    S.places v o = ∑ i, v i • S.places (Pi.single i 1) o := by
  funext U
  let L := S.eval_linear.mk' _
  change L v _ = _
  have hm : v=∑ i:R.Index, v i • (Pi.single i 1:R.Coeff) := by
    funext i
    rw [Finset.sum_apply, sum_eq_single i];
    · simp
    · intro j _ hj; simp [Pi.single_eq_of_ne (Ne.symm hj)]
    simp
  calc
    _ = L (∑ i:R.Index, v i • (Pi.single i 1:R.Coeff)) (expandAt o U) := by rw [← hm]
    _ = _ := by rw [map_sum]; simp_rw [Finset.sum_apply, map_smul]; rfl

lemma reorders (hs : S.Sound H) (i:R.Index) (o : Site n) : pullField s u S i o =
    ∑ j : R.Index with R.grades i=R.grades j, ((R.act s.ortho (Pi.single i 1) j).re) • SlotEvaluation.fieldAt S j (affine s u o) := by
  funext U; unfold pullField fieldAt; simp only [Function.comp_apply, S.placed_signed hs]
  rw [basis_series _ _ S, Finset.sum_apply, Complex.re_sum]; symm; rw [Finset.sum_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl; intro j _
  split
  · have hp := SlotEvaluation.scalar_real (C:=S) (H:=H) hs (i:=j) (o:=affine s u o) (u:=U)
    simp only [Pi.smul_apply,smul_eq_mul,← hp]; simp
  rename_i hh; rw [Rotation.compare _ hh]; simp

-- admissible stamp for a transformed label.
variable (p : Bid.pop S) (hs : S.Sound H) (u)
def asStamp (i : R.Index) (o : Site n) : Stamp G n where
  stencil := pullField s u S i o
  slots := (R.grades i).2
  test := by
    rw [reorders s hs]
    apply Proxy.active
    · apply Proxy.sum; intro j hj; exact ((field_proxy R S (Pi.single j 1) (affine s u o)).after _ Complex.reCLM.contDiff).const_smul _
    intro t ht U; rw [Finset.sum_apply,Finset.sum_apply]; apply sum_congr rfl; intro j hj
    rw [Pi.smul_apply, (pre_field S hs p ..).1.gauge t ht U]; rfl
  cleared j hj := by
    apply weightFloor.wipes (f:=pullField s u S i o) _ _ hj
    · rw [reorders s hs]; apply weightFloor.unpaid; intro a ha x
      have h := (mem_filter.mp ha).2
      let f := fun i => SlotEvaluation.fieldAt S i (affine s u o)
      have he : Bill (R.grades a).2 (fun r:ℝ=> f a (representative (r • x))) := (pre_field S hs p a _).2 x
      rw [h]; simpa only [Nat.zero_add] using! bill_mul (bill_const ((R.act s.ortho (Pi.single i 1) a).re)) he
    rw [reorders s hs]; apply Proxy.sum; intro j hj; exact ((field_proxy R S (Pi.single j 1) (affine s u o)).after _ Complex.reCLM.contDiff).const_smul _

-- separate use `commute_turn` with same t on every slot, feed these stamps.
theorem export_stamp (i : R.Index) (o : Site n) :
    (asStamp s u p hs i o).stencil=(Stamp.native o hs p i).stencil ∘ pull s u ∧
    (asStamp s u p hs i o).slots=(Stamp.native o hs p i).slots := ⟨rfl,rfl⟩
end Rotation
end YM.FormalOPE.RG10.InversionWard
