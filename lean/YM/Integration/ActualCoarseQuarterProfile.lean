import YM.Lattice.Scale
import YM.MS.Fleet.Place
import YM.MS.Tide.Cost
import YM.Extraction.Inherited

/-!
Quarter-period geometry for the actual schedule and a candidate coarse-scale
profile on the original mesh-then-period filter, followed by the coarse limit.
The profile is not identified here with the actual effective-action supplier.
No bank, fee, measure-transport, RG-equivariance or r-to-coarse-scale claim is made.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualCoarseQuarterProfile

open Filter Lattice
open scoped Topology

abbrev Cutoffs := ℕ × (ℕ × ℕ)

def quarterIndex (S : Schedule) (m p : ℕ) : ℕ :=
  (S.side m p).val / 4 - 1

def halfSide (S : Schedule) (m p : ℕ) : Side :=
  MS.Fleet.walkway (quarterIndex S m p)

def head (S : Schedule) (m p : ℕ) : Cover :=
  fun i => if i = 0 then ((S.side m p).val / 4 : ℕ) else 0

def site (S : Schedule) (m p : ℕ) : Site (S.side m p) :=
  wrap (S.side m p) (head S m p)

private theorem quarter_pos (S : Schedule) (m p : ℕ) :
    1 ≤ (S.side m p).val / 4 := by
  have h4 : 4 ≤ (S.side m p).val :=
    Nat.le_of_dvd (S.side m p).property (S.side_four m p)
  omega

theorem dimension (S : Schedule) (m p : ℕ) :
    MS.Orbit.periodN (halfSide S m p) = S.side m p := by
  apply Subtype.ext
  change (MS.Orbit.dimT MS.Fleet.walkway (quarterIndex S m p)).val =
    (S.side m p).val
  rw [MS.Fleet.fullC]
  have hd := Nat.div_mul_cancel (S.side_four m p)
  have hp := quarter_pos S m p
  unfold quarterIndex
  omega

theorem head_native (S : Schedule) (m p : ℕ) :
    head S m p = MS.Fleet.crane (quarterIndex S m p) := by
  funext i
  unfold head MS.Fleet.crane quarterIndex
  split_ifs
  · exact_mod_cast (show (S.side m p).val / 4 =
        (S.side m p).val / 4 - 1 + 1 by have := quarter_pos S m p; omega)
  · rfl

theorem head_scaled (S : Schedule) {m N : ℕ} (hmN : m ≤ N) (p : ℕ) :
    head S N p = (S.toDepth hmN p).count.val • head S m p := by
  have hq : (S.side N p).val / 4 =
      (S.toDepth hmN p).count.val * ((S.side m p).val / 4) := by
    rw [(S.toDepth hmN p).exact_size,
      Nat.mul_comm (S.side m p).val (S.toDepth hmN p).count.val,
      Nat.mul_div_assoc _ (S.side_four m p)]
  funext i
  by_cases hi : i = 0
  · simp only [head, hi, if_pos, Pi.smul_apply, nsmul_eq_mul]
    exact_mod_cast hq
  · simp only [head, hi, if_false, Pi.smul_apply, smul_zero]

theorem site_embedded (S : Schedule) {m N : ℕ} (hmN : m ≤ N) (p : ℕ) :
    (S.toDepth hmN p).embed (site S m p) = site S N p := by
  unfold site
  rw [Ratio.embed_wrap, ← head_scaled S hmN p]

/-- Inner coordinates are the actual fine mesh and period, as in Order.fuse. -/
def nested (f : Extraction.Order) : Filter Cutoffs :=
  atTop.curry f.fuse

def lengths (S : Schedule) (w : Cutoffs) : Side :=
  halfSide S w.1 w.2.2

def heads (S : Schedule) (w : Cutoffs) : Cover :=
  head S w.1 w.2.2

theorem clearance (S : Schedule) :
    MS.Vista.Clearance (lengths S) (heads S) := by
  intro w x
  change MS.Vista.mine
    (MS.Orbit.periodN (halfSide S w.1 w.2.2))
    (wrap (MS.Orbit.periodN (halfSide S w.1 w.2.2))
      (head S w.1 w.2.2) - MS.Orbit.thin (halfSide S w.1 w.2.2) x)
  rw [head_native]
  exact MS.Fleet.Cleared (quarterIndex S w.1 w.2.2) x

theorem width (S : Schedule) : MS.Vista.width (lengths S) (heads S) := by
  obtain ⟨C, hC, h⟩ := MS.Fleet.scaleWalk
  refine ⟨C, hC, fun w => ?_⟩
  simpa only [lengths, heads, halfSide, head_native, MS.Orbit.dimT] using
    h (quarterIndex S w.1 w.2.2)

/-- This is a candidate profile; authenticating it to an actual model is separate. -/
def profile (S : Schedule) (μ : ℝ) : MS.Rake.Geo Cutoffs where
  θ w := S.scale w.1
  η w := μ - S.scale w.1
  room w := by
    unfold Schedule.scale Schedule.a
    rw [inv_inv]
    exact Real.log_nonneg (by exact_mod_cast (S.denominator w.1).property)

theorem profile_tendsto (S : Schedule) (f : Extraction.Order) (μ : ℝ) :
    Tendsto (profile S μ).θ (nested f) atTop := by
  apply tendsto_atTop.2
  intro b
  change ∀ᶠ m : ℕ in atTop, ∀ᶠ k : ℕ in atTop, ∀ᶠ j : ℕ in atTop,
    b ≤ S.scale m
  exact (S.divergent.eventually (eventually_ge_atTop b)).mono
    (fun m hm => Eventually.of_forall fun _ => Eventually.of_forall fun _ => hm)

private theorem side_tendsto (S : Schedule) (m : ℕ) :
    Tendsto (fun p => ((S.side m p).val : ℝ)) atTop atTop := by
  have h : StrictMono (fun p => (S.side m p).val) := by
    intro a b hab
    change (S.period a).val * (S.denominator m).val <
      (S.period b).val * (S.denominator m).val
    exact Nat.mul_lt_mul_of_pos_right (S.period_strict hab) (S.denominator m).property
  exact tendsto_natCast_atTop_atTop.comp h.tendsto_atTop

theorem profile_super (S : Schedule) (f : Extraction.Order) (μ : ℝ) :
    MS.Tide.Super (nested f) (lengths S) (profile S μ).θ := by
  intro h
  have he : ∀ w : Cutoffs,
      MS.Vista.tickA (lengths S) w = ((S.side w.1 w.2.2).val : ℝ) := by
    intro w
    change ((MS.Orbit.periodN (halfSide S w.1 w.2.2)).val : ℝ) = _
    rw [dimension]
  simp_rw [he]
  change ∀ᶠ m : ℕ in atTop, ∀ᶠ k : ℕ in atTop, ∀ᶠ j : ℕ in atTop,
    h * S.scale m ≤ Real.log ((S.side m (f.per k)).val : ℝ)
  exact Eventually.of_forall fun m =>
    ((Real.tendsto_log_atTop.comp (side_tendsto S m)).comp f.per.cofinal).eventually
      (eventually_ge_atTop (h * S.scale m)) |>.mono
        (fun k hk => Eventually.of_forall fun _ => hk)

theorem eventually_legal (f : Extraction.Order) :
    ∀ᶠ w : Cutoffs in nested f, w.1 ≤ w.2.1 := by
  change ∀ᶠ m : ℕ in atTop, ∀ᶠ k : ℕ in atTop, ∀ᶠ j : ℕ in atTop,
    m ≤ f.mesh j
  exact Eventually.of_forall fun m => Eventually.of_forall fun _ =>
    f.mesh.cofinal.eventually (eventually_ge_atTop m)

end YM.Integration.ActualCoarseQuarterProfile
end
