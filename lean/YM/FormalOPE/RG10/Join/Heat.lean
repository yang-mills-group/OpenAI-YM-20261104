import YM.FormalOPE.RG10.Join.Split
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.LocalPolynomial
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Arity
import YM.PertExtension.Series
/-!
# Gaussian forest prices (primitive, ingredient for formal report)

Restrict the quantitative bound to Gaussian with no tag randomness. Use at a fixed ideal tree,
never compare a *statistical* error with this rule by fixing tags without an independent argument.
Tag-response required by actual comparison remains with RG02. Reuse relative Schur, not mass in
sup-norm chart boxes or count of possible labels. All positions & covariance profiles are in the
explicit units caller uses (native torus sites of `Side n`). No IR quotient for this lemma!
`bank` is true torus distance, not modulo inversion & not continuum.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Joins.Gauss
open MeasureTheory PowerSeries Finset Marker Extra.Trajectories FlatFeed Word Polar Function
open Primitives.GCC Primitives.GCC.Anchor Lattice
open YM.Multi (parts shards)
open YM.Multi.Vacuum.Gauss
open Next.SectorChange.Schur Next.SectorChange.Wisps
open Grove Connector Fused Probe Growth Moment Charge Expansion Price
open scoped BigOperators Topology Classical

variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    {R : Census V} {S : Census I}

def standardFeed (J : Type) [Fintype J] : FlatFeed Unit (Row J) where
  chance _ := 1
  chance_nonneg _ := zero_le_one
  chance_one := by simp
  base _ := standard J
  density _ := 1
  density_nonneg _ := .of_forall fun _ => zero_le_one
  density_integrable _ := integrable_const _
  mass_pos _ := by simp

variable {J : Type} [Fintype J] (v : Probes V I) (s : R.Mode) (q : Rows V I J)
-- broad P proof. w = 1+ square; not a norm estimate
open PertExtension.Series (Zone)
private def zone (J : Type) [Fintype J] : Zone (Row J) := ⟨size, size_one⟩

def admissible (f : Unit × Row J → ℂ) := Continuous (fun x => f ((),x)) ∧
      Zone.Invoice (zone J) (fun x => f ((),x))
lemma admit_constant (c : ℂ) : admissible (J:=J) (fun _=>c) := ⟨continuous_const, Zone.Invoice.const c⟩

def hall (J : Type) [Fintype J] : Subalgebra ℂ (Unit × Row J → ℂ) where
  carrier := admissible
  mul_mem' {x y} h k := ⟨(show admissible x from h).1.mul (show admissible y from k).1,
    Zone.Invoice.mul (show admissible x from h).2 (show admissible y from k).2⟩
  one_mem' := admit_constant _
  zero_mem' := admit_constant _
  add_mem' {x y} h k := ⟨(show admissible x from h).1.add (show admissible y from k).1,
    Zone.Invoice.add (show admissible x from h).2 (show admissible y from k).2⟩
  algebraMap_mem' _ := show admissible (J:=J) _ from admit_constant _

lemma accepted (J : Type) [Fintype J] : accepts (standardFeed J) (hall J) := by
  rintro f ⟨h,⟨C,j,hC,hf⟩⟩ ⟨⟩
  have hu : Integrable (fun x : Row J => size x ^ j) (standard J) := by
    have hi := volume_pay (show (0:ℝ) < 1/4 by norm_num) j (J:=J); simpa using hi
  simp only [standardFeed, Pi.one_apply, Complex.ofReal_one, one_mul];
  exact (hu.const_mul C).mono' h.aestronglyMeasurable (.of_forall hf)

/-- One Gaussian driver-representation piece. For different local pieces the read cut, derivative
needs and supports are allowed DIFFERENT. v,q are projections of the same flat sample (not
resampling independent coordinates). -/
def joint (u : Probes V I) (q : Rows V I J) (t : V) (x : Unit × Row J) := u t (mapRows (q t) x.2)
omit [Fintype V] [Fintype I] [DecidableEq I] in
lemma recognized : partners (standardFeed J) R (joint v q) = accounts R q v := by
  ext i
  change (standardFeed J).mean (guests (joint v q) i) = total i.val q v
  unfold FlatFeed.mean; simp only [standardFeed, integral_const, Pi.one_apply, isProbabilityMeasure_iff_real.mp,
    Finset.univ_unique, Finset.sum_singleton, Complex.ofReal_one, one_mul] -- inspect
  simp [guests, joint, Finset.prod_apply, total, values]

variable {n : Side} (p : I→ Site n) (γ δ α K : ℝ) (a : ℕ)
variable (o : V) (N : V → Support n) (L : V → Finset I) (w : V → Row I) (H : V → ℕ→ℝ)

/-- Direct cost for analytical local realizations, kernel norms in the construction require
further uniform bound and translation ledger. α exponent retained for support-cover-number
charge; δ residual rate (use positive for decay). State exact budget, not asymptotic here. -/
structure ConnectedLaw (q : Rows V I J) (p : I→ Site n) (a : ℕ) (γ δ α K : ℝ)
    (v : Probes V I) (s : R.Mode) (o : V) (N : V → Support n) (L : V → Finset I)
    (w : V→Row I) (H : V → ℕ→ℝ) : Prop where
  stem : o ∈ s.val
  row : Price.Bank s.val q p γ K
  room : 0 ≤ α
  width : δ + α / (a + 1) ≤ γ
  live i (h : i∈s.val) : (N i).Nonempty
  endpoints i (h : i∈s.val) k (hk : k∈L i) : p k ∈ N i
  moment : Moment.base q s.val w
  absolute : Probe.Valid s.val s.val.card v w H
  reads i (h : i∈s.val) : Probe.Reads (L i) (v i)

lemma costed (φ : V → Unit × Row J→ℂ) (hm : ∀ i∈s.val, φ i = joint v q i)
    (h : ConnectedLaw q p a γ δ α K v s o N L w H) :
    ‖tally (standardFeed J) s φ‖ ≤
      ∑ f∈options s.val {o}, Price.loan N L s.val o a α δ K q H w f /
        node α a (s.val.biUnion N) := by
  have hx : ({o} : Finset V) ⊆ s.val := singleton_subset_iff.mpr h.stem
  rw [tally_congr _ _ hm, tally, recognized v, ← PolyUtil.at_marker o (accounts R q v) (accounts_quiet ..) s h.stem]
  let k:=(s.val \ {o}).card
  have hk : k+1=s.val.card:=by
    unfold k; rw [Finset.card_sdiff_of_subset hx,card_singleton,Nat.sub_add_cancel]; exact card_pos.mpr ⟨o,h.stem⟩
  change ‖mixed q v s {o}‖ ≤ _
  rw [Primitives.GCC.Expansion.detail s k {o} hx rfl q v w H h.moment (hk.symm ▸ h.absolute)];
  apply (norm_sum_le ..).trans; apply Finset.sum_le_sum; intro f hf
  obtain ⟨hA,hB⟩ := Price.receipt N L o h.stem a h.live h.endpoints h.row h.room h.width
    h.moment h.absolute h.reads f ((choices ..).1 hf) -- inspect
  apply hA.trans; exact (le_div_iff₀ (show 0 < node α a (s.val.biUnion N) from rate_pos ..)).2 (by rwa [mul_comm])
end YM.FormalOPE.RG10.Joins.Gauss
