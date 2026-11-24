import YM.Integration.WilsonJointMoment
import YM.Integration.ActualStartupNormalizedQ

/-! Forward second moments of a single signed combination of all the
physical startup words. Every test, coefficient and field is shared. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonStartupJointMoment
open Function Finset MeasureTheory Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison
open IterationFour IterationFour.Vacuum FullQLocal.RenderedStep
open MergeProof MergeProof.Accent
open scoped Classical BigOperators Topology

variable {G : Gauge} {V : Type} {R : Run G} {B : MS.Local.Physical.Deck G}
    {m p n : ℕ} {hn : n ≤ m + 1} [DecidableEq V] [Fintype V] [Nonempty V]
    (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R p (m+1) n hn V)
    (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ)
local notation "P₁" => R.family.path.rep (m+1) p (m+1)
local notation "P₀" => R.family.path.rep (m+1) p m
local notation "S₀" => R.family.path.levels.clock.op m p
local notation "b₀" => R.family.path.β (m+1) p (m+1)
local notation "nf" => R.family.side (m+1) p
local notation "nc" => R.family.side m p

omit [Nonempty V] in
/-- One finite linear readout, including the original product of all fields in each mode. -/
def field (c : (Stock.census V).Mode → ℂ) (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (U : Config G nf) : ℂ := ∑ s, c s*ActualStartupNormalizedQ.modeObservable Q D u μ orders x s U

def source (hG : G.Simple) (c : (Stock.census V).Mode → ℂ) (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (U : Config G nf) : ℂ :=
  ∑ s, c s*(((ActualOriginalQInput.input Q D u μ orders hG (m+1) le_rfl).leaf x).density U).part s

omit [Nonempty V] in
/-- The single jointly tested field has an actual bounded measurable representative. -/
theorem measured (c : (Stock.census V).Mode → ℂ) (x : TestSpace (ActualRunQlocalNativeTuple.orbit D)) :
    Envelope (field Q D u μ orders c x) := by
  apply Envelope.compactC
  apply continuous_finsetSum
  exact fun s _ => continuous_const.mul (ActualStartupNormalizedQ.mode_continuous Q D u μ orders x s)

/-- Factor the true startup vacuum before the sum of signed coefficients. -/
theorem original (hG : G.Simple) (href : ∀ a : ActualOriginalQReaders.Slot u, R.family.ref a.2.size ≤ m + 1)
    (c : (Stock.census V).Mode → ℂ) (x : TestSpace (ActualRunQlocalNativeTuple.orbit D)) :
    source Q D u μ orders hG c x = fun U => (P₁).eval U • field Q D u μ orders c x U := by
  funext U
  unfold source field
  simp only [ActualStartupNormalizedQ.input_density_mode Q D u μ orders hG href,Complex.real_smul,Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- True one-step joint comparison for the full signed mark, its coarse
model and an arbitrary bounded nonnegative event. -/
theorem model (hG : G.Simple) (href : ∀ a : ActualOriginalQReaders.Slot u, R.family.ref a.2.size ≤ m + 1)
    (c : (Stock.census V).Mode → ℂ) (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    {v : Config G nc → ℂ} (hv : Envelope v) {t : Config G nc → ℝ} (ht : Envelope t) (ht0 : ∀ W, 0 ≤ t W)
    (k : ℕ) :
    (∫ W, (P₀).eval W*t W*‖((P₀).eval W)⁻¹ • (S₀).push b₀ (source Q D u μ orders hG c x) W-v W‖^k ∂prior G nc) ≤
      ∫ U, (P₁).eval U * ∫ W, (S₀).density b₀ U W*t W*‖field Q D u μ orders c x U-v W‖^k ∂prior G nc ∂prior G nf := by
  rw [original Q D u μ orders hG href c x]
  simp only [←actualAverage_push]
  exact WilsonJointMoment.joint R.makes (Nat.lt_succ_self m) (measured Q D u μ orders c x) hv ht ht0 k

/-- Every fine signed mode shares the one genuine positive Wilson factor.
The full readout's kth moment is bounded by the one startup moment. -/
theorem contracted (hG : G.Simple) (href : ∀ a : ActualOriginalQReaders.Slot u, R.family.ref a.2.size ≤ m + 1)
    (c : (Stock.census V).Mode → ℂ) (x : TestSpace (ActualRunQlocalNativeTuple.orbit D)) (k : ℕ) :
    (∫ W, (P₀).eval W*‖((P₀).eval W)⁻¹ • (S₀).push b₀ (source Q D u μ orders hG c x) W‖^k ∂prior G nc) ≤
      ∫ U, (P₁).eval U * ‖field Q D u μ orders c x U‖^k ∂prior G nf := by
  have hj := model Q D u μ orders hG href c x (Envelope.constC 0) (Envelope.const 1) (fun _=>zero_le_one) k
  simpa only [sub_zero,mul_one,integral_mul_const,(R.family.path.levels.transition_mass m p b₀).total,one_mul] using hj

end YM.Integration.WilsonStartupJointMoment
