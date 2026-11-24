import YM.OPE.Frame.Tokens
import YM.OPE.Exchange.Coherence
/-!
# Finite-demand rates for the invariant probes

A coefficient comparison can use costs of entire errors uniformly over each orbit.
These are single-time (log-of-length) rates. Preparatory Wilson costs & replicated
comparisons underneath `available_cost`, `arrangement_cost`, not a coupling-power bound.
-/
set_option autoImplicit false
noncomputable section

open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open Set Filter Function MeasureTheory
namespace YM.OPE.Frame
open Table
open MultipleContact (Detector)
variable {G : Gauge} {C : Family G} {U : Extraction.Order} {S : Table C.book} {F : Spec.Final C U S}
variable {I J L W : Type} [Fintype I] [Fintype J] {l : Filter L} {T : L → ℝ} {X : L → I → E4}
    {Y : L → J → E4} {O : L → E4} {a b c s v : ℝ} {d : ℕ} (hT : Tendsto T l atTop)
    (A : I → S.Tag)

abbrev load {G:Gauge} {R:Register G} {S : Table R} (A : I → S.Tag) : ℕ := sigma (deploy ∘ A)

lemma sight (B : S.Tag) : load (sole B) = B.fst := by unfold load sigma; simp [sole,deploy]
lemma both (A : I → S.Tag) (B : J → S.Tag) : load (beside A B) = load A + load B := by unfold load sigma; rw [Fintype.sum_sum_type]; rfl

section Cost
attribute [local instance] YM.Work.A15.compact_ortho
local notation "ν" => normalizedRotations
variable {Z Z' : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup Z']
    [NormedSpace ℝ Z'] {f : L → Z}
include hT
lemma mapped (h : RateLE l T f a) (A : Z →L[ℝ] Z') : RateLE l T (A ∘ f) a := by
  refine ((RateLE.const ‖A‖ hT |>.mul h.norm).mono (by exact (zero_add _).le)).of_norm_le ?_; exact Eventually.of_forall fun i => A.le_opNorm _
omit [NormedSpace ℝ Z] in
lemma rotating_bound (f : Ortho → Z) (h : Continuous f) (r : L → Ortho) : RateLE l T (fun i => f (r i)) 0 := by
  obtain ⟨B,hB⟩ := (isCompact_range h.norm).bddAbove; exact RateLE.absBound B hT (Eventually.of_forall fun i => hB ⟨r i,rfl⟩)
omit hT in
lemma rotating [CompleteSpace Z] (f : L → Ortho → Z) (h : ∀ r:L→Ortho, RateLE l T (fun i=> f i (r i)) a) :
    RateLE l T (fun i=>∫ K : Ortho, f i K ∂ν) a := by
  intro c hc; filter_upwards [universalize (p:=fun i (K:Ortho)=> ‖f i K‖ ≤ Real.exp (c*T i)) (fun r=> h r c hc)] with i hi
  apply le_trans (norm_integral_le_of_norm_le_const (Eventually.of_forall (hi)))
  simp

variable {m : J→ ℕ}
/-- uniform estimation remains valid for moving exterior labels with rate-zero budgets in fixed grades. -/
lemma met (f : L → MultilinearMap ℂ (fun i => S.Field (m i)) ℂ)
    (h : ∀ x, RateLE l T (fun i => f i x) a) (g : L → ∀ i, S.Field (m i)) (hh : ∀ j, RateLE l T (fun i => g i j) 0) :
    RateLE l T (fun i => f i (g i)) a := by
  let B (i : J) := Module.finBasis ℂ (S.Field (m i))
  have hf i : f i (g i) = ∑ b : ∀ j, Fin (Module.finrank ℂ (S.Field (m j))), (∏ j, (B j).coord (b j) (g i j)) • f i (fun j => B j (b j)) := flds_sum ..
  simp_rw [hf]; refine RateLE.sum hT fun b _ => ((RateLE.prod (r:=fun i:J=> (0 : ℝ)) (f:=fun j i=> (B j).coord (b j) (g i j)) hT (fun j _ => ?_)).smul (h (fun j => B j (b j)))).mono (by simp)
  exact mapped hT (hh j) (LinearMap.toContinuousLinearMap (((B j).coord (b j)).restrictScalars ℝ))
end Cost
section Clearance
include hT
/-- Fixed positive clearances all over each orbit. -/
lemma escort_bounds [l.NeBot] (e : Exterior C.book) (O : L → E4) (K : L→ Ortho) :
    Kept l T 0 (fun k=> escorts e (O k) (K k)) ∧ Intervals l T 0 (fun k=> sole (O k)) (fun k=> escorts e (O k) (K k)) := by
  obtain ⟨hp,hk⟩ := bearing_lifetime hT e; constructor
  · intro b hb; filter_upwards [hp b hb] with k h i j hij
    rw [escorts,escorts,add_sub_add_right_eq_sub, ← Ortho.motion_at, ← Ortho.motion_at, ← map_sub, LinearIsometryEquiv.norm_map]; exact h i j hij
  intro b hb; filter_upwards [hk b hb] with k h i j; rw [norm_sub_rev,escorts,sole, add_sub_cancel_right,Ortho.move_norm]; have hh := h i j; change _ < ‖0-bearing e j‖ at hh; simpa using hh

omit hT in
lemma cleared_footprints (V : Detector S d) (h : Tendsto (fun k=>away (X k) (O k)) l (𝓝 0)) (hx : ∀ᶠ i in l, Injective (X i)) :
    ∀ᶠ k in l, admissible V (X k) (O k) := by
  filter_upwards [hx,h.eventually (Metric.ball_mem_nhds _ (threshold_positive V))] with i hi ht; refine within_reach V hi _ le_rfl fun j => (norm_le_pi_norm (away (X i) (O i)) j).trans ?_
  exact (show ‖away (X i) (O i)‖ < _ from mem_ball_zero_iff.mp ht).le
omit hT in
lemma retreats {r : L → ℝ} (hr : Tendsto r l (𝓝[>]0)) (hx : ∀ᶠ i in l, Seen (r i) (X i) (O i)) :
    Tendsto (fun i=> away (X i) (O i)) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun i=> norm_nonneg _) ?_ (g:=fun i=>Real.sqrt (r i)) ?_
  · filter_upwards [hx] with i hi using (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr (fun j=> (hi.housed j).le)
  simpa only [Real.sqrt_zero] using (hr.mono_right nhdsWithin_le_nhds).sqrt
/-- If footprints merely tend to the indicated center then *fixed* orbit probes have rate zero
for their gaps to those footprints. (Useful when the outer scale itself is at rate zero.) -/
lemma escorts_room (e : Exterior C.book) (h : Tendsto (fun k => away (X k) (O k)) l (𝓝 0)) (K : L→Ortho) :
    Intervals l T 0 X (fun k=> escorts e (O k) (K k)) := by
  have he j : 0 < ‖bearing e j‖ := norm_pos_iff.mpr (beside_distinct.mp (bearing_clear e)|>.2.2 () j|>.symm)
  intro b hb; let z k:=Real.exp (-b*T k); have ht:Tendsto z l (𝓝 0):= (RateIs.exp (-b) hT).tends (by linarith only [hb]) hT
  have h' j : ∀ᶠ k in l, ‖away (X k) (O k)‖ + z k < ‖bearing e j‖ := by
    refine ((h.norm.add ht).eventually (p:=fun x:ℝ=> x < ‖bearing e j‖) (gt_mem_nhds ?_)); simpa using he j
  filter_upwards [eventually_all.mpr h'] with k h i j; specialize h j
  have hj:=c_dist_point (O k) (X k i) (escorts e (O k) (K k) j); rw [norm_sub_rev (O k), escorts, add_sub_cancel_right,Ortho.move_norm] at hj; rw [norm_sub_rev (O k)] at hj; change z k < ‖X k i-escorts e (O k) (K k) j‖; unfold escorts; have he : ‖X k i-O k‖ ≤ ‖away (X k) (O k)‖ := norm_le_pi_norm (away (X k) (O k)) i; linarith only [hj,h,he] -- escorts unfolded in hj?
end Clearance
section Deck
variable (Z : Scheme F) (D : Detector S d) (p : Row Z.rings) {X' : W → L → J → E4} -- list at same arity J used, variable
local notation "χ" => F.room.kernel.spin
local notation "R" => F.sector.turns
local notation "P" => F.phase.transport.spots
local notation "ν" => normalizedRotations
include hT
/-- Generic price comparison through one finite readout. Compact-integrable as required by the orbit
formulas, with a rate bound for those *complete differences* indicating integrand eligibility. The other
expression can be a sum with cancellations, or a single previously matched field. -/
lemma assess_price {g : L → Bool → D.probes → Ortho → ℂ} (φ : L → Bool → S.Field d)
    (hh : ∀ᶠ i in l, ∀ b, φ i b = ∑ e : D.probes, ∫ K : Ortho, g i b e K • rotatedAnswer R χ D e b K ∂ν)
    (hg : ∀ᶠ i in l, ∀ b e, Integrable (fun K=> g i b e K • rotatedAnswer R χ D e b K) ν)
    (h : ∀ᶠ k in l, admissible D (X k) (O k))
    (hb : ∀ (e : D.probes) b (K : L→Ortho), RateLE l T (fun k=> inspect R χ e b (X k) A (O k) (K k) - g k b e (K k)) a) :
    RateLE l T (fun k=> assess R χ D (X k) A (O k) - (1/2:ℂ) • (φ k false + φ k true)) a := by
  have he (b) : RateLE l T (fun k=> investigate R χ D b (X k) A (O k) - φ k b) a := by
    let f (e : D.probes) k K := (inspect R χ e b (X k) A (O k) K - g k b e K) • rotatedAnswer R χ D e b K
    refine (RateLE.sum (S:=Finset.univ) (f:=fun e k=> ∫ K, f e k K ∂ν) hT fun e _ => rotating (a:=a) (f e) (fun K=> ((hb e b K).smul (rotating_bound hT _ (F.phase.transport.spots.spin d _) K)).mono (add_zero _|>.le))).congr ?_
    filter_upwards [hh,hg,h] with k hi hi' ht; rw [hi b,investigate, ← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun e _=>?_
    rw [← integral_sub (inspect_live R χ P F.room.kernel (ht e)) (hi' b e)]; unfold f; simp_rw [sub_smul]
  apply ((RateLE.const (1/2:ℂ) hT |>.smul ((he false).add (he true) hT)).mono (zero_add _ |>.le)).congr
  filter_upwards with i; rw [assess, ← smul_sub]; congr 1; abel
omit hT in
lemma coherent_coord (m : ℕ) (H : S.Field m) (o : E4) : Z.representation.coord p p.fst (assess R χ (Z.sampling p.fst) (sole o) (sole ⟨m,H⟩) o) = Z.representation.coord p m H := by
  rw [← realized F.room.kernel P]; exact congrArg ((Z.representation.axes p.fst).coord p.snd) (show sheaf Z.rings p.fst p.fst _ = sheaf Z.rings p.fst m H from Subtype.ext (Z.coherent ..))
end Deck
end YM.OPE.Frame
