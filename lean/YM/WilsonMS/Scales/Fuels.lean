import YM.WilsonMS.Scales.OnlyMass
/-!
# Smooth and polynomial scale running in the posing coupling

The scale on MS charts includes a log shift selected by `Port`. Need
actual all-orders property even for finite diagnostics through the IFT
and for connected calibration; proving only continuity in length at
each *single ray* is not enough.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.GFlow
open Function Set Filter MeasureTheory Real Finset Metric
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus XSpace.TestBudget XSpace.Structure1
open Maxwell Maxwell.Free Maxwell.Wick VisitH
open MS MS.Menus MS.Theater MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Logarithm
open PowerSeries (coeff mk X C constantCoeff invOfUnit)
open Fiscal BMenu Rider Reservoir VisitH Sea Fray FrameConj FrameConj.Gates FrameX Ice TraceMC
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {d k n m j : ℕ}
local notation "BΨ" => Ensure.deck G
namespace Raha

variable {S : ℝ → ChartK G d} {P : Points n} {M : Booked (Ensure.deck G)} (F : MS_Data G M)

lemma fuelM (s : Set (Points n)) (h : IsCompact s) (hp : s ⊆ conf n) (v : Fin n → Sec G d) (j : ℕ) :
    Ready (fun r : ℝ => fun x : s => GMS F r d n x.val j v) := by
  let B := Daylight BΨ d
  have he (p : Point G d n) :
    p v = ∑ j : Fin n → Glyph BΨ d, (∏ i, B.coord (j i) (v i)) * p (glow ∘ j) := fromHeight ..
  let ψ := fun i (x : s) => VisitH.actual x.val i
  have hb := group_visit h hp 0 (fun x : s => x.property)
  simp_rw [he (GMS ..)]
  unfold GMS
  simp_rw [lowK]
  let K (p : ℝ) (x : Fin n → Glyph BΨ d) (v : s) := answers x F p j v.val
  let X (i : Fin n → Glyph (Ensure.deck G) d) (r : ℝ) := fun x : s =>
    (∏ j, B.coord (i j) (v j)) * K r i x
  have hp : Ready (∑ i : Fin n → Glyph (Ensure.deck G) d, X i) :=
    Ready.sums _ fun i _ =>
      (letLog hb F (profileK i) Finset.univ j).linear
        ((LinearMap.mulLeft (s → ℂ) (fun _ => ∏ j, B.coord (i j) (v j))).restrictScalars ℝ)
  convert hp using 1
  funext p i
  simp only [Finset.sum_apply]
  rfl

lemma forumT (w : Test n) (p : Fin n → Sec G d) (j : ℕ) :
    Ready (fun t : ℝ => Continuum F t j d n w p) := by
  let K := tsupport w
  obtain ⟨M, h⟩ := fuelM F K w.hasCompactSupport w.tsupport_subset p j
  let D t := Continuum F t j d n w p
  have ht : D = evaluate M D := by
    funext i
    have he (x) (hv : x ∈ K) :
      GMS F i d n x j p = ∑ r ∈ Finset.range M, (plate M r).eval i • GMS F r d n x j p := by
      obtain he := congr_fun (interpret h i) (⟨x, hv⟩ : K)
      simpa only [Logarithm.evaluate, Finset.sum_apply, Pi.smul_apply] using he
    have hX (x) :
      w x * (GMS F i d n x j p) =
        ∑ r ∈ Finset.range M, (plate M r).eval i • (w x * GMS F r d n x j p) := by
      by_cases hp : x ∈ K
      rw [he x hp, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_smul_comm ..
      rw [image_eq_zero_of_notMem_tsupport hp]
      simp
    unfold D Logarithm.evaluate
    simp_rw [(coupon_stage F _ d n j p).2]
    unfold Test.applyTo
    dsimp only
    simp_rw [hX]
    rw [integral_finsetSum _ (fun i _ => ?_)]
    · simp_rw [integral_smul]
    exact (w.smearing (coupon_stage F _ _ _ j p |>.1)).smul ((plate M i).eval _)
  change Ready D
  exact ht.symm ▸ eval_ready M D

lemma π_sum {I E : Type} [Fintype I] [AddCommGroup E] [Module ℝ E] {f : ℝ → I → E}
    (h : ∀ i, Ready (fun x => f x i)) : Ready f := by
  classical
  have he : f = (fun p => ∑ i, Pi.single i (f p i)) := by
    ext v i
    simp
  rw [he]
  refine accounts _ (fun i _ => (h i).linear (LinearMap.single ℝ (fun _ : I => E) i))

lemma atF {P : ℝ → Prediction G d} (h : ∀ (n : ℕ) p (t : Test n), Ready (fun r : ℝ => P r n t p))
    (w : Screen G d) : Ready (fun r : ℝ => w.D (P r)) := by
  obtain ⟨n, w, T, hp⟩ := w.observable
  simp_rw [hp]
  refine Ready.linear (π_sum (f := fun x i => watch (w i) (P x)) ?_) T
  exact fun i => h (w i).n (w i).p (w i).t

lemma track_mem {T : ℝ → Pick G d} (h : Ready (fun v => T v n)) :
    Ready (fun v => coeff n (deck (T v))) := by
  have he : Ready (fun r => ((T r n).val : FieldEnd G d)) := by
    apply Ready.linear (F := FieldEnd G d) h (Change G d).subtype
  simp_rw [decked, pulling]
  split_ifs with hx
  · unfold stand
    exact Ready.add (Ready.const (1 : FieldEnd G d)) he
  exact he

lemma cart_card {X : Type} (s : Finset X) {f : X → ℝ → ℂ} (h : ∀ i ∈ s, Ready (f i)) :
    Ready (fun v => ∏ i ∈ s, f i v) := by
  classical
    induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    exact Ready.const _
  | insert i s hi ih =>
    simp_rw [Finset.prod_insert hi]
    exact
      Ready.pair (Algebra.lmul ℝ ℂ).toLinearMap (h _ (by simp))
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma merit {Y : ℝ → Point G d n} (h : ∀ v : Fin n → Glyph BΨ d, Ready (fun i => Y i (glow ∘ v)))
    (p : ℝ → Fin n → Sec G d) (hp : ∀ v, Ready (fun i => p i v)) : Ready (fun v => Y v (p v)) := by
  let B := Daylight BΨ d
  have he (k : ℝ) :
    Y k (p k) = ∑ v : Fin n → Glyph BΨ d, (∏ i, B.coord (v i) (p k i)) * Y k (glow ∘ v) :=
    fromHeight ..
  simp_rw [he]
  refine accounts _ fun i _ => Ready.pair (Algebra.lmul ℝ ℂ).toLinearMap ?_ (h i)
  exact cart_card _ fun k _ => Ready.linear (hp k) ((B.coord _).restrictScalars ℝ)

lemma shellship {v : ℝ → FieldEnd G d} (h : Ready v) (x : Sec G d) : Ready (fun t => v t x) :=
  Ready.linear h ((LinearMap.applyₗ (R := ℂ) (M₂ := Sec G d) x).restrictScalars ℝ)

lemma clockPoly (V : Store G) (d j : ℕ) : Ready (fun r : ℝ => Lμ V F r d j) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases ht : j = 0
    · subst j
      simp_rw [KnotBase]
      exact Ready.const _
    let X := V.measure d
    let E := V.prepared d
    let P r := Lμ V F r d
    let U r := Screen.blind (P r) j
    let V r i := Continuum F r i d
    have hU (i : ℕ) (h : i ≤ j) : Ready (fun r => coeff i (deck (U r))) := by
      apply track_mem
      obtain hz | hz := lt_or_eq_of_le h
      · unfold U
        simp_rw [Screen.blind_low _ j i hz]
        exact ih _ hz
      unfold U
      rw [hz]
      simp_rw [Screen.blind_at]
      exact Ready.const _
    have hK : Ready (fun t : ℝ => X.D (realm (deck (U t)) (V t) j)) := by
      refine atF ?_ X
      intro n p s
      simp_rw [Normalize.really]
      apply accounts
      intro i hi
      have ht (a : Option (Fin n)) : i a ≤ j :=
        le_trans
          (Finset.single_le_sum (f := fun j => i j) (fun i _ => Nat.zero_le _) (Finset.mem_univ a))
          ((totaled i |>.mp hi).le)
      exact
        merit (Y := fun t => V t _ _ s) (fun g => forumT F s _ _) _
          (fun a => shellship (hU _ (ht (some a))) (p a))
    have he (t : ℝ) : P t j = -X.D (realm (deck (U t)) (V t) j) := by
      obtain hh : slope X (P t 0) (V t 0) (P t j) = _ :=
        Screen.bare_price _ _ _ ht (preparedK F _ t d).2.1
      rw [show P t 0 = 0 from KnotBase .., show V t 0 = reference G d from free_match ..,
        regular X E _] at hh
      exact hh
    rw [show (fun r => _) = (fun t => -X.D (realm (deck (U t)) (V t) j)) from funext he]
    exact Ready.neg hK
end Raha
end YM.WilsonMS.GFlow
