import YM.WilsonMS.Scales.Carried
/-!
# EqX dilation rule in the filtering (not mass-independent) scheme

Intrinsic characterization by the Wilson-calibrated X array. `Mandate`
at all finite horizons; it has a unique solution. Only one freely calibrated
length, no assumption of any sequence continuity. Must use the coupled
operator A(t) (needn't preserve grading yet). Group property of the entire
system by uniqueness. Apply to native MS with all geometry, not an abstract
transfer p.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.GFlow
open Function Set Filter MeasureTheory Real Finset Metric
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus XSpace.TestBudget XSpace.Structure1
open Maxwell Maxwell.Free Maxwell.Wick VisitH
open MS MS.Menus MS.Theater MS.Land MS.Book MS.Book.Program MS.Book.Convolve
open PowerSeries (coeff mk X C constantCoeff invOfUnit)
open Fiscal BMenu Rider Reservoir VisitH Sea Fray FrameConj FrameConj.Gates FrameX Ice
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {d k n m j : ℕ}
local notation "BΨ" => Ensure.deck G
section chart

abbrev Links (G : Gauge) :=
  ∀ d, Guard G d

abbrev Connect (T : Links G) :=
  ∀ d, Ladder (T (d + 1)) (T d)
variable {M : Booked (Ensure.deck G)} {F : MS_Data G M} {V : Store G} (P : Rose.Pick V) {r t s : ℝ}
  {W : Initialize G}

private lemma step_scales (F : MS_Data G M) (r : ℝ) (d : ℕ) (j : ℕ) :
    recruit (step d) (Continuum F r j (d + 1)) = Continuum F r j d := by
  ext1 n
  ext1 x
  ext1 p
  rw [fromHeight, fromHeight ((Continuum F r j d n) x) p]
  apply Finset.sum_congr rfl
  intro i _
  apply congr_arg
  let k (j : Glyph BΨ d) : Glyph BΨ (d + 1) := ⟨j.fst.castSucc, j.snd⟩
  have hx : Normalize.step d ∘ (glow ∘ i) = Fiscal.glow ∘ (k ∘ i) := rfl
  rw [recruits, hx, continues, continues]
  simp_rw [lowK]
  rfl

lemma layout_fit (F : MS_Data G M) (V : Store G) (t : ℝ) : Connect (KnotMS F V t) := by
  intro d
  let U (d j) := Continuum F t j d
  have h (d : ℕ) : Fray.Via (u := pure (0 : ℝ)) (V.survey d) (fun _ => U d 0) := by
    unfold Fray.Via U
    rw [free_match]
    exact tendsto_const_nhds
  have he :=
    Fray.chain_layout (P := fun (_ : ℝ) => U (d + 1)) (Q := fun (_ : ℝ) => U d) (V.survey d)
      (V.prepared d) (V.survey (d + 1)) (V.respects d) (V.prepared _) (fun _ j => step_scales F t d j)
      (h _) (h d)
  have he : (Lμ V F t d) = (fun i => fell d (Lμ V F t (d + 1) i)) := (eventually_pure.mp he).1
  exact Normalize.nest _ _ (fun i => (congr_fun he i).symm)

abbrev flair (P : Rose.Pick V) (F : MS_Data G M) (t : ℝ) (d : ℕ) :=
  buryD t (coupon (ψW P F) (KnotMS F V 0 d))

def changeM (P : Rose.Pick V) (F : MS_Data G M) (s : ℝ) : Links G := fun d =>
  vault (flair P F s d) * coupon (ψW P F) (KnotMS F V (-s) d)

abbrev Scheme (G : Gauge) :=
  ∀ d, ChartK G d

structure Linked (S : Scheme G) (t : ℝ) (Q : Links G) (U : Cn) : Prop where
  ground : ∀ d, CloseP (Q d)
  normal : Aware U
  origin : ∀ d, Equad (Act (sweep t (S d)) (Q d)) (Sub U (S d))

lemma Linked.twirl {S : Scheme G} {Q R : Links G} {U P : Cn} (h : Linked S s Q U)
    (he : Linked S t R P) : Linked S (t + s) (fun d => buryD t (Q d) * coupon U (R d)) (P.subst U) := by
  refine
    ⟨fun d => (duties t (h.ground d)).times ((he.ground d).substitute h.normal.clean),
      he.normal.extend h.normal, fun d => ?_⟩
  rw [← action_times, ← lands]
  apply Equad.trans (Y := Sub (P.subst U) (S d))
  swap
  · exact Equad.rfl _
  rw [← adjoint]
  obtain hv := sweep_t (h.origin d) t
  rw [← name_sub _ h.normal.root] at hv
  apply Equad.trans (Equad.act hv (coupon U (R d)))
  rw [← action_sub h.normal.root, ← sub_subK _ he.normal.root h.normal.root]
  exact Equad.sub (he.origin d) U
variable (hG : G.Simple) {X : Prescription (Ensure.deck G)} (hp : Installed W F X) (hh : Commuting X)
include hG hp hh

lemma Oven : CloseP (flair P F t d) :=
  duties t ((knot_base _ _ _ _).substitute (ψ_aware P hG hp hh |>.clean))

lemma growth (t : ℝ) : Linked (ΨScheme P F) t (changeM P F t) (transit P F t) := by
  obtain hw := ψ_aware P hG hp hh
  obtain he := awareχ P hG hp hh (-t)
  refine
    ⟨fun d => (Oven (d := d) P hG hp hh).invert.times ((knot_base F V _ _).substitute hw.clean),
      flowAware P hG hp hh _, fun d => ?_⟩
  let U := KnotMS F V 0 d
  let Y := GMS F 0 d
  let Z := GMS F (-t) d
  let B := sweep t (ΨScheme P F d)
  let S := KnotMS F V (-t) d
  let Pₖ := coupon (ψW P F) S
  let T := flair P F t d
  let A' := Act Z S
  have hU : ΨScheme P F d = Act (Sub (ψW P F) Y) (coupon (ψW P F) U) := by
    rw [← action_sub hw.root]
    rfl
  have H : Equad B (Act (Sub (ψW P F) Z) T) := by
    unfold B
    rw [hU, adjoint, ← name_sub t hw.root]
    refine Equad.act (Equad.sub ((show Equad (sweep t Y) Z from ?_)) _) _
    simpa only [zero_sub] using starClock F 0 t d
  obtain hx : Equad (Act B (vault T * Pₖ)) (Sub (ψW P F) A') := by
    obtain ht := H.act (vault T * Pₖ)
    rwa [action_times, ← mul_assoc T, (antidote (Oven (d := d) P hG hp hh)).1, one_mul, ←
      action_sub (F := Z) hw.root S] at ht
  apply Equad.trans hx
  obtain hV := Equad.sub ((take_ψ P hG hp hh (-t) d).symm) (transit P F t)
  unfold transit at hV
  unfold ψW at hV
  apply Equad.trans _ hV
  rw [sub_subK _ (Ice.born _) (flowAware P hG hp hh _ |>.root), ← Ice.assoc he.root hw.root,
    Ice.counter_r he.root
      (by
        rw [he.paid]
        norm_num),
    PowerSeries.subst_X (FrameConj.Worried hw.root)]

lemma built_nested : Connect (changeM P F t) := fun d =>
  Ladder.product
    (Ladder.turnback
      (Ladder.product (Ladder.product (Ladder.watches G d _) (Ladder.edit (layout_fit F V 0 d) _))
        (Ladder.watches G d _))
      (Oven P hG hp hh) (Oven P hG hp hh))
    (Ladder.edit (layout_fit F V _ d) _)

lemma single {A : Links G} {U : Cn} (h : Linked (ΨScheme P F) t A U) :
    A = changeM P F t ∧ U = transit P F t := by
  obtain H := growth P hG hp hh t
  have he : A = changeM P F t :=
    funext fun d =>
      BasisTest.forcing V (h.origin d) (H.origin d) (BasisTest.styled _ (ψCert P hG hp hh d) h.normal)
        (BasisTest.styled _ (ψCert P hG hp hh d) H.normal) (h.ground d) (H.ground d)
  refine ⟨he, ?_⟩
  have ht : Equad (Sub U (ΨScheme P F 6)) (Sub (transit P F t) (ΨScheme P F 6)) := by
    apply Equad.trans (h.origin 6 |>.symm)
    rw [he]
    exact H.origin 6
  obtain hh' := obs_equ P ht
  rwa [ob_sub P h.normal.root (fitted P F 6 3), ob_sub P H.normal.root (fitted P F 6 3),
    watches P hG hp hh, PowerSeries.subst_X (FrameConj.Worried h.normal.root),
    PowerSeries.subst_X (FrameConj.Worried H.normal.root)] at hh'

lemma scale_law (s t : ℝ) :
    (∀ d : ℕ,
        buryD t (changeM P F s d) * coupon (transit P F s) (changeM P F t d) =
          changeM P F (t + s) d) ∧
      (PowerSeries.subst (transit P F s) (transit P F t)) = transit P F (t + s) := by
  obtain ⟨he, hc⟩ := single P hG hp hh ((growth P hG hp hh s).twirl (growth P hG hp hh t))
  exact ⟨fun i => congr_fun he i, hc⟩
end chart
end YM.WilsonMS.GFlow
