import YM.Integration.MSMatch.MarkArithmetic
import YM.Integration.MSMatch.Uniqueness
import YM.Comparison.RG02.Bare.Signals
import YM.FormalOPE.RG10.CommonStamps

/-!
# Binding sources at the finite top

For every finite list of placed basis entries from the retained Family, use units
of its `places` (lattice units; restore external engineering powers separately).
Use their actual insertion stencils and retain the individual powers g^-slots.
See `as_field` for the physical re-expression, including the exact top threshold,
terminal and engineering factors in `SameColumns.reprice`. These are the bare
columns before e.g. the top free W adjustment. On the torus, use them as positive
markers in the local conditional step. Use `bareUp`: add the *entire difference*
of the Wilson action and main term, not only selected cubic/quartic information.
Connect the canonical `LocalFormal.Datum` so obtained, through every order, to
the transparent RG10 formula. Prove the expansion of the genuine full thermal
push with these insertions (including tails, using the fixed-geometry supplier),
for the numerator, denominator and conditional ratios. This step is exact,
no unknown geometric, gap, asymptotic or IR-comparison premise left.

These top data are shared with our auxiliary *different* infrared geometry via
`InversionTop.Stamp.Reservation`; keep the kernel comparisons between geometries
separate (and this result is not yet any continuum limit). No estimates here in
physical norms or uniform in the aperture/period. `places` choices are the indicated
ones, not identifying an arbitrary Family across label/phase selections.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.MSMatch.SourceTop
open Function Filter MeasureTheory
open Comparison.RG02 FormalOPE FormalOPE.RG10 FormalOPE.RG10.InversionTop
open Marker Multi RG Wilson Lattice Precision Tree Exterior Next.SectorChange Source
open Laplace Integral PertExtension.Series.Tested
open scoped Topology ContDiff BigOperators Classical

section inputs
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {C : Family G} {n : Side} {d : ℕ}
    (R : Census V) (U : V → Stamp.Reservation C n d)

abbrev field (i : V) := (C.localSection (U i).height).places (Pi.single (U i).leg 1) (U i).anchor
abbrev grade (i : V) := Bare.Signals.title (C:=C) (U i).leg

variable {N p : ℕ}
omit [DecidableEq V] [Fintype V] in
lemma as_field (U : V → Stamp.Reservation C (C.side N p) d) (i : V) :
    field U i = C.O N p (PertExtension.SameColumns.reprice C N p (Pi.single (U i).leg 1)) (U i).anchor :=
  (PertExtension.SameColumns.reprice_eq ..).symm

def stencilColors := Bare.Signals.flare R (fun i _ => field U i) (grade U)

lemma stencil_well (hs : C.Makes) (hV : ∀ d, Bid.pop (C.localSection d)) : Bulk.Well (stencilColors R U) := by
  refine Bare.Signals.flare_well R _ _ ?_ (fun i _ => Envelope.compactC
    ((C.localSection (U i).height).continuous_places ..)) ?_
  · intro i
    let p := Bare.Signals.primary (U i).leg (hV _) (U i).anchor
    exact Assembly.GradeAt.coarse p (g:=(Prod.snd : ℝ × fieldDir G n 1 → _))
      contDiffAt_snd rfl
  intro i _
  exact (C.localSection _).placed_invariant (hs.sections _) (U i).anchor _

lemma stencil_starts : Bare.Starts (stencilColors R U) := by
  apply Bare.Signals.flare_good
  intro i
  obtain ⟨C',hv⟩ := isCompact_univ.exists_bound_of_continuousOn (s:=Set.univ)
    (show ContinuousOn (field U i) _ from ((C.localSection _).continuous_places ..).continuousOn)
  refine ⟨0,max C' 0,le_max_right ..,Eventually.of_forall fun _ j => ?_⟩
  rw [pow_zero,mul_one]
  exact (hv j (Set.mem_univ j)).trans (le_max_left ..)

end inputs

variable {G : Gauge} {C : Family G} (L : Bulk.Chain C.path)
    {V : Type} [Fintype V] [DecidableEq V] (R : Census V)
    (m p : ℕ) {h : ℕ} (U : V → Stamp.Reservation C (C.side (m+1) p) h)
local notation "S"=> C.path.levels.clock.op m p
local notation "K"=> L.step (m+1) m p (Nat.lt_succ_self m)
local notation "f₁"=> C.side (m+1) p
variable (F : Forest (C.path.levels.clock.op m p).ratio)
    (t : (C.path.levels.clock.op m p).Choices) (x : fieldDir G (C.side m p) 1)
    (hC : C.Makes) (hs : ∀ d, Bid.pop (C.localSection d))

/-- Local coefficient datum at the top step for these actual (pre-quotient)
stencils and the exact Wilson action. One choice before orders. -/
def datum : LocalFormal.Datum C R where
  cutoff := m+1
  period := p
  level := m
  below := Nat.lt_succ_self _
  forest := F
  tag := t
  colors := Bare.bareUp R m p (H:=C.path) (stencilColors R U)
  field := x

local notation "W"=> Bare.bareUp R m p (H:=C.path) (stencilColors R U)
local notation "D" => datum R m p U F t x
local notation "I" => (Precision.Key F G → ℝ)
local notation "Ψ" => Conditional.vertices K F t W x
local notation "Λ" => Conditional.feed K F t
local notation "X" => Conditional.inputWord K F W x

include L hC hs in
theorem admitted : (W).Standard :=
  Bare.still_ok R L m p _ (stencil_well R U hC hs)

include hC hs in
lemma witnessed : Bare.Witnessed W K :=
  Bare.based R L m p _ (stencil_well R U hC hs) (stencil_starts R U)

-- parent origin (displaced within retained-field units)
def column (i : V) : RG10.Kernel (Unit × I) := fun a => PowerSeries.mk (fun n =>
    Assembly.jet (fun v : Bulk.Joint S F (G:=G) => field U i (Work.F03.live F v.2))
      (grade U i+n) (Bulk.translated K F x a.2))

lemma inputs (a : Unit × I) : X a = Word.emit R (fun i => column L m p U F x i a) := by
  unfold Conditional.inputWord
  apply MarkArithmetic.exp_is_emit
  · intro i
    let q : Hot R := ⟨R.fire i, by simp [Census.fire]⟩
    have hh : ∃ k : V, R.fire k = q.val := ⟨i,rfl⟩
    have he : hh.choose = i := (R.fire_inj ..).1 hh.choose_spec
    apply PowerSeries.ext; intro k
    change PowerSeries.coeff k (Word.see q.val _) = _
    rw [Conditional.cares, column, PowerSeries.coeff_mk,
      show (W).power q=grade U i from ?a_, Bulk.markFn,
      show (W).mark q=(fun _ => field U i) from ?x_]
    rfl
    case x_ => change (stencilColors R U).mark q=_; dsimp only [stencilColors, Bare.Signals.flare]; rw [dif_pos hh, he]
    case a_ => change (stencilColors R U).power q=_; dsimp only [stencilColors, Bare.Signals.flare]; rw [dif_pos hh, he]
  intro s ho; by_cases hx:s=R.quiet
  · subst s; exact Conditional.inputLog_quiet ..
  let i : Hot R := ⟨s,(Cumulants.hot_iff_ne _).2 hx⟩
  have hg : (W).power i=0 := dif_neg ho
  have hc : Bulk.markFn S F W i=0 := by
    unfold Bulk.markFn Bulk.posed
    rw [show (W).mark i=0 from dif_neg ho]; rfl
  apply PowerSeries.ext; intro k
  change PowerSeries.coeff k (Word.see i.val _) = _
  rw [Conditional.cares,hg,hc,map_zero]
  simp [Assembly.jet]

lemma factors (s : R.Mode) :
    Word.read s X = ∏ i∈s.val, column L m p U F x i := by
  rw [funext (fun a=> inputs L R m p U F x a)]
  exact Word.read_emitted ..

lemma columns_funded (s : R.Mode) : (Λ).Funded ((Ψ).weight * ∏ i∈s.val,column L m p U F x i) := by
  rw [← factors L R m p U F x, ← FlatFeed.totalize_read]
  exact Conditional.funded K F t W x s

theorem ordinary_column (s : R.Mode) {r k : ℕ} (hk : k ≤ r) :
    (D).ordinaryCoefficient L r k s =
      PowerSeries.coeff k ((Λ).ordinary Ψ s.val (column L m p U F x)) := by
  change (Order.observe R r (Order.ratio (Bulk.Fk K F t W x r)) k).part s = _
  rw [Conditional.ordinary, Order.observation _ _ _ hk, ← Word.unfold_see,
    FlatFeed.close_part,factors]
  rfl

lemma numerator_column (s : R.Mode) {r k : ℕ} (hk : k ≤ r) :
    (D).rawCoefficient L r k s = PowerSeries.coeff k
      ((Λ).average ((Ψ).weight * ∏ i∈s.val,column L m p U F x i)) := by
  change (Order.observe R r (Bulk.Fk K F t W x r) k).part s = _
  rw [Conditional.raw, Order.observation _ _ _ hk, ← Word.unfold_see,
    FlatFeed.column_eq, FlatFeed.totalize_read, factors]

theorem priced (g : ℝ) (Y : Config G f₁) (s : R.Mode) :
    (Bare.top W g Y).part s = ↑(Wilson.bare (Integral.temperature g) Y) *
      ∏ i ∈ s.val, (g^grade U i)⁻¹ • field U i Y := by
  unfold Bare.top
  rw [Poly.part_smul]
  change _ * (Poly.pass (Integral.markedLog g Y (stencilColors R U))).part s = _
  unfold stencilColors; rw [Bare.Signals.singleton, Cumulants.pass_lambda]

/-- The integral which is actually expanded at this matched finite geometry
(no Taylor cut; all fine links). -/
def torusFull (s : Finset V) (g : ℝ) :=
  (S).push (Integral.temperature g)
    (fun Y : Config G f₁ => ↑(Wilson.bare (Integral.temperature g) Y) *
      ∏ i∈s, (g^grade U i)⁻¹ • field U i Y) (Integral.sample g x)

def torusVacuum (g : ℝ) :=
  (S).push (Integral.temperature g) (Wilson.bare (Integral.temperature g)) (Integral.sample g x)

-- Include the precise thermal prefactor from completing square / g and chart dimensions.
lemma integrated (s : R.Mode) (g : ℝ) :
    (Bare.realMoment K F W t x g).part s =
      (Integral.office K F t g 0 x)⁻¹ • torusFull m p U x s.val g := by
  unfold Bare.realMoment
  rw [Poly.part_smul, Actual.grades, Complex.real_smul, Complex.ofReal_inv]
  have he : Actual.atMark s (Bare.top W g)=fun Y => ↑(Wilson.bare (Integral.temperature g) Y) *
      ∏ i∈s.val, (g^grade U i)⁻¹ • field U i Y := funext (fun Y=> priced R m p U g Y s)
  dsimp only
  rw [he]
  rfl

include L F t in
theorem positive (g : ℝ) (hg : 0 < g) : 0 < torusVacuum (C:=C) m p x g := by
  have he := Bare.rho_pos K F t x g hg
  have hv := Integral.office_pos K F t g 0 x hg
  exact pos_of_mul_pos_right he (inv_nonneg.mpr hv.le)

lemma normalized (s : R.Mode) {g : ℝ} (hg : 0 < g) :
    (Order.unitScale (Bare.realMoment K F W t x g)).part s =
      (torusVacuum (C:=C) m p x g)⁻¹ • torusFull m p U x s.val g := by
  unfold Order.unitScale
  rw [Poly.part_smul,Bare.vacancy,Bare.rho, integrated, Complex.real_smul, Complex.real_smul,
    Complex.ofReal_mul,Complex.ofReal_inv, Complex.ofReal_inv]
  have hp : (↑(Integral.office K F t g 0 x):ℂ) ≠ 0 := by
    exact_mod_cast (Integral.office_pos K F t g 0 x hg).ne'
  unfold torusVacuum
  field_simp

include hC hs

theorem full_numerator (s : R.Mode) : Aspiration
    (fun g => (Integral.office K F t g 0 x)⁻¹ • torusFull m p U x s.val g)
    (fun k => PowerSeries.coeff k
      ((Λ).average ((Ψ).weight * ∏ i∈s.val,column L m p U F x i))) := by
  intro n
  have hx := Bare.header K F W t x n (C.path.levels.budget (m+1)) (witnessed L R m p U hC hs) s
  refine Laplace.trial_flow (Laplace.trial_congr ?_ hx) ?_
  · exact Eventually.of_forall (fun _=> integrated L R m p U F t x s _)
  intro i hi
  exact numerator_column L R m p U F t x s hi

lemma full_denominator : Aspiration
    (fun g => (↑((Integral.office K F t g 0 x)⁻¹ * torusVacuum (C:=C) m p x g):ℂ))
    (fun k => PowerSeries.coeff k ((Λ).den Ψ)) := by
  intro n
  have hx := Bare.header K F W t x n (C.path.levels.budget (m+1)) (witnessed L R m p U hC hs) R.quiet
  refine Laplace.trial_flow (Laplace.trial_congr ?_ hx) ?_
  · exact Eventually.of_forall (fun _=> Bare.vacancy ..)
  intro i hi
  have hp := numerator_column L R m p U F t x R.quiet hi
  simp only [Census.quiet, Finset.prod_empty, mul_one] at hp
  exact hp

/-- Full and uncut normalized identification. Every finite order (tail
errors only at this finite geometry). Scale is ordinary powers of g after
paying **each** g^-rank and taking the ratio. -/
theorem full_step (s : R.Mode) : Aspiration
    (fun g => (torusVacuum (C:=C) m p x g)⁻¹ • torusFull m p U x s.val g)
    (fun k => PowerSeries.coeff k ((Λ).ordinary Ψ s.val (column L m p U F x))) := by
  intro n
  have hx := Bare.wilson_step_test K F W t x n (C.path.levels.budget (m+1))
    (witnessed L R m p U hC hs)
  refine Laplace.trial_flow (Laplace.trial_congr ?_ (hx.2.2.1 s)) ?_
  · filter_upwards [PertExtension.Series.Tested.eventually_pos] with g hg
    exact normalized L R m p U F t x s hg
  intro i hi
  exact ordinary_column L R m p U F t x s hi

theorem source_step_unique (s : R.Mode) (b : ℕ → ℂ) {n : ℕ} (hb : Laplace.Trial b
    (fun g => (torusVacuum (C:=C) m p x g)⁻¹ • torusFull m p U x s.val g) n) {k : ℕ} (hk : k≤n) :
    b k = (D).ordinaryCoefficient L n k s := by
  rw [ordinary_column L R m p U F t x s hk]
  exact trial_gap hb (full_step L R m p U F t x hC hs s n) _ hk

end YM.Integration.MSMatch.SourceTop
