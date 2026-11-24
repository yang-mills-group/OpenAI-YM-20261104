import YM.Integration.PhysicalWilsonRootedHessian
import YM.Integration.PhysicalWilsonSignedOutput
import YM.Integration.WilsonLimitConstruction.FundedPhysicalCatalogue
import YM.Integration.WilsonLimitConstruction.FundedSpringLocalClock
import YM.Integration.WilsonLimitConstruction.FundedSpringMovingLaw
import YM.WilsonCoeffUV.Winding.Gazette

/-! The finite Wilson action, its thermal contact and the separately issued
canonically periodized vacuum and nonempty marked coefficients. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.PhysicalWilsonPricedOutput
open Function Filter Lattice Wilson RG Precision Exterior Gauge Marker
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 Comparison.RG02.Assembly PhysicalWilsonRootedHessian
open Pert.Asymptotics WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Winding
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Blue
open WilsonLimitConstruction
open scoped Topology ContDiff Classical BigOperators

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {S : Census V}
variable (T : Run G) (d : LocalFormal.Datum T.family S)
local notation "n" => T.family.side d.level d.period
local notation "nf" => T.family.side (d.level+1) d.period
local notation "X" => fieldDir G n 1
local notation "g₀" => regulatorRun T.family d.cutoff d.period (d.level+1)

/-- The actual incoming-coupling chart of the finite positive Wilson measure. -/
def action (g : ℝ) (U : Config G n) : ℝ :=
  FundedSpringMovingLaw.action T d.cutoff d.period
    (FundedSpringLocalClock.clock T d.cutoff d.period (d.level+1) g) d.level d.below.le U

omit [Fintype V] in
theorem measured (U : Config G n) :
    action T d g₀ U = PhysicalWilsonActionConvention.physicalAction T d.cutoff d.period d.level U := by
  unfold action
  rw [FundedSpringLocalClock.endpoint T d.cutoff d.period (d.level+1) (Nat.succ_le_of_lt d.below)]
  exact FundedSpringMovingLaw.endpoint T d.cutoff d.period d.level d.below.le U

def centered (g : ℝ) (B : X) : ℂ :=
  ((action T d g (represent (g • B)) - action T d g 1 : ℝ):ℂ)

variable {J : Request V} {A : NumericSchedule T.family J} {K : NumericPrices A}
variable (Y : Bulk.Chain T.family.path)
def finiteQuiet (W : Bulk.Colors S G nf) (k : ℕ) (B : X) : ℂ :=
  Symmetry.Orbit.ground (d.kernel Y) d.forest d.tag W J.order k 0 -
  Symmetry.Orbit.ground (d.kernel Y) d.forest d.tag W J.order k B

def finiteMarked (W : Bulk.Colors S G nf) (k : ℕ) (B : X) : Poly S :=
  Order.observe S J.order (({d with colors := W,field := B} : LocalFormal.Datum T.family S).markedLog Y J.order) k

def planQuiet (P : Plan T.family d.cutoff d.period J.order) (k : ℕ) (B : X) : ℂ :=
  jet (SelectedPlanClearedNumerator.numerator T P d.level) (2+k) (1,B) -
    jet (SelectedPlanClearedNumerator.numerator T P d.level) (2+k) (1,0)

/-- The charged cover ray is an actual evaluation of the chosen packet bank at
every nonzero coupling. Its finite and periodized coefficient comparisons are separate. -/
structure MarkedRay (P : MarkedPackets J.tests G n S) where
  summable (x : TestSpace J.tests) (g : ℝ) (hg : g≠0) (U : Config G n) :
    Summable (fun i => Poly.send (P.mode i) (P.term x g U i))
  extension : TestSpace J.tests → ℝ → X → Poly S
  value (x : TestSpace J.tests) (g : ℝ) (hg : g≠0) (B : X) :
    extension x g B = P.read x g (represent (g • B))
  smooth (x : TestSpace J.tests) (B : X) : ContDiffAt ℝ J.order (fun g => extension x g B) 0

section
variable {T d}
def MarkedRay.coefficient {P : MarkedPackets J.tests G n S} (E : MarkedRay T d P)
    (x : TestSpace J.tests) (k : ℕ) (B : X) : Poly S :=
  (k.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ k (fun g => E.extension x g B) 0 (fun _ => 1)

end

def MarkedRay.fromFinite {P : MarkedPackets J.tests G n S}
    {w : TestSpace J.tests → Bulk.Colors S G nf} (E : PrescribedPackets Y d w P J.order) :
    MarkedRay T d P := ⟨E.summable,E.extension,E.value,E.smooth⟩

theorem MarkedRay.finite {P : MarkedPackets J.tests G n S}
    {w : TestSpace J.tests → Bulk.Colors S G nf} (E : PrescribedPackets Y d w P J.order)
    (x : TestSpace J.tests) (k : ℕ) (hk : k ≤ J.order) (B : X) :
    finiteMarked (J:=J) T d Y (w x) k B - (MarkedRay.fromFinite T d Y E).coefficient x k B = 0 :=
  sub_eq_zero.mpr (E.coefficients x B k hk).symm

def table {l : ℕ} (f : X → ℂ) (z : Fin l → Label G n) : ℂ :=
  (l.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ l f 0 (fun j => unit (z j))

def form (l : ℕ) (f : (Fin l → Label G n) → ℂ) (B : X) : ℂ :=
  ∑ z, ((∏ i, coordinate B (z i) : ℝ):ℂ)*f z

/-- The actual chosen cover array and the original same-tag finite reference carry positive action sign. -/
def quietCover (k : ℕ) : (l : ℕ) → (Fin l → Label G n) → ℂ
  | 0, _ => ((freshet T.family.path.levels T.metals.O d.cutoff d.level k 0 (fun i => i.elim0) : ℝ) : ℂ)
  | l+1, z => ((lagoon (freshet T.family.path.levels T.metals.O d.cutoff d.level k (l+1)) n z : ℝ) : ℂ)
def quietReference (k l : ℕ) (z : Fin l → Label G n) : ℂ :=
  ((coil0 T.family.path.levels T.metals.O d.level d.cutoff n k l z:ℝ):ℂ)

/-- A marked native bank, together with its original linear reading on the
entire independent test array. The bank is fixed before the marks move. -/
structure Origin (J : Request V) where
  dims : V → ℕ
  orders : V → ℕ
  input : (V → Cover) → family G dims
  reader (s : S.Mode) : TestSpace J.tests → Pen dims s.val →L[ℝ] ℂ

def address (p : V → Site n) (o : V) (v : V) : Cover := lift (p o) + lift (p v-p o)

def Origin.cover (O : Origin (G:=G) (S:=S) J) (s : S.Mode) (o : V) (p : V → Site n)
    (x : TestSpace J.tests) (k l : ℕ) (z : Fin l → Label G n) : ℂ :=
  O.reader s x (Carp.plume ((logO T.family.path.levels T.metals.O d.level d.cutoff
    (O.input (address T d p o)) O.orders s.val).2 k l) n z)
def Origin.reference (O : Origin (G:=G) (S:=S) J) (s : S.Mode) (o : V) (p : V → Site n)
    (x : TestSpace J.tests) (k l : ℕ) (z : Fin l → Label G n) : ℂ :=
  O.reader s x (coilH T.family.path.levels T.metals.O d.level d.cutoff n
    (O.input (address T d p o)) O.orders (ratioHigh T.family.path.levels T.metals.O d.cutoff d.level)
    s.val k l z)

def span (p : Finset (Site n)) : ℕ := p.sup fun x => p.sup fun y => separation x y

def quietHeld {l : ℕ} (width : ℝ) (s : Fin l) (o : Label G n)
    (Q : (Fin l → Label G n) → ℂ) : ℝ :=
  ∑ z, if z s=o then Real.exp (width*span T d (Finset.univ.image fun i => (z i).1))*‖Q z‖ else 0

def markedHeld {l : ℕ} (s : S.Mode) (o : s.val) (root : Site n) (width : ℝ)
    (Q : (s.val → Site n) → (Fin l → Label G n) → ℂ) : ℝ :=
  ∑ p, if p o=root then ∑ z, Real.exp (width*span T d
    (Finset.univ.image p ∪ Finset.univ.image fun i => (z i).1))*‖Q p z‖ else 0

def position {s : S.Mode} (base : V → Site n) (p : s.val → Site n) (v : V) : Site n :=
  if h : v∈s.val then p ⟨v,h⟩ else base v

structure Prices where
  width : ℕ → ℝ
  positive : ∀ m, 0 < width m
  legCap : ℕ
  debt : ℕ
  degree : ℕ
  cutRate : ℕ → ℝ
  windingRate : ℕ → ℝ
  cut_positive : ∀ m, 0 < cutRate m
  winding_positive : ∀ m, 0 < windingRate m

def Prices.cut (S₀ : Prices) (K : NumericPrices A) : ℝ :=
  K.geometry d.level * (A.admittedCost d.level)^S₀.degree * g₀^(-(S₀.debt:ℝ)) *
    Real.exp (-S₀.cutRate d.level*(T.family.path.levels.clock.coverSize d.level:ℝ))
def Prices.wind (S₀ : Prices) (K : NumericPrices A) : ℝ :=
  K.geometry d.level * (A.admittedCost d.level)^S₀.degree * g₀^(-(S₀.debt:ℝ)) *
    Real.exp (-S₀.windingRate d.level*(T.family.side d.level d.period).val)

/-- Exact prices before field re-expression, with the true measured density and
the two distinct signed tables down to every test, field direction and marker address. -/
structure Output (caps : Handoff.OutputCapacities) (K : NumericPrices A) (F : AnalyticInput J A d)
    (O : Origin (G:=G) (S:=S) J) (b : Prices) extends FundedPhysicalCatalogue.Purchase caps K F where
  marked : MarkedRay T d toPurchase.model
  moved : (V → Site n) → TestSpace J.tests → Bulk.Colors S G nf
  assigned : moved F.coarseRoots = F.colors
  trial (x : TestSpace J.tests) (B : X) :
    Laplace.Trial (fun k => finiteQuiet (J:=J) T d Y (F.colors x) k B)
      (fun g => centered T d g B) J.order
  placedModel : (V → Site n) → MarkedPackets J.tests G n S
  placedRay (a : V → Site n) : MarkedRay T d (placedModel a)
  model_value (x : TestSpace J.tests) (g : ℝ) (U : Config G n) :
    (placedModel F.coarseRoots).read x g U = toPurchase.model.read x g U
  model_ray (x : TestSpace J.tests) (g : ℝ) (B : X) :
    (placedRay F.coarseRoots).extension x g B = marked.extension x g B
  quietField (k : ℕ) (hk : k≤J.order) (x : TestSpace J.tests) (B : X) :
    let D := fun y => finiteQuiet (J:=J) T d Y (F.colors x) k y - planQuiet T d toPurchase.plan k y
    D B = ∑ l ∈ Finset.range (b.legCap+1), form T d l (fun z => table T d D z) B
  markedField (s : S.Mode) (_o : s.val) (k : ℕ) (hk : k≤J.order) (x : TestSpace J.tests) (B : X) :
    ((finiteMarked (J:=J) T d Y (F.colors x) k B).part s - (marked.coefficient x k B).part s) =
    ∑ l ∈ Finset.range (b.legCap+1), form T d l (fun z =>
      table T d (fun y => (finiteMarked (J:=J) T d Y (F.colors x) k y).part s) z -
      table T d (fun y => (marked.coefficient x k y).part s) z) B
  quietCut (k l : ℕ) (hk : k≤J.order) (hl : l≤b.legCap) (x : IndependentTests J.tests)
      (s : Fin l) (o : Label G n) :
    quietHeld T d (b.width d.level) s o (fun z =>
      table T d (finiteQuiet (J:=J) T d Y (F.colors (testInclusion J.tests x)) k) z -
      quietReference T d k l z + (quietCover T d k l z - table T d (planQuiet T d toPurchase.plan k) z))
      ≤ b.cut T d K
  quietWind (k l : ℕ) (hk : k≤J.order) (hl : l≤b.legCap) (s : Fin l) (o : Label G n) :
    quietHeld T d (b.width d.level) s o (fun z => quietReference T d k l z - quietCover T d k l z)
       ≤ b.wind T d K
  markedCut (s : S.Mode) (o : s.val) (k l : ℕ) (hk : k≤J.order) (hl : l≤b.legCap)
      (x : IndependentTests J.tests) (root : Site n) :
    (∏ v ∈ s.val, F.outputRadii v/F.kernelCosts v) *
      markedHeld T d s o root (b.width d.level) (fun p z =>
        let h := position T d F.coarseRoots p
        table T d (fun B => (finiteMarked (J:=J) T d Y (moved h (testInclusion J.tests x)) k B).part s) z -
        O.reference T d s o h (testInclusion J.tests x) k l z +
        (O.cover T d s o h (testInclusion J.tests x) k l z -
          table T d (fun y => ((placedRay h).coefficient (testInclusion J.tests x) k y).part s) z))
      ≤ b.cut T d K
  markedWind (s : S.Mode) (o : s.val) (k l : ℕ) (hk : k≤J.order) (hl : l≤b.legCap)
      (x : IndependentTests J.tests) (root : Site n) :
    (∏ v ∈ s.val, F.outputRadii v/F.kernelCosts v) *
      markedHeld T d s o root (b.width d.level) (fun p z =>
        let h := position T d F.coarseRoots p
        O.reference T d s o h (testInclusion J.tests x) k l z -
        O.cover T d s o h (testInclusion J.tests x) k l z) ≤ b.wind T d K

omit [Fintype V] in
theorem add_quiet {l : ℕ} (width : ℝ) (slot : Fin l) (root : Label G n)
    (Q H : (Fin l → Label G n) → ℂ) :
    quietHeld T d width slot root (fun z => Q z+H z) ≤
      quietHeld T d width slot root Q + quietHeld T d width slot root H := by
  unfold quietHeld
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro z _
  by_cases h : z slot = root
  · simp only [if_pos h,←mul_add]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.exp_pos _).le
  · simp [h]

omit [Fintype V] in
theorem add_mark {l : ℕ} (s : S.Mode) (o : s.val) (root : Site n) (width : ℝ)
    (Q H : (s.val → Site n) → (Fin l → Label G n) → ℂ) :
    markedHeld T d s o root width (fun p z => Q p z+H p z) ≤
      markedHeld T d s o root width Q + markedHeld T d s o root width H := by
  unfold markedHeld
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p _
  by_cases h : p o = root
  · simp only [if_pos h,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro z _
    rw [←mul_add]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.exp_pos _).le
  · simp [h]

variable {caps : Handoff.OutputCapacities} {F : AnalyticInput J A d}
    {O : Origin (G:=G) (S:=S) J} {b : Prices}
    (M : Output T d Y caps K F O b)

theorem quiet_total (k l : ℕ) (hk : k≤J.order) (hl : l≤b.legCap)
    (x : IndependentTests J.tests) (slot : Fin l) (root : Label G n) :
    quietHeld T d (b.width d.level) slot root (fun z =>
      table T d (finiteQuiet (J:=J) T d Y (F.colors (testInclusion J.tests x)) k) z -
      table T d (planQuiet T d M.plan k) z) ≤ b.cut T d K + b.wind T d K := by
  let f := table (l:=l) T d (finiteQuiet (J:=J) T d Y (F.colors (testInclusion J.tests x)) k)
  let m := table (l:=l) T d (planQuiet T d M.plan k)
  let c := quietCover T d k l
  let q := quietReference T d k l
  change quietHeld T d _ slot root (fun z => f z-m z) ≤ _
  have e : (fun z => f z-m z) =
      (fun z => (f z-q z+(c z-m z))+(q z-c z)) := by funext z; abel
  rw [e]
  exact (add_quiet T d _ slot root _ _).trans (add_le_add
    (M.quietCut k l hk hl x slot root) (M.quietWind k l hk hl slot root))

theorem marked_total (s : S.Mode) (o : s.val) (k l : ℕ) (hk : k ≤ J.order)
    (hl : l ≤ b.legCap) (x : IndependentTests J.tests) (root : Site n) :
    (∏ v ∈ s.val, F.outputRadii v/F.kernelCosts v) *
      markedHeld T d (l:=l) s o root (b.width d.level) (fun p z =>
        let h := position T d F.coarseRoots p
        table T d (fun B => (finiteMarked (J:=J) T d Y (M.moved h (testInclusion J.tests x)) k B).part s) z -
        table T d (fun B => ((M.placedRay h).coefficient (testInclusion J.tests x) k B).part s) z) ≤
      b.cut T d K + b.wind T d K := by
  let pos := position (s:=s) T d F.coarseRoots
  let v := testInclusion J.tests x
  let f (a : s.val → Site n) (z : Fin l → Label G n) :=
    table T d (fun B => (finiteMarked (J:=J) T d Y (M.moved (pos a) v) k B).part s) z
  let m (a : s.val → Site n) (z : Fin l → Label G n) :=
    table T d (fun B => ((M.placedRay (pos a)).coefficient v k B).part s) z
  let c (a : s.val → Site n) := O.cover T d s o (pos a) v k l
  let q (a : s.val → Site n) := O.reference T d s o (pos a) v k l
  let w := ∏ j ∈ s.val, F.outputRadii j/F.kernelCosts j
  have hw : 0 ≤ w := Finset.prod_nonneg fun j _ => div_nonneg (F.output_radius_positive j).le
    (F.kernel_positive j).le
  change w * markedHeld T d s o root _ (fun p z => f p z - m p z) ≤ _
  have e : (fun p z => f p z-m p z) =
    (fun p z => (f p z-q p z+(c p z-m p z))+(q p z-c p z)) := by funext p z; abel
  rw [e]
  apply LE.le.trans (mul_le_mul_of_nonneg_left (add_mark T d s o root _ _ _) hw)
  rw [mul_add]
  exact add_le_add (M.markedCut s o k l hk hl x root) (M.markedWind s o k l hk hl x root)

/-- Public contact projection of the stronger exact finite prescription. Independent identification
with either native cover periodization or its paid short-window rendering still has its own rooted invoices. -/
theorem from_exact {caps : Handoff.OutputCapacities} {F : AnalyticInput J A d}
    (M : PhysicalWilsonActionConvention.SignedAnalyticOutput caps Y K F) (x : TestSpace J.tests)
    (k : ℕ) (hk : k≤J.order) (B : X) :
    finiteQuiet (J:=J) T d Y (F.colors x) k B - planQuiet T d M.plan k B = 0 ∧
    finiteMarked (J:=J) T d Y (F.colors x) k B -
      (MarkedRay.fromFinite T d Y M.prescribed).coefficient x k B = 0 :=
  ⟨sub_eq_zero.mpr (PhysicalWilsonActionConvention.centered_ground T M x B k hk).symm,
    MarkedRay.finite T d Y M.prescribed x k hk B⟩

end YM.Integration.PhysicalWilsonPricedOutput
