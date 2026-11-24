import YM.Integration.FundedOriginalCoefficientWindows
import YM.Integration.FundedOriginalMarkedInput

/-! Turn actual finite source rows into the donor's pre-block bank. Both the
strong winding comparison and the complete curvature-path lease use the same
priced family. The only sums charged before selection are on the original
colours, words, addresses, and labelled source rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalIssuedMarkedRows
open Function Filter Lattice RG Wilson Precision Next.Foundations
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Winding
open WilsonCoeffUV.Embroider WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls Work.F08
open IndependentSourcePathFamily FundedMarkedPathSelection MeasureTheory
open scoped Classical BigOperators

variable {G : Gauge} {v : Type} [Fintype v] [DecidableEq v]
variable {D k : v → ℕ} {I : v → Type} [∀ i, Fintype (I i)]
variable (X : ∀ i, I i → Seed G (D i))
variable {e m N : ℕ} (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m)
variable (w : Gear G → ℝ) (hw : ∀ I, 0 < w I)
variable (Z J : Finset v) (cells : (v → Cover) → v → Site (loose Q.draws m).L)

private def width := max (w (Q.mint m hm).gear) (Q.mint (m+1) (by omega)).σ

/-- The physical finite Haar colour/derivative bill, evaluated before the
independent tests and without a factor of the running coupling. -/
def fee : ℝ := bill X k e (4*width Q hm w)

private def position (y : v → Cover) := chartIn (loose Q.draws m) y (cells y)

include hw in
private theorem primitive (h : ∀ i b, (X i b).rank ≤ k i + (X i b).head) (y : v → Cover) :
    let A := fee (k:=k) X Q hm w
    let p := position Q cells y
    let raw := independent X p
    0 ≤ A ∧ Eu k raw ∧ raw ∅ = 0 ∧ safeB p raw Z e (width Q hm w) A := by
  have pos : 0 < width Q hm w := (hw _).trans_le (le_max_left ..)
  have base := preblock X (k:=k) (position Q cells y) Z e (show 0 < 4*width Q hm w by positivity) h
  simpa only [fee,show steep (4*width Q hm w) = width Q hm w by unfold steep; ring] using base

/-- The input for the genuine selected `waltz` trees. -/
def input (h : ∀ i b, (X i b).rank ≤ k i + (X i b).head) :
    Input Q hm Z k D (fee (k:=k) X Q hm w) where
  familyAt y := independent X (position Q cells y)
  offsets := cells
  empty y := (primitive X Q hm w hw Z cells h y).2.2.1
  degree y := (primitive X Q hm w hw Z cells h y).2.1
  price y J hJ i hi r :=
    ((primitive X Q hm w hw Z cells h y).2.2.2 J hJ i hi r).shave (le_max_right ..)

theorem enters (h : ∀ i b, (X i b).rank ≤ k i + (X i b).head) :
    let bank := input X Q hm w hw Z cells h
    let A := fee (k:=k) X Q hm w
    0 ≤ A ∧ ∀ y, Eu k (bank.familyAt y) ∧ (bank.familyAt y) ∅=0 ∧
      safeB (position Q cells y) (bank.familyAt y) Z e (w (Q.mint m hm).gear) A := by
  refine ⟨(primitive X Q hm w hw Z cells h 0).1,fun y => ⟨?_,?_,?_⟩⟩
  · exact (primitive X Q hm w hw Z cells h y).2.1
  · exact (primitive X Q hm w hw Z cells h y).2.2.1
  · intro K hK i hi r
    exact ((primitive X Q hm w hw Z cells h y).2.2.2 K hK i hi r).shave (le_max_left ..)

/-- Complete original thin field/colour paths with their joint derivative
and source-displacement measures, before external field/test evaluation. -/
def Lease {A : ℝ} (bank : Input Q hm Z k D A) (N i : ℕ) (o : v) (origin : Cover)
    (r : Fin (mass k J+i+1)) : Prop :=
  let width := VestS J.card (mass k J) Q m hm
  let rows := packetH J (output bank J N) (mass k J) (e+1) o origin
  let Z := fun a : Frill J o => rows a i r
  ∃ μ : (a : Frill J o × RadP G r.val) → Stationary.Ink G r.val → Measure (Sky D),
    (∀ a, Barn (Z a.1 a.2) (μ a)) ∧
    SumBudget (fun a : Frill J o × RadP G r.val =>
      Real.exp (width*feeH (toe J o origin a.1) o J)*lease (Z a.1 a.2) (μ a) width)
      (glacier G (mass k J) (e+1) * VestZ J.card (mass k J) Q m hm *
        price Q k D A J m * sprigs J o (Vσ Q m hm))

/-- The periodic rendering on these rows uses the same independently
selected periodization. -/
def Renders {A : ℝ} (bank : Input Q hm Z k D A) (N i : ℕ) (o : v) : Prop :=
  ∀ y : v → Cover,
    let P := sphere (output bank J N y) (mass k J) (e+1) o y
    let T := shifted (baton P (e+1)) (y o)
    Auth (mass k J) T ∧ T.2 i = (output bank J N y).2 i ∧
      ∀ n r, T.1 n i r = Carp.plume ((output bank J N y).2 i r) n

private theorem grant {A : ℝ} (bank : Input Q hm Z k D A) (ha : 0 ≤ A) (hJ : J ⊆ Z)
    (closed : Cloze D k Q Credit.leanC) (tickets : Insure J.card (mass k J) Q Credit.leanC)
    (o : v) (ho : o ∈ J) (hN : m < N) (i : ℕ) (hi : i ≤ e) :
    Renders Q hm Z J bank N i o ∧
      ∀ (origin : Cover) (r : Fin (mass k J+i+1)), Lease Q hm Z J bank N i o origin r :=
  ⟨fun _ => rendering bank hJ ha hN closed J.card le_rfl tickets o ho _ i (Nat.lt_succ_of_le hi),
    fun _ _ => measured bank hJ ha hN closed J.card le_rfl tickets o ho _ i (Nat.lt_succ_of_le hi) _⟩

section original
variable {n i r d c q : ℕ} {R : Run G} {J Z : Finset (Fin n)} {o : Fin n}
    {k D : Fin n → ℕ} {w s : Gear G → ℝ}

/-- The joint rendered cover invoice and the genuine marked winding invoice,
produced on the same realm for one independently named raw input bank. -/
def Award (R : Run G) (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m)
    (J Z : Finset (Fin n)) (o : Fin n) (s : Gear G → ℝ) (N p i r d c q : ℕ)
    {A : ℝ} (bank : Input Q hm Z k D A) : Prop :=
  let n₀ := R.family.side m p
  let g := Pert.Asymptotics.regulatorRun R.family N p (m+1)
  let t := fun z => PeriodicMarkedWinding.roots n₀ z o
  let F := fun z => (output bank J N (t z)).2 i r
  let P := fun z => coilH Q.draws Q.paid m N n₀ (bank.familyAt (t z)) k
    (ratioHigh Q.draws Q.paid N m) J i r
  Renders Q hm Z J bank N i o ∧
  (∀ (origin : Cover) (u : Fin (mass k J+i+1)), Lease Q hm Z J bank N i o origin u) ∧
  ∃ B, B * g^(-(c:ℝ)) ≤ g^q*A^J.card ∧
    PostMark J o r (RootedPeriodicMarkedWinding.row n₀ J o (fun z => Carp.plume (F z) n₀ - P z))
      (s (Q.mint m hm).gear/32/2/2/2) B d

/-- The incoming `familyAt` may contain genuine correlated higher marked
vertices. Its pre-block receipt has only an input norm and the native
grading. Its complete output address and path measures are manufactured. -/
theorem all (hJ : J ⊆ Z) (ho : o ∈ J) (hi : i ≤ e)
    (stage : FundedMarkedWindingWindow.Window R J Z o D k e i r d c q w s m) :
    ∃ (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m),
      Q.draws = R.family.path.levels ∧ Q.paid = R.metals.O ∧
      ∀ N p, m < N → ∀ A : ℝ, ∀ bank : Input Q hm Z k D A, 0 ≤ A →
        (∀ y, safeB (chartIn (loose Q.draws m) y (bank.offsets y)) (bank.familyAt y)
          Z e (w (Q.mint m hm).gear) A) → Award R Q hm J Z o s N p i r d c q bank := by
  obtain ⟨Q,hm,draws,paid,_,closed,tickets,stock⟩ := stage
  refine ⟨Q,hm,draws,paid,?_⟩
  intro N p hN A bank hA fine
  have paid := grant Q hm Z J bank hA hJ closed tickets o ho hN i hi
  exact ⟨paid.1,paid.2,stock N p hN bank.familyAt bank.offsets A hA
    (fun y => ⟨bank.degree y,bank.empty y,fine y⟩)⟩

/-- Every presold genuine independent input shares its output path lease
with the strongly measured finite winding row on the actual torus. -/
theorem select (hJ : J ⊆ Z) (ho : o ∈ J) (hi : i ≤ e) (hw : ∀ I, 0 < w I)
    (stage : FundedMarkedWindingWindow.Window R J Z o D k e i r d c q w s m) :
    ∃ (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m),
      Q.draws = R.family.path.levels ∧ Q.paid = R.metals.O ∧
      ∀ N p, m < N → ∀ (I : Fin n → Type) [∀ j, Fintype (I j)] (X : ∀ j, I j → Seed G (D j))
          (h : ∀ j b, (X j b).rank ≤ k j + (X j b).head)
          (cells : (Fin n → Cover) → Fin n → Site (loose Q.draws m).L),
        let bank := input X Q hm w hw Z cells h
        Award R Q hm J Z o s N p i r d c q bank := by
  obtain ⟨Q,hm,draws,paid,stock⟩ := all hJ ho hi stage
  refine ⟨Q,hm,draws,paid,?_⟩
  intro N p hN I fI X h cells bank
  have pre := enters X Q hm w hw Z cells h
  exact stock N p hN _ bank pre.1 (fun y => (pre.2 y).2.2)

/-- At the real ultraviolet opening the original frozen Haar tensor,
directions and chart derivatives themselves produce the joint window. The
complete complex source is the finite independent sum over its quadratures. -/
theorem frozen {p n₀ : ℕ} {h₀ : n₀ ≤ m+1} {B : MS.Local.Physical.Deck G}
    (P : MS.Land.Prescription B) (a : ActualRunQlocalNativeTuple.Datum R p (m+1) n₀ h₀ (Fin n))
    (u : Fin n → MS.Rake.Label B) (μ : ℝ) (orders : Fin n → ℕ) (normal : Fin n → ℂ)
    (quad : Fin n → Bool) (hJ : J ⊆ Z) (ho : o ∈ J) (hi : i ≤ e) (hw : ∀ I, 0 < w I)
    (stage : FundedMarkedWindingWindow.Window R J Z o (FundedOriginalMarkedInput.OrbitD a) k
      e i r d c q w s m) :
    ∃ (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m),
      Q.draws = R.family.path.levels ∧ Q.paid = R.metals.O ∧
        ∀ cells : (Fin n → Cover) → Fin n → Site (loose Q.draws m).L,
          let X := FundedOriginalMarkedInput.chosen P a u μ orders normal quad
          let bank := input X Q hm w hw Z cells (fun j _ => Nat.le_add_left _ (k j))
          Award R Q hm J Z o s (m+1) p i r d c q bank := by
  obtain ⟨Q,hm,draws,paid,stock⟩ := select hJ ho hi hw stage
  refine ⟨Q,hm,draws,paid,?_⟩
  intro cells X bank
  exact stock (m+1) p (Nat.lt_succ_self m) (FundedOriginalMarkedInput.Count a u) X
    (fun j b => Nat.le_add_left _ (k j)) cells

end original
end YM.Integration.OriginalIssuedMarkedRows
end
