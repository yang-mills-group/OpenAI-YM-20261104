import YM.Integration.WilsonMixedFaceLog
import YM.Integration.WilsonOriginalClubSourceReference

/-! One finite original Gaussian for an inherited marked face and a newly filed Q face. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMixedFiniteMaterial
open Finset Lattice Wilson RG Tree Source Labels Marker Multi Exterior
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureSalary WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope
open QuadraticLocal.Earn AllOrder.Floe Comparison.RG02 WilsonMixedFaceLog
open private staff from YM.Integration.WilsonOriginalClubSourcePackets
open scoped Classical BigOperators

section routing
variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] {C : Census V}
  (old fresh : Finset V) (A B : Bulk.Colors C G n)

private def source (v : Hot C) : Bulk.Colors C G n :=
  if v.val.val ⊆ old then A else if v.val.val ⊆ fresh then B else Bulk.Colors.noHole G n C

def bank : Bulk.Colors C G n where
  vac := A.vac
  mark v := (source old fresh A B v).mark v
  power v := (source old fresh A B v).power v

theorem standard (a : A.Standard) (b : B.Standard) : (bank old fresh A B).Standard := by
  have legal (v : Hot C) : (source old fresh A B v).Standard := by
    unfold source
    split
    · exact a
    split
    · exact b
    · exact Bulk.Colors.no_hole G n C
  exact ⟨⟨a.1.suppose_vac, fun v => (legal v).1.suppose_mark v, a.1.natural,
    fun v t => (legal v).1.gauges v t, a.1.envelope, fun v t => (legal v).1.prices v t⟩, a.2⟩

private theorem parts (apart : Disjoint old fresh) (g : ℝ) (U : Config G n) (s : C.Mode) :
    (Integral.markedLog g U (bank old fresh A B)).part s =
      (if s.val ⊆ old then (Integral.markedLog g U A).part s else 0) +
      (if s.val ⊆ fresh then (Integral.markedLog g U B).part s else 0) := by
  by_cases active : s.val.Nonempty
  · let v : Hot C := ⟨s, active⟩
    change (Integral.markedLog g U (bank old fresh A B)).part v.val = _
    unfold Integral.markedLog
    rw [Multi.part_lit _ v, show s = v.val from rfl, Multi.part_lit _ v, Multi.part_lit _ v]
    by_cases first : s.val ⊆ old
    · have last : ¬s.val ⊆ fresh := by
        intro both
        obtain ⟨a, ha⟩ := active
        exact Finset.disjoint_left.mp apart (first ha) (both ha)
      simp only [bank, source, v, if_pos first, if_neg last, add_zero]
    · by_cases last : s.val ⊆ fresh
      · simp only [bank, source, v, if_neg first, if_pos last, zero_add]
      · simp only [bank, source, v, if_neg first, if_neg last, Bulk.Colors.noHole, Pi.zero_apply, smul_zero, add_zero]
  · have quiet : s = C.quiet := not_not.mp (fun h => active ((Cumulants.hot_iff_ne s).mpr h))
    subst s
    simp only [Integral.markedLog, Multi.part_lit_quiet, ite_self, add_zero]
end routing

variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {per i n : ℕ} {hn : n ≤ i+1} {V : Type} [DecidableEq V] [Fintype V]
  (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R per (i+1) n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ) (N : ℕ)
  (σ : ℝ) (extra : V → ℕ) (layout : Layout G) (tape : Finset Age)
  {ι α γ : Type} {P : Passport (R.family.side (i+1) per) V}
  (M : ι → Row P (Stock.census V) G α) (old fresh : Finset V) (sep : Disjoint old fresh)
  (leftTest : γ → α) (rightTest : γ → tastes D) (x : γ)

local notation "Y" => WilsonOriginalProjectedCurvatureLamps.cohort Q D u μ orders N σ extra
local notation "gradesQ" => (fun _ : V => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u)
local notation "S" => routed M Y old fresh sep leftTest rightTest
variable (grades jointGrades : V → ℕ)
local notation "X" => Air.craft M (fun j => (M j).paint (leftTest x)) grades layout tape
local notation "J" => Air.craft S (fun j => (S j).paint x) jointGrades layout tape
local notation "Q₀" => Air.craft Y (fun j => (Y j).paint (rightTest x)) gradesQ layout tape
local notation "test" => testInclusion (ActualRunQlocalNativeTuple.orbit D) (rightTest x)
local notation "packets" => ActualOriginalQPackets.packets Q D u μ orders N
local notation "actualQ" => NativePaidPacketColors.colors packets (X).vac test
local notation "filed" => bank old fresh X actualQ

theorem original {w₀ w : V → ℝ} {s₀ s c₀ c : ℝ} {k₀ d₀ e₀ k d e : ℕ}
    (oldRows : Scene.Armada M w₀ grades s₀ c₀ k₀ d₀ e₀) (oldPositive : 0 < s₀)
    (joinedRows : Scene.Armada S w jointGrades s c k d e) (positive : 0 < s)
    (below : i < N) (legal : Legal tape layout) (point : BudgetPoint)
    (F : Forest (R.family.path.levels.clock.op i per).ratio) (tag : (R.family.path.levels.clock.op i per).Choices)
    (b : fieldDir G (R.family.side i per) 1) (r : ℕ) :
    (J).Standard ∧ (filed).Standard ∧
    (∀ g, g ≠ 0 → ∀ U, Integral.markedLog g U J = Integral.markedLog g U filed) ∧
    Bulk.Fk ((RunFormalChain.fromRun R).step N i per below) F tag J b r =
      Bulk.Fk ((RunFormalChain.fromRun R).step N i per below) F tag filed b r ∧
    PhysicalWilsonPeriodizedMaterial.reference R N i per below b J r =
      PhysicalWilsonPeriodizedMaterial.reference R N i per below b filed r := by
  have hM := Air.license M (fun j => (M j).paint (leftTest x)) grades w₀ oldRows oldPositive
    (fun j => oldRows.honor j (leftTest x))
  have hS := Air.license S (fun j => (S j).paint x) jointGrades w joinedRows positive (fun j => joinedRows.honor j x)
  obtain ⟨_, hQ⟩ := staff Q D u μ orders N σ extra (rightTest x)
  have ideal : (actualQ).Standard := (WilsonOriginalClubSourceReference.original Q D u μ orders N σ extra
    layout tape (rightTest x) below legal point F tag b r).2.1
  have authentic := Air.standard S _ jointGrades hS layout tape legal
  have checked := standard old fresh X actualQ (Air.standard M _ grades hM layout tape legal) ideal
  have paid := ActualOriginalQPackets.packets_paid Q D u μ orders N point (fun _ => 1) 1 zero_lt_one (fun _ => zero_lt_one)
  have hg := (IterationFour.Currency.g_pos R.makes N per (i+1) below).ne'
  have read (g : ℝ) (nonzero : g ≠ 0) (U : Config G (R.family.side (i+1) per)) :
      Integral.markedLog g U J = Integral.markedLog g U filed := by
    have block : Integral.markedLog g U Q₀ = Integral.markedLog g U actualQ :=
      (WilsonOriginalClubSourcePackets.original Q D u μ orders N σ extra layout tape
        (rightTest x) point g nonzero U).trans (NativePaidPacketColors.colors_markedLog paid hg (X).vac test g nonzero U).symm
    funext v
    exact (WilsonMixedFaceLog.original M Y old fresh sep leftTest rightTest grades gradesQ jointGrades layout tape x
      hM hQ hS point g nonzero U v).trans (by rw [block]; exact (parts old fresh X actualQ sep g U v).symm)
  have finite := WilsonNormalizedMarkedSource.formal ((RunFormalChain.fromRun R).step N i per below)
    F J filed authentic.1 checked.1 read tag rfl b r
  exact ⟨authentic, checked, read, finite,
    (PhysicalWilsonPeriodizedMaterial.original R N i per below b J r F tag authentic.1).symm.trans
      (finite.trans (PhysicalWilsonPeriodizedMaterial.original R N i per below b filed r F tag checked.1))⟩

end YM.Integration.WilsonOriginalMixedFiniteMaterial
