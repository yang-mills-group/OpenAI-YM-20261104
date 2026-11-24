import YM.Integration.LocalComparisonInterface
import YM.Integration.NativePaidPacketColors
import YM.Integration.FullQLocalFullPreparedInputAt
import YM.Integration.ManuscriptQLocalMarkedGradeTail
import YM.Integration.ActualRunPacketRetuning

/-! The physical tariff on a marked packet is invariant when an integer power
is moved between its tagged Laurent monomial and its tensor at the same
nonzero physical coupling. The original power remains available for all
formal coefficient comparisons away from zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalPacketGrades
open Lattice Wilson RG Marker Precision Push.AbsoluteSums Comparison.Density.RenderM
open ActualRunPacketRetuning LocalComparison
open scoped BigOperators

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] {S : Census V}
    {D : V → ComparisonDensity.Address.Orbit} (P : MarkedPackets D G n S)

structure Grading where
  power : ℕ → ℤ
  cap : ℕ
  bounded i T : P.packet i = some T → (power i).natAbs ≤ cap
  nonnegative i T : P.packet i = some T → 0 ≤ power i + (P.rank i:ℤ)

namespace Grading
variable {P} (A : Grading P)

def coefficient (g : ℝ) (i : ℕ) : ℂ := (g:ℂ)^(P.power i-A.power i)

def amplified (c : ℕ → ℂ) : MarkedPackets D G n S where
  mode := P.mode
  rank := P.rank
  power := A.power
  packet i := (P.packet i).map (scaleToken (c i))
  marked i T h := by
    obtain ⟨Q,hQ,_⟩ := Option.map_eq_some_iff.mp h
    exact P.marked i Q hQ
  rankCap := P.rankCap
  powerCap := A.cap
  rank_bounded i T h := by
    obtain ⟨Q,hQ,_⟩ := Option.map_eq_some_iff.mp h
    exact P.rank_bounded i Q hQ
  power_bounded i T h := by
    obtain ⟨Q,hQ,_⟩ := Option.map_eq_some_iff.mp h
    exact A.bounded i Q hQ
  nonnegative_grade i T h := by
    obtain ⟨Q,hQ,_⟩ := Option.map_eq_some_iff.mp h
    exact A.nonnegative i Q hQ

def packets (g : ℝ) : MarkedPackets D G n S := A.amplified (A.coefficient g)

omit [DecidableEq V] in
private theorem scaled_touch {q : ℕ} (c : ℂ)
    (T : Token G n (fun v => (D v).Mood) q) (x : TestSpace D)
    (B : Fin q → G.Color) :
    (scaleToken c T).touch x B = c * T.touch x B := by
  unfold Token.touch scaleToken
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

omit [DecidableEq V] in
private theorem scaled_read {q : ℕ} (c : ℂ)
    (T : Token G n (fun v => (D v).Mood) q) (x : TestSpace D) (U : Config G n) :
    (scaleToken c T).read x U = c*T.read x U := by
  exact scaled_touch c T x (fun j => (T.path j).atSite U T.root)

theorem balance {g : ℝ} (hg : g ≠ 0) (i : ℕ) :
    (g:ℂ)^(A.power i)*A.coefficient g i = (g:ℂ)^(P.power i) := by
  have h : (g:ℂ) ≠ 0 := by exact_mod_cast hg
  rw [coefficient,← zpow_add₀ h]
  congr 1
  omega

theorem term {g : ℝ} (hg : g ≠ 0) (i : ℕ) (x : TestSpace D) (U : Config G n) :
    (A.packets g).term x g U i = P.term x g U i := by
  cases h : P.packet i with
  | none => simp [MarkedPackets.term,packets,amplified,h]
  | some T =>
    simp only [MarkedPackets.term,packets,amplified,h,Option.map_some,scaled_read]
    rw [← mul_assoc,A.balance hg]

theorem read [Fintype V] {g : ℝ} (hg : g ≠ 0) (x : TestSpace D) (U : Config G n) :
    (A.packets g).read x g U = P.read x g U := by
  unfold MarkedPackets.read
  exact tsum_congr fun i => congrArg (Poly.send (P.mode i)) (A.term hg i x U)

/-- The literal Laurent displacement at any independently chosen formal
coupling, prior to the original clearing and finite Wick extraction. -/
theorem formal {g t : ℝ} (ht : t ≠ 0) (i : ℕ) (x : TestSpace D) (U : Config G n) :
    (t:ℂ)^(P.power i-A.power i)*(A.packets g).term x t U i =
      A.coefficient g i*P.term x t U i := by
  have htc : (t:ℂ) ≠ 0 := by exact_mod_cast ht
  cases h : P.packet i with
  | none => simp [MarkedPackets.term,packets,amplified,h]
  | some T =>
    have hpow : (t:ℂ)^(P.power i-A.power i)*(t:ℂ)^(A.power i)=(t:ℂ)^(P.power i) := by
      rw [←zpow_add₀ htc,sub_add_cancel]
    simp only [MarkedPackets.term,packets,amplified,h,Option.map_some,scaled_read]
    linear_combination (A.coefficient g i*T.read x U)*hpow

/-- Every independent test, chart, address, cover and rooted triangle bill
is the original one at exactly the same physical coupling. -/
theorem billed (c : ℕ → ℂ) {g : ℝ}
    (balance : ∀ i, ‖(g:ℂ)^(A.power i)‖*‖c i‖ = ‖(g:ℂ)^(P.power i)‖)
    {B : BudgetPoint} {address : V → Support n}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
    {w : V → ℝ} {width budget : ℝ} {coverOffset coverSlope : ℕ}
    (hP : P.Paid B address region w g width budget coverOffset coverSlope) :
    (A.amplified c).Paid B address region w g width budget coverOffset coverSlope := by
  refine
    { width_pos := hP.width_pos
      positive := hP.positive
      coefficient := ?_
      paths := ?_
      addresses := ?_
      symmetry := ?_
      reads := ?_
      multilinear := ?_
      roots := ?_
      cover := ?_
      width_reserved := hP.width_reserved }
  · intro i Q hQ
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.mp hQ
    refine ⟨mul_nonneg (norm_nonneg _) (hP.coefficient i T hT).1, ?_⟩
    intro x
    change (∑ j, ‖(c i) * T.gem j (testInclusion D x)‖) ≤
      ‖c i‖ * T.coin
    simp only [norm_mul, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left ((hP.coefficient i T hT).2 x) (norm_nonneg _)
  · intro i Q hQ
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.mp hQ
    exact hP.paths i T hT
  · intro i Q hQ
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.mp hQ
    exact hP.addresses i T hT
  · intro i Q hQ x U k
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.mp hQ
    change (scaleToken (c i) T).touch x
        (fun j => G.adjoint k (U j)) =
      (scaleToken (c i) T).touch x U
    exact (scaled_touch (c i) T x _).trans
      ((congrArg (fun z : ℂ => (c i) * z)
        (hP.symmetry i T hT x U k)).trans
          (scaled_touch (c i) T x U).symm)
  · intro i Q hQ j x y hxy
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.mp hQ
    exact congrArg (fun z : ℂ => (c i) * z)
      (hP.reads i T hT j x y hxy)
  · intro i Q hQ j
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.mp hQ
    exact RG3.Held.Letter.cmul (c i) (hP.multilinear i T hT j)
  · intro v
    convert hP.roots v using 1
    funext i
    by_cases hv : v ∈ (P.mode i).val
    · cases h : P.packet i with
      | none => simp only [amplified,hv,if_true,h,Option.map_none]
      | some T =>
        simp only [amplified,hv,if_true,h,Option.map_some,scaleToken]
        rw [show ‖(g:ℂ)^(P.power i)‖ = ‖(g:ℂ)^(A.power i)‖*‖c i‖ by
          exact (balance i).symm]
        ring
    · simp only [amplified,if_neg hv]
  · intro i Q hQ
    obtain ⟨T,hT,rfl⟩ := Option.map_eq_some_iff.mp hQ
    exact hP.cover i T hT
theorem paid {g : ℝ} (hg : g ≠ 0)
    {B : BudgetPoint} {address : V → Support n}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
    {w : V → ℝ} {width budget : ℝ} {coverOffset coverSlope : ℕ}
    (hP : P.Paid B address region w g width budget coverOffset coverSlope) :
    (A.packets g).Paid B address region w g width budget coverOffset coverSlope := by
  apply A.billed (A.coefficient g) _ hP
  intro i
  rw [← norm_mul,A.balance hg]

theorem modulated (c z : ℕ → ℂ) (t : ℝ) (i : ℕ) (x : TestSpace D) (U : Config G n) :
    (A.amplified (fun i => z i*c i)).term x t U i =
      z i*(A.amplified c).term x t U i := by
  cases h : P.packet i with
  | none => simp [MarkedPackets.term,amplified,h]
  | some T =>
    simp only [MarkedPackets.term,amplified,h,Option.map_some,scaled_read]
    ring

end Grading

/-- For every original row the negative part is the effective power used
by the analytic tail. Its positive part is retained as a formal label. -/
def effective : Grading P where
  power i := min (P.power i) 0
  cap := P.powerCap
  bounded i T h := by
    by_cases z : P.power i ≤ 0
    · simpa only [min_eq_left z] using P.power_bounded i T h
    · simp [min_eq_right (le_of_lt (lt_of_not_ge z))]
  nonnegative i T h := by
    by_cases z : P.power i ≤ 0
    · simpa only [min_eq_left z] using P.nonnegative_grade i T h
    · simp [min_eq_right (le_of_lt (lt_of_not_ge z))]

theorem displacement (i : ℕ) :
    P.power i-(effective P).power i = ((P.power i).toNat:ℤ) := by
  change P.power i-min (P.power i) 0=_
  omega

theorem earned {B : BudgetPoint} {address : V → Support n}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
    {w : V → ℝ} {g width budget : ℝ} {offset slope : ℕ}
    (hP : P.Paid B address region w g width budget offset slope)
    (hg : 0 < g) (hweak : g ≤ 1) :
    ((effective P).packets g).Paid B address region w 1 width budget offset slope :=
  ManuscriptQLocalOriginalGradeTariff.unweighted _ ((effective P).paid hg.ne' hP)
    hg hweak (fun _ => min_le_right _ _)

/-- The auxiliary source variable is attached to the original marked
vertices. The physical coupling used for scaling the tensors stays real. -/
def phaseSource (g : ℝ) (ξ : ℂ) : MarkedPackets D G n S :=
  (effective P).amplified fun i => ξ^(P.power i).toNat*(effective P).coefficient g i

theorem phase_term (g t : ℝ) (ξ : ℂ) (i : ℕ) (x : TestSpace D) (U : Config G n) :
    (phaseSource P g ξ).term x t U i =
      ξ^(P.power i).toNat*((effective P).packets g).term x t U i :=
  (effective P).modulated _ _ t i x U

@[simp] theorem phase_one (g : ℝ) : phaseSource P g 1=(effective P).packets g := by
  simp only [phaseSource,Grading.packets,one_pow,one_mul]

theorem phase_paid {B : BudgetPoint} {address : V → Support n}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
    {w : V → ℝ} {g width budget : ℝ} {offset slope : ℕ}
    (hP : P.Paid B address region w g width budget offset slope)
    (hg : g ≠ 0) (ξ : ℂ) (hξ : ‖ξ‖=1) :
    (phaseSource P g ξ).Paid B address region w g width budget offset slope := by
  apply (effective P).billed _ _ hP
  intro i
  rw [norm_mul,norm_pow,hξ,one_pow,one_mul,←norm_mul,(effective P).balance hg]

theorem phase_earned {B : BudgetPoint} {address : V → Support n}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
    {w : V → ℝ} {g width budget : ℝ} {offset slope : ℕ}
    (hP : P.Paid B address region w g width budget offset slope)
    (hg : 0 < g) (hweak : g ≤ 1) (ξ : ℂ) (hξ : ‖ξ‖=1) :
    (phaseSource P g ξ).Paid B address region w 1 width budget offset slope :=
  ManuscriptQLocalOriginalGradeTariff.unweighted _ (phase_paid P hP hg.ne' ξ hξ)
    hg hweak (fun _ => min_le_right _ _)

/-- Reinsert a nonnegative total of displaced input powers in a genuine
output token, including every finite completion above the prescribed grade. -/
def restored (s : ℕ → ℕ) (K : ℕ) (hs : ∀ i, s i ≤ K) : Grading P where
  power i := P.power i + (s i:ℤ)
  cap := P.powerCap + K
  bounded i T h := by
    calc (P.power i+(s i:ℤ)).natAbs ≤ (P.power i).natAbs+s i := by
            simpa only [Int.natAbs_natCast] using Int.natAbs_add_le (P.power i) (s i:ℤ)
         _ ≤ _ := Nat.add_le_add (P.power_bounded i T h) (hs i)
  nonnegative i T h := by
    have orig := P.nonnegative_grade i T h
    omega

/-- A finite Wick or connected term can use only disjoint, nonempty source
modes. Its displaced degree is bounded before any source, lattice or tests
are chosen. -/
theorem total_displacement [Fintype V] {ι : Type} [Fintype ι] (rows : ι → ℕ)
    (live : ∀ j, ∃ T, P.packet (rows j) = some T)
    (separate : Pairwise fun i j =>
      Disjoint (P.mode (rows i)).val (P.mode (rows j)).val) :
    ∑ i, (P.power (rows i)).toNat ≤ Fintype.card V * P.powerCap := by
  classical
  have occupied (i : ι) : (P.mode (rows i)).val.Nonempty := by
    obtain ⟨T,hT⟩ := live i
    apply Finset.nonempty_iff_ne_empty.mpr
    exact fun h => P.marked (rows i) T hT (Subtype.ext h)
  choose v hv using occupied
  have distinct : Function.Injective v := by
    intro i j h
    by_contra hij
    exact (Finset.disjoint_left.mp (separate hij)) (hv i) (h.symm ▸ hv j)
  have one (i : ι) : (P.power (rows i)).toNat ≤ P.powerCap := by
    obtain ⟨T,hT⟩ := live i
    have hl : (P.power (rows i)).toNat ≤ (P.power (rows i)).natAbs := by
      cases P.power (rows i) <;> simp
    exact hl.trans (P.power_bounded _ T hT)
  calc ∑ i, (P.power (rows i)).toNat ≤ ∑ _ : ι, P.powerCap :=
        Finset.sum_le_sum fun i _ => one i
       _ = Fintype.card ι * P.powerCap := by simp
       _ ≤ _ := Nat.mul_le_mul_right _ (Fintype.card_le_of_injective v distinct)

/-- On the independently variable real chart the restored output has the
original lower-power rendering times its precise positive coupling ratio. -/
theorem restored_formula (s : ℕ → ℕ) (K : ℕ) (hs : ∀ i, s i ≤ K)
    {t g : ℝ} (ht : t ≠ 0) (i : ℕ) (x : TestSpace D) (U : Config G n) :
    ((restored P s K hs).packets g).term x t U i =
      ((t:ℂ)/(g:ℂ))^(s i) * P.term x t U i := by
  let A := restored P s K hs
  have t0 : (t:ℂ) ≠ 0 := by exact_mod_cast ht
  have power : P.power i-A.power i = -(s i:ℤ) := by
    change P.power i-(P.power i+(s i:ℤ))=_
    omega
  have eqn := A.formal (g:=g) ht i x U
  rw [Grading.coefficient,power,zpow_neg,zpow_neg,zpow_natCast,zpow_natCast] at eqn
  change (A.packets g).term x t U i=_
  calc
    _ = (t:ℂ)^(s i)*(((t:ℂ)^(s i))⁻¹ * (A.packets g).term x t U i) := by
          rw [←mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ t0),one_mul]
    _ = _ := by rw [eqn, div_pow,div_eq_mul_inv,mul_assoc]

/-- The original marked model is recovered by evaluating its displaced
source variable at t/g, for every genuine signed Laurent chart probe. -/
theorem effective_formula {t g : ℝ} (ht : t ≠ 0) (hg : g ≠ 0)
    (i : ℕ) (x : TestSpace D) (U : Config G n) :
    P.term x t U i = ((t:ℂ)/(g:ℂ))^((P.power i).toNat) *
      ((effective P).packets g).term x t U i := by
  have g0 : (g:ℂ) ≠ 0 := by exact_mod_cast hg
  have eqn := (effective P).formal (g:=g) ht i x U
  rw [Grading.coefficient,displacement,zpow_natCast,zpow_natCast] at eqn
  calc
    _ = ((g:ℂ)^(P.power i).toNat)⁻¹*((g:ℂ)^(P.power i).toNat*P.term x t U i) := by
          rw [←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ g0),one_mul]
    _ = _ := by rw [←eqn,div_pow,div_eq_mul_inv]; ring

theorem phase_recovery [Fintype V] {t g : ℝ} (ht : t ≠ 0) (hg : g ≠ 0)
    (x : TestSpace D) (U : Config G n) :
    (phaseSource P g ((t:ℂ)/(g:ℂ))).read x t U=P.read x t U := by
  unfold MarkedPackets.read
  apply tsum_congr
  intro i
  apply congrArg (Poly.send (P.mode i))
  rw [phase_term,←effective_formula P ht hg]

end YM.Integration.ManuscriptQLocalPacketGrades
end

/-! Effective-power and finite-phase presentations of a complete original
analytic input. Phase one uses the same prepared physical density and all
the same integrable exceptional activities at the actual fine coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalEffectiveInput
open Lattice Wilson RG Marker MeasureTheory Comparison.RG02
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric ManuscriptQLocalPacketGrades
open scoped Classical BigOperators

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
  {R : Census V} {C : Family G} {J : Request V} {A : NumericSchedule C J}
  {d : LocalFormal.Datum C R}
local notation "g₀" => Pert.Asymptotics.regulatorRun C d.cutoff d.period (d.level+1)
variable (F : AnalyticInput J A d)

def colors (ξ : ℂ) (x : TestSpace J.tests) :=
  NativePaidPacketColors.colors (phaseSource F.packets g₀ ξ) (F.colors x).vac x

theorem convention (hg : g₀ ≠ 0) (ξ : ℂ) (hξ : ‖ξ‖=1) :
    InputColors (colors F ξ) (phaseSource F.packets g₀ ξ) where
  well x :=
    let old := F.convention.well x
    NativePaidPacketColors.colors_well (phase_paid _ F.input_paid hg ξ hξ)
      hg (F.colors x).vac old.suppose_vac old.natural old.envelope x
  vacuum x y := F.convention.vacuum x y
  power _ _ := rfl
  marks x t ht U := NativePaidPacketColors.colors_markedLog
    (phase_paid _ F.input_paid hg ξ hξ) hg (F.colors x).vac x t ht U

/-- Each unit phase is an actual complete analytic datum on the original
history, with the original vacuum action and independent test domains. -/
def analytic (hg : g₀ ≠ 0) (ξ : ℂ) (hξ : ‖ξ‖=1) : AnalyticInput J A d :=
  { F with
    colors := colors F ξ
    packets := phaseSource F.packets g₀ ξ
    convention := convention F hg ξ hξ
    rank_bounded := F.rank_bounded
    power_bounded := F.power_bounded
    input_paid := phase_paid _ F.input_paid hg ξ hξ
    whole_input := {
      standard := fun x => ⟨(convention F hg ξ hξ).well x,(F.whole_input.standard x).2⟩
      input_summable := F.whole_input.input_summable
      inputExtension := F.whole_input.inputExtension
      formalInputExtension := F.whole_input.formalInputExtension
      input_extension_value := F.whole_input.input_extension_value
      formal_input_extension_value := F.whole_input.formal_input_extension_value
      input_extension_smooth := F.whole_input.input_extension_smooth
      formal_input_extension_smooth := F.whole_input.formal_input_extension_smooth
      input_whole := F.whole_input.input_whole } }

/-- The unweighted primitive bound is earned for the whole phased analytic
datum before any test is applied. -/
theorem bare (hg : 0 < g₀) (weak : g₀ ≤ 1) (ξ : ℂ) (hξ : ‖ξ‖=1) :
    (analytic F hg.ne' ξ hξ).packets.Paid (A.inputNorm d.level)
      F.inputAddresses F.inputRegion (fun v => F.inputRadii v / F.kernelCosts v)
      1 (A.inputWidth d.level) (A.admittedCost d.level) F.coverOffset F.coverSlope :=
  phase_earned _ F.input_paid hg weak ξ hξ

/-- At phase one the same incoming full representation, on every test and
group field, has precisely its original marked remainder and divided bill. -/
def prepared (hg : g₀ ≠ 0) {η : ℝ} (I : FullPreparedInputAt F η) :
    FullPreparedInputAt (analytic F hg 1 norm_one) η :=
  { I with
    prepared := {
      convention := convention F hg 1 norm_one
      remainder := I.prepared.remainder
      full := fun x U => by
        change (I.input.leaf x).density U =
          Poly.pass ((phaseSource F.packets g₀ 1).read x g₀ U) *
            (I.prepared.remainder.leaf x).density U
        rw [phase_one,Grading.read _ hg]
        exact I.prepared.full x U
      remainder_price := I.prepared.remainder_price } }

end YM.Integration.ManuscriptQLocalEffectiveInput
end


/-! The physical divisor of an original marked compulsory row is flat
before it is used in any integral. Its full rooted budget therefore buys
every prescribed finite auxiliary degree, at a common stage and for the
original support of every row. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalCompulsoryGrade
open Filter Finset Lattice Wilson RG Function Marker Push Push.AbsoluteSums
open PhysicalNext.Repeat LocalComparison ConnectedActivityE6 Pressure RG3.Script.Picnic
open scoped Topology Classical BigOperators

variable {G : Gauge}

/-- The native, whole-input divisor dominates any fixed boost up to the
entire current beta. This is independent of the cutoff and period. -/
theorem physical_divisor (C : Family G) (hG : G.Simple) (d : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ C.path.levels.clock.hatBeta m →
      ρ^d * forcedDivisor C m ≤ 1 := by
  let D := C.path.levels
  have goes : Tendsto D.clock.hatBeta atTop atTop :=
    tendsto_atTop_add_const_left _ _ (D.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos hG))
  have flat : Rate G (1:Side) (-((d:ℝ)+1)) Blush.glyph := by
    refine Rate.congr (Rate.monitor_cutoff (δ:=1/2) (γ:=1/5) ?_ ?_) ?_
    · norm_num
    · norm_num
    filter_upwards with x
    unfold Blush.glyph
    dsimp only [AbsoluteSums.Delay.fineMonitor]
    rw [Real.sqrt_eq_rpow,← Real.exp_mul]
    simp [betaF]
    ring_nf
    rfl
  have rate := flat (-(d:ℝ)) (by linarith)
  filter_upwards [goes.eventually rate,goes.eventually_ge_atTop 1] with m hm great
  let β := D.clock.hatBeta m
  have hβ : 0 < β := zero_lt_one.trans_le great
  have small : forcedDivisor C m ≤ β^(-(d:ℝ)) := by
    have same : betaF G β (1:Side) = β := by simp [betaF]
    change |Blush.glyph β| ≤ (betaF G β (1:Side))^(-(d:ℝ)) at hm
    rw [same] at hm
    exact (le_abs_self _).trans hm
  intro ρ hρ hcap
  calc ρ^d*forcedDivisor C m ≤ β^d*β^(-(d:ℝ)) :=
          mul_le_mul (pow_le_pow_left₀ hρ hcap _) small (Real.sqrt_nonneg _) (pow_nonneg hβ.le _)
       _ = 1 := by rw [← Real.rpow_natCast,← Real.rpow_add hβ,add_neg_cancel,Real.rpow_zero]

variable {n : Side} {V X : Type} [DecidableEq V] {Γ : Census V}
    {P : Rep G n} {o : V → Site n} {T : Taste X o P Γ} {w : V → ℝ}
    {p : BudgetPoint} {κ b f : ℝ}

def rowPrice (H : FullBudget p T w κ b f) (v : V) (i : ℕ × ℕ) :=
  if v ∈ (T.menu.marks i.1 i.2).val then
    Poly.toll w (T.menu.marks i.1 i.2) * p.mass (P.activities.forced i.1).support (H.black i)
  else 0

/-- This is precisely the paid forced-total integrand, still carrying
its input marks, test tariff, physical support and all original rows. -/
theorem graded_roots (H : FullBudget p T w κ b f) (v : V) (charge : ℝ)
    (hcharge : 0 ≤ charge) (receipt : charge*κ ≤ 1) :
    SumBudget (fun i => charge * rowPrice H v i) f := by
  have paid : SumBudget (rowPrice H v) (κ*f) := H.forcedTotal v
  have hf : 0 ≤ f := nonneg_of_mul_nonneg_right (budget_nonneg paid) H.divisor
  apply budget_loosen (budget_scale hcharge paid)
  calc charge*(κ*f) = (charge*κ)*f := (mul_assoc ..).symm
       _ ≤ 1*f := mul_le_mul_of_nonneg_right receipt hf
       _ = f := one_mul _

/-- A single original fine-stage threshold pays for every inherited
compulsory source, every physical charge radius up to beta, each actual
root, and all finite test rosters. -/
theorem earned (C : Family G) (hG : G.Simple) (d : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (H : FullBudget p T w (forcedDivisor C m) b f)
      (v : V) (ρ : ℝ), 0 ≤ ρ → ρ ≤ C.path.levels.clock.hatBeta m →
        SumBudget (fun i => ρ^d * rowPrice H v i) f := by
  filter_upwards [physical_divisor C hG d] with m hm
  exact fun H v ρ hρ hc => graded_roots H v _ (pow_nonneg hρ _) (hm ρ hρ hc)
end YM.Integration.ManuscriptQLocalCompulsoryGrade
