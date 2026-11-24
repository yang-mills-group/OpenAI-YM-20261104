import YM.Integration.WilsonOriginalReceivedFiledChain
import YM.Integration.WilsonReceivedForcedExit

/-! The actual registered receiving hard array, at renewed individual native radii. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFiledHardRebill
open FVA1 Finset Function MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity QuadraticLocal.Tint Pressure ConnectedActivityE6
open WilsonOriginalReceivedChain Ac AbsoluteSums Progress.DirectedRecipe
open scoped Classical BigOperators Topology

section HardArray
variable {G:Gauge} {n:Side} {p:BudgetPoint} {V T:Type} [DecidableEq V]
  {M:Marker.Census V} {o o':V→Site n} {S:Activities G n}

theorem smaller (H:Hard T p S.forced S.K o M) {w w':V→ℝ} {B:ℕ} {a b:ℝ}
    (positive:∀i,0<w' i) (within:∀i,w' i≤w i) (paid:H.Paid w B a b) :
    H.Paid w' B a b := by
  have price (x:Poly M) : Poly.price w' x ≤ Poly.price w x := by
    apply Finset.sum_le_sum
    intro u _
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact Finset.prod_le_prod (fun i _ => (positive i).le) (fun i _ => within i)
  obtain ⟨f,hf,actual⟩:=paid.wages
  refine ⟨f,hf,fun i=>budget_mono (actual i) ?_ ?_⟩
  · intro j
    split
    · exact mul_nonneg (Poly.nonnegative positive _) (Real.exp_nonneg _)
    · rfl
  · intro j
    split
    · exact mul_le_mul_of_nonneg_right (price _) (Real.exp_nonneg _)
    · rfl

private theorem transported {H:Hard T p S.forced S.K o M} {F:Hard T p S.forced S.K o' M}
    (roots:o'=o) (same:HEq F H) {w:V→ℝ} {B:ℕ} {a b:ℝ} (paid:H.Paid w B a b) :
    F.Paid w B a b := by
  cases roots
  exact (eq_of_heq same).symm ▸ paid
end HardArray

variable {G : Gauge} (R : Run G) {m j N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ i, RG.Rep G (R.family.side i per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ) (floor : m ≤ j)
  (physical : Wallet actors → Config G (R.family.side ((j+1)+1) per) → Poly (Stock.census V))
local notation "up" => floor.trans (Nat.le_succ j)
variable (P : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1) (floor.trans (Nat.le_succ j)) physical)
variable (F : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats j floor (fun x:Wallet actors => LocalComparison.actualPush R.family N per (j+1) (physical x)))
  (filed : Filed R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor physical P F)
local notation "heat" => R.alloy.B.a.clock.hatBeta ((j+1)+1)
local notation "κ" => LocalComparison.forcedDivisor R.family (j+1)
local notation "B₁" => (Ψ (j+1)).p.B
local notation "a₁" => (Ψ (j+1)).p.supportExponent

include filed
/-- Keep the actual outgoing array before any radius decrease made by the report. -/
theorem original (live:j+1<N) (way:WayStation R.kit)
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (q:ℕ) (active:q+6*seats≤R.alloy.B.a.clock.J (j+1))
    (w:V→ℝ) (positive:∀i,0<w i) (within:∀i,w i≤P.w i) :
    F.input.hard.Paid w B₁ a₁ (heat^(-(q:ℝ))*κ) := by
  have paid:=WilsonReceivedForcedExit.original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats up physical P live way course q active
  have held:=smaller P.output.hard positive within paid
  have origin := congrArg Earn.Passport.origin filed.passport
  exact transported origin filed.hard held

/-- If rebooking exceeds the incoming radii by at most an adjacent clock power, the
same ordered output pays for it before the regulator and retains the requested flat order. -/
theorem enlarged (live:j+1<N) (way:WayStation R.kit)
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (q e c:ℕ) (cap:∀s:(Stock.census V).Mode,s.val.card≤c)
    (active:q+e*c+6*seats≤R.alloy.B.a.clock.J (j+1))
    (w:V→ℝ) (positive:∀i,0<w i) (within:∀i,w i≤P.w i*heat^e) :
    F.input.hard.Paid w B₁ a₁ (heat^(-(q:ℝ))*κ) := by
  have hx:1≤heat := (R.alloy.B.a.fits.delayed _).le
  have xp:0<heat := zero_lt_one.trans_le hx
  have scale:0<heat^e:=pow_pos xp _
  have one:1≤heat^e:=one_le_pow₀ hx
  have reduced:∀i,Stoop.radius w (heat^e) i≤P.w i :=
    fun i => (div_le_iff₀ scale).2 (within i)
  have paid:=original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor
    physical P F filed live way course (q+e*c) active (Stoop.radius w (heat^e))
    (fun i=>div_pos (positive i) scale) reduced
  have restored:=Stoop.budget w cap F.input.hard positive one paid
  have balance:(heat^e)^c*(heat^(-((q+e*c:ℕ):ℝ))*κ)=heat^(-(q:ℝ))*κ := by
    rw [← pow_mul,Real.rpow_neg xp.le,Real.rpow_natCast,Real.rpow_neg xp.le,Real.rpow_natCast,pow_add]
    field_simp
  exact Hard.mono _ restored balance.le

end YM.Integration.WilsonOriginalFiledHardRebill
end
