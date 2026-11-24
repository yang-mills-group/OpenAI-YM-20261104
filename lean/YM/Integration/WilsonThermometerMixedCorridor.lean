import YM.Integration.WilsonReceivedGalleryEnlarged
import YM.Integration.WilsonThermometerMixedTandemWallet
import YM.Integration.WilsonSingleHardSchedule
import YM.MergeProof.South.Window

/- The original measured steps carry all eight faces through any finite short collar.
   Only the marker radius depends on its length; the regular and hard incomes stay
   at their native sizes. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerMixedCorridor
open Function Finset Filter Lattice Wilson RG Tree Marker QuadraticLocal Ac
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open WheelP AnalyticBridge VerifiedReset PhysicalNext PhysicalNext.Repeat Legato
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {N per m k b t:ℕ}
local notation "β" j:max => R.alloy.B.a.clock.hatBeta j
local notation "stage" j:max => R.alloy.B.a.clock.J j
local notation "J" => Stock.census (Fin 3)
local notation "place" j:max => Fin 3→Site (R.family.side j per)
local notation "κ" j:max => LocalComparison.forcedDivisor R.family j
local notation "scene" j:max => Config G (R.family.side j per)

def rent (j:ℕ):ℝ:= min (Beaming.spray (β (j+1))) ((β (j+1))^(Beaming.grain (stage j)))

def factor (j:ℕ):ℝ:=max 1 (rent R j)

def sites (o:place t){j:ℕ}(jt:j≤t):place j:=
  Nat.decreasingInduction (motive:=fun j _=>place j)
    (fun j _ z=>(R.family.path.levels.clock.op j per).ratio.parent ∘ z) o jt

def wallet (w:Fin 3→ℝ){j:ℕ}(jt:j≤t):Fin 3→ℝ:=
  Nat.decreasingInduction (motive:=fun _ _=>Fin 3→ℝ)
    (fun j _ z=>Stoop.radius z (factor R j)) w jt

theorem positive (w:Fin 3→ℝ)(hw:∀v,0<w v){j:ℕ}(jt:j≤t) : ∀v,0<wallet R w jt v:=by
  refine Nat.decreasingInduction (motive:=fun j jt=>∀v,0<wallet R w jt v) ?_ ?_ jt
  · intro j lt ih
    rw [show wallet R w lt.le=Stoop.radius (wallet R w lt) (factor R j) from Nat.decreasingInduction_succ_left ..]
    exact fun v=>div_pos (ih v) (zero_lt_one.trans_le (le_max_left ..))
  · rw [show wallet R w (le_refl t)=w from Nat.decreasingInduction_self ..]; exact hw

private lemma weaker {X I:Type}{n:Side}{p:BudgetPoint}{o:Fin 3→Site n}
    (A:Lamps X I G p o (J))(w:Fin 3→ℝ)(hw:∀v,0<w v){B:ℕ}{a a' C:ℝ}
    (paid:A.Paid w B a C)(he:a'≤a): A.Paid w B a' C:=by
  obtain ⟨f,hf,hF,hH⟩:=paid.budget
  refine ⟨f,hf,hF,fun x=>budget_mono (hH x) ?_ ?_⟩
  · intro i;split
    · exact mul_nonneg (mul_nonneg (Poly.worth hw _).le (hf _)) (Real.exp_nonneg _)
    · exact le_rfl
  · intro i;split
    · exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right he (by positivity)))
        (mul_nonneg (Poly.worth hw _).le (hf _))
    · exact le_rfl

variable (way:WayStation R.kit) (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q:D.Tab R.rolls)(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(Ψ:∀i,RG.Rep G (R.family.side i per))
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)(ticket:TicketP R.alloy R.kit D Q)
    {X I:Type} [Countable I] [Nonempty X]
    (o:Fin 3→Site (R.family.side t per))(A:Gallery X I o (Ψ t) (J))(w:Fin 3→ℝ)(hw:∀v,0<w v)

include course way ticket hw in
theorem original (floor:m≤b) (top:t≤N)(bt:b≤t)
    (stage₀:∀ (i : ℕ), b ≤ i → 3 ≤ (stage i)) (cap:∀ (i : ℕ), b ≤ i → (κ i) ≤ 1)
    (regular:A.E.Paid w (Ψ t).p.B ((Ψ t).p.supportExponent+2) 1)
    (hard:A.K.Paid w (Ψ t).p.B (Ψ t).p.supportExponent (κ t)):
    ∃ (K:Type)(L:Gallery X K (sites R o bt) (Ψ b) (J)), Countable K ∧
      L.E.Paid (wallet R w bt) (Ψ b).p.B ((Ψ b).p.supportExponent+2) 1 ∧
      L.K.Paid (wallet R w bt) (Ψ b).p.B (Ψ b).p.supportExponent (κ b) ∧
      ∀x,L.density x=gust R.family.path N per t (A.density x) b bt := by
  refine Nat.decreasingInduction (motive:=fun j jt=>b ≤ j → ∃(K:Type)(L:Gallery X K (sites R o jt) (Ψ j) (J)), Countable K ∧
      L.E.Paid (wallet R w jt) (Ψ j).p.B ((Ψ j).p.supportExponent+2) 1 ∧
      L.K.Paid (wallet R w jt) (Ψ j).p.B (Ψ j).p.supportExponent (κ j) ∧
      ∀x,L.density x=gust R.family.path N per t (A.density x) j jt) ?_ ?_ bt le_rfl
  · intro j lt ih bj
    obtain ⟨K,L,hK,ready,forced,matched⟩:=ih (bj.trans (Nat.le_succ j))
    letI:Countable K:=hK
    have wp:=positive R w hw lt
    let src:=wallet R w lt
    have entry:L.Pays src (Ψ (j+1)).p.supportExponent 1 1:=
      ⟨weaker L.E src wp ready (by linarith),Hard.mono _ forced (cap _ (bj.trans (Nat.le_succ j)))⟩
    have alive:=lt.trans_le top
    obtain ⟨K',P,hK',wide,tap,seen⟩:=WilsonReceivedGalleryEnlarged.original R way D Q π Γ Ψ course ticket
      (floor.trans bj) alive src wp L entry (stage₀ j bj) (fun s=>by simpa using card_le_univ s.val)
    rw [show sites R o lt.le=(R.family.path.levels.clock.op j per).ratio.parent ∘ sites R o lt
        from Nat.decreasingInduction_succ_left ..,
      show wallet R w lt.le=Stoop.radius src (factor R j) from Nat.decreasingInduction_succ_left ..]
    have dpos:0<factor R j:=zero_lt_one.trans_le (le_max_left ..)
    have reprice:(factor R j)⁻¹*rent R j ≤ 1:=(inv_mul_le_one₀ dpos).2 (le_max_right ..)
    have budget:=Stoop.tighten src P.E wp (le_max_left 1 (rent R j)) wide
    have output:=Advent.force_bill R way π Γ Ψ course (floor.trans bj) alive (Nat.zero_le (stage j))
    rw [Nat.cast_zero,neg_zero,Real.rpow_zero,one_mul] at output
    refine ⟨K',P,hK',?_,Stoop.leaves src P.K wp (le_max_left ..) (Hard.mono _ tap output),?_⟩
    · have h:=Lamps.loan_monotone _ budget reprice
      rw [show (Ψ j).p.supportExponent+1+1=(Ψ j).p.supportExponent+2 by ring] at h
      exact h
    intro x
    rw [seen x,matched x,gust_step R.family.path N per t (A.density x) lt]
    rfl
  ·
    intro _
    rw [show sites R o (le_refl t)=o from Nat.decreasingInduction_self ..,
      show wallet R w (le_refl t)=w from Nat.decreasingInduction_self ..]
    refine ⟨I,A,inferInstance,regular,hard,?_⟩
    intro x
    unfold gust
    rw [Nat.decreasingInduction_self]
end YM.Integration.WilsonThermometerMixedCorridor
end
