import YM.Integration.WilsonUniformUnmarkedCommonStrip
import YM.Integration.WilsonUniformUnmarkedMomentTail

/-! One common subsequence for every occupied field tuple and admitted
date at a fixed order. The definition makes no claim about orders
outside the funded cap, nor about a gauge-complete extension there. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonUniformUnmarkedCompact
open Filter Function Finset PowerSeries Lattice RG Wilson Tree Stationary Push.Uniform Bloch Exterior Precision
open FormalBulk08 Jets Flat Reef Mesa Lava Shore Lotus Wine Bank Orb Next.Free Series Gorge
open PhysicalNext.Repeat.Legato MSbar MSbar.Heath MSbar.Rolling MSbar.Cacao MSbar.Midpoint MSbar.Bakery
open RG16 RG16.Literal Pert.Asymptotics WilsonConditionalTaylorBulkHistory
open scoped Classical Topology BigOperators ENNReal

variable {G : Gauge}
abbrev Keys (G : Gauge) := ℕ × ℕ × (Σ r : ℕ,chain (edgeL G) (r+1))

def coordinate (R : Run G) (u : G.ColorIndex)
    (wood : ∀ j,Lodge (R.family.path.levels.clock.op j 0).patch)
    (tags : ∀ j n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)
    (N per : ℕ) (q : Keys G) : ℝ :=
  let j:=q.1
  let n:=R.family.side j per
  rancho (course R u wood tags N j n) q.2.1 (q.2.2.1+1) (drip n ∘ q.2.2.2)

def Capped (R : Run G) (u : G.ColorIndex)
    (wood : ∀ j,Lodge (R.family.path.levels.clock.op j 0).patch)
    (tags : ∀ j n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)
    (k E : ℕ) (N per a : ℕ→ℕ) (A : ℕ→Mesa.Pot G) : Prop :=
  ∀ (j e r : ℕ), k ≤ j → 0<e → e ≤ E → r ≤ e+1 → ∀ w : chain (edgeL G) (r+1),
    Tendsto (fun t => coordinate R u wood tags (N (a t)) (per (a t)) (j,e,⟨r,w⟩))
      atTop (𝓝 (A j e (r+1) w))

def capPrice (C : Family G) (j : ℕ) := 2/(C.path.levels.clock.hatCoupling j)

theorem physicalPrice (R : Run G) (N per j : ℕ) (hi : j ≤ N) :
    (regulatorRun R.family N per j)⁻¹ ≤ capPrice R.family j := by
  let h:=R.family.path.levels.clock.hatCoupling j
  let g:=regulatorRun R.family N per j
  have h0 : 0<h := inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans (R.family.path.levels.fits.delayed j)))
  have g0 : 0<g := RG16.Literal.g_pos R.makes hi
  have price : h ≤ 2*g := (IterationFour.Currency.hat_g R.makes N per j hi).1
  change g⁻¹ ≤ 2/h
  rw [←one_div]
  exact (div_le_div_iff₀ g0 h0).mpr (by simpa only [one_mul] using price)

variable (R : Run G) (simple : G.Simple) (u : G.ColorIndex) (V : Voice G)
variable (bought : WilsonConditionalTaylorPurchase.Inventory u V R.kit)
variable (wood : ∀ j,Lodge (R.family.path.levels.clock.op j 0).patch)
variable (tags : ∀ j n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)

include bought simple in
theorem collected (E : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ (N per : ℕ→ℕ), Tendsto N atTop atTop →
      ∃ (a : ℕ→ℕ) (A : ℕ→Mesa.Pot G), StrictMono a ∧ Capped R u wood tags k E N per a A := by
  filter_upwards [WilsonUniformUnmarkedCommonStrip.purchased R simple u V bought wood tags E zero_lt_one]
    with k ledger N per fine
  let shown (t : ℕ) (q : Keys G) := k ≤ q.1 ∧ q.1 ≤ N t ∧ 0<q.2.1 ∧ q.2.1 ≤ E ∧ q.2.2.1 ≤ q.2.1+1
  let bank (t : ℕ) (q : Keys G) :=
    if shown t q then coordinate R u wood tags (N t) (per t) q else 0
  let box (q : Keys G):=Metric.closedBall (0:ℝ) (capPrice R.family q.1)
  have inside (t : ℕ) : ∀ q, bank t q ∈ box q := by
    intro q
    have h0 : 0 ≤ capPrice R.family q.1 := div_nonneg (by norm_num) (show 0 < R.family.path.levels.clock.hatCoupling q.1 from inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans (R.family.path.levels.fits.delayed _)))).le
    change dist (bank t q) 0 ≤ _
    rw [Real.dist_eq,sub_zero]
    by_cases Q : shown t q
    · obtain ⟨lo,hi,pos,cap,val⟩:=Q
      let n:=R.family.side q.1 (per t)
      let U:=course R u wood tags (N t) q.1 n
      let σ:=Alto.candles R.family.path.levels q.1/4
      let v:=drip n ∘ q.2.2.2
      have paid:=ledger (N t) (per t) (lo.trans hi) q.1 lo hi q.2.1 pos cap q.2.2.1 val
      have point:=Lotus.palmed paid v (0:Fin (q.2.2.1+1))
      have sig : 0≤σ := div_nonneg (WilsonUniformUnmarkedMomentTail.localWidth R.family q.1).le (by norm_num)
      have one : 1 ≤ Real.exp (σ*(wide (lake n _) v:ℝ)) :=Real.one_le_exp (mul_nonneg sig (Nat.cast_nonneg _))
      rw [show bank t q=coordinate R u wood tags (N t) (per t) q from if_pos ⟨lo,hi,pos,cap,val⟩]
      change |rancho U q.2.1 (q.2.2.1+1) v| ≤ _
      have h:=le_mul_of_one_le_left (norm_nonneg (rancho U q.2.1 (q.2.2.1+1) v)) one
      calc
        _ ≤ (regulatorRun R.family (N t) (per t) q.1) ^ (-(1:ℝ)) := by simpa only [Real.norm_eq_abs] using (h.trans point)
        _ ≤ _ := by simpa only [Real.rpow_neg_one] using physicalPrice R (N t) (per t) q.1 hi
    · rw [show bank t q=0 from if_neg Q,abs_zero];exact h0
  obtain ⟨f,_fits,a,mono,tends⟩ := (isCompact_pi_infinite (s:=box) (fun _=>isCompact_closedBall ..)).tendsto_subseq inside
  let A (j e : ℕ) : (r : ℕ)→Tile (edgeL G) r :=
    fun r=>match r with
    | 0=>0
    | r+1=>fun w=>f (j,e,⟨r,w⟩)
  refine ⟨a,A,mono,?_⟩
  intro j e r lo positive cap val w
  let q : Keys G :=(j,e,⟨r,w⟩)
  have valAt:=tendsto_pi_nhds.mp tends q
  apply valAt.congr'
  filter_upwards [(fine.comp mono.tendsto_atTop).eventually_ge_atTop j] with t paid
  exact if_pos ⟨lo,paid,positive,cap,val⟩

end YM.Integration.WilsonUniformUnmarkedCompact
