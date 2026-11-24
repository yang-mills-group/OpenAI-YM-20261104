import YM.GradedFar.Logged.Trace

/-! Single scale log payment in S units, fixed caps PREFIX (`Book` estimate) -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Logged.RootRoom
open Finset Filter Function Set Spec Table Extraction OPE.Log Asymptotics Orbits
open scoped Topology Classical BigOperators
open Economy (Paint)
variable {G:Gauge}{C:Family G}{f:Order}{S:Table C.book}
    (F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {I J L:Type}[Fintype I][Fintype J] (K:Economy.Small L) {M δ:ℝ}(hm:0≤M)(hd:0<δ)
    {x:L→I→E4} {o:L→E4} (hx:∀ᶠ i in K.p,WithinRoom (K.r i) M δ (x i) (o i))
    {d:I→ℕ}
    (bank : LogTrace F R.port) (v: Labels S d) (s:L→Viewers F)
local notation "r"=>K.r
local notation "P"=>R.port
local notation "bare"=>Stage.bare

-- RAW whole no ext, compare all v and price via SingleLog. Don't assume stationary sizes in Growing t, since this is still on basis (even dimensionful).
include hm hd hx bank
local notation "A"=> (fun i:L=> (r i)⁻¹^(∑ j,d j))
lemma grain (b:Mode F.sector.derivatives)(zero:b.fst=0) : Paint K A (fun i=> R.port.ope b (x i) (names v) (o i)) := by
    obtain ⟨k,h⟩:= bank.terms I (names v) δ M hd hm b
    refine Paint.from_cost 1 zero_lt_one k ?_; filter_upwards [K.leaps.eventually h,hx] with i hi hx
    have hx':=(hi _ _ hx).2; rw [zero, pow_zero,one_div] at hx'; rw [one_mul,inv_pow]; exact hx'

lemma base_size (simple:G.Simple) : Paint K A (fun i=> moment (spectator F (s i)) (x i) v) := by
    have he (i:L): ClearOf (o i) (bare:Fin 0→E4) 1:=⟨fun j=>Fin.elim0 j,fun j=>Fin.elim0 j⟩
    obtain ⟨k,h⟩:= bank.horizons I (Fin 0) (names v) bare δ M 1 hd hm zero_lt_one 0
    let U b i:= R.port.ope b (x i) (names v) (o i)*VAC.value F P b
    let Z i:= ∑ b∈bands F.sector.derivatives 0, U b i
    let D i:= moment (spectator F (s i)) (x i) v
    have hr : Paint K (fun i=> r i / r i^sigma (names v)) (fun i=> D i - Z i) := by
       refine Paint.from_cost 1 zero_lt_one k ?_; filter_upwards [K.leaps.eventually h,hx] with i hi hx
       obtain ⟨hp,hh,H⟩:= hi _ (bare:Fin 0→E4) (o i) hx (he i);
       have hw:=H.phaseBound (s i); rw [Seats.observe_bare _ (x i) (names v) (s i) (beside_distinct.mp hp|>.1)] at hw;
       unfold D; rw [observed,one_mul]; rw [pow_one] at hw
       rw [show Z i = R.port.truncated (spectator F (s i)) 0 (x i) (names v) (o i) (bare:Fin 0→E4) bare from ?_]; exact hw
       symm; refine Finset.sum_congr rfl (fun j hj=>congrArg (_*·) ?_); exact (VAC.common F simple (s i) j (sole (o i)) () (Nat.eq_zero_of_le_zero (full_bands ..|>.mp hj)))
    have hz : Paint K A Z := Paint.sum _ (fun b hb=> by
           have hv:= (grain F R K hm hd hx bank v b (Nat.eq_zero_of_le_zero ((full_bands ..).mp hb))).times (Paint.const (VAC.value F P b)); unfold U; simpa only [mul_one] using hv)
    refine Paint.assists (Paint.plus (Paint.eases hr ?_) hz) (Eventually.of_forall fun _=> sub_add_cancel ..)
    filter_upwards [K.positive,K.bounded] with i hp hi; rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity),inv_pow, ←one_div]; exact div_le_div_of_nonneg_right hi (by positivity : 0 ≤ r i ^ sigma (names v))
end YM.OPE.Logged.RootRoom
