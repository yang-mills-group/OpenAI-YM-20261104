import YM.Integration.WilsonOriginalMicroscopicEntranceGridRow
import YM.Integration.WilsonOriginalMicroscopicEntranceEarlier

/-! The complete signed ordinary entrance on the actual embedded reporters.
The previously issued signed rows keep both of their actual companion functions. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceGridStock
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records WilsonOriginalNullCorridor MergeProof MergeProof.Accent Marker
open WilsonPositionProgramOriginalBlockedTrial WilsonAddressedRestartedColumn
open WilsonOriginalMicroscopicGuardedTrial (guarded)
open WilsonOriginalMicroscopicEntranceDeposits (mean reading funded)
open WilsonOriginalMicroscopicEntranceEarlier (face salary)
open WilsonOriginalMicroscopicEntranceFiling (units supplied)
open WilsonOriginalMicroscopicEntranceGridRow (pin factor entered old signed)
open WilsonThermometerSolitaryExchange (share)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ){N p f n:ℕ}
local notation "J" => Stock.census (Fin 3)
local notation "X" i:max => Config G (R.family.side i p)
local notation "K" => f+n
local notation "k₀" => Nat.le_add_right f n
variable (live:f+n≤N)(Y:∀a:Fin 3,R.family.label (d a))(o:Fin 3→Site (R.family.side f p))
   (v:∀a:Fin 3,R.family.label (d a))
local notation "raw₀" => old R d ((k₀).trans live) Y o
local notation "seat" => entered R d (N:=N) (n:=n) o v
local notation "mask" => guarded R d N p K (pin R k₀ o) v

theorem old_paid (a:Fin 3):funded (raw₀ a):=by
  have cont:=R.family.continuousO N p (d a) (Y a) (pin R ((k₀).trans live) o a)
  obtain ⟨M,bound⟩:=(isCompact_range cont.norm).bddAbove
  exact ⟨cont.measurable,M,fun U=>bound ⟨U,rfl⟩⟩

theorem entered_paid (a:Fin 3):funded (seat a):=by
  obtain ⟨m,M,bound⟩:=(supplied R d (N:=N) (pin R k₀ o) v a).1
  refine ⟨measurable_const.mul m,‖factor R d K a‖*M,fun U=>?_⟩
  rw [entered,norm_mul]
  exact mul_le_mul_of_nonneg_left (bound U) (norm_nonneg _)

theorem panel (s:(J).Mode):face seat s=fun U=>units R d K s*face mask s U:=by
  funext U
  exact prod_mul_distrib

def debt (s:(J).Mode)(U:X f):ℂ:=
  (∑i∈Ico f N,reading R.family N raw₀ s.val f i U)-
    (∑i∈Ico f K,reading R.family N seat s.val f i U)

def peer (s:(J).Mode)(a:Fin 3)(U:X f):ℂ:=
  share (fun i=>mean R.family N (raw₀ i) f U) (fun i=>mean R.family N (seat i) f U) a s

variable (B:Fin 3→ℝ)(z:∀a:Fin 3,store R.family (d a) p f)
def Filed :Prop:=∀a:Fin 3,WilsonAddressedRestartedFiled.Filed R (d a) N p f (o a)
    (track R (d a) N p K (numerator R (d a) N p K 0 (v a)) f-
        calValues (C:=R.family) (d a) N p f ((R.family.factory (d a) N p).terminal.symm (Y a))) (B a) (z a)

def account (s:(J).Mode)(U:X f):ℂ:=debt R d live Y o v s U+
    ∑a:Fin 3,signed R d (N:=N) a (o a) (z a) U*peer R d live Y o v s a U

theorem original (mature:∀a,R.family.ref (d a)≤f)(filed:Filed R d (N:=N) (n:=n) Y o v B z)
    (s:(J).Mode){u:ℕ}(earlier:u≤f)(W:X u):
    WilsonOriginalMicroscopicEntranceSockets.read R d Y (pin R ((k₀).trans live) o) live (earlier.trans k₀) mask s W=
      actualTransport R.family (N:=N) (account R d live Y o v z s) earlier W:=by
  let pay:=fun a=>(supplied R d (N:=N) (pin R k₀ o) v a).1
  have receipt:=WilsonOriginalMicroscopicEntranceFiling.original R d Y (pin R ((k₀).trans live) o) live
    mask pay (earlier.trans k₀) s W
  rw [←panel R d (N:=N) (n:=n) o v s] at receipt
  apply receipt.trans
  apply WilsonOriginalMicroscopicEntranceEarlier.carry R.family R.makes live k₀ earlier (face raw₀ s) (face seat s)
    (salary raw₀ (old_paid R d live Y o) s) (salary seat (entered_paid R d (N:=N) (n:=n) o v) s)
  intro U
  have exchange:=WilsonOriginalMicroscopicEntranceExchange.original R.family R.makes live k₀ raw₀ seat
    (old_paid R d live Y o) (entered_paid R d (N:=N) (n:=n) o v) s U
  apply exchange.trans
  apply congrArg (fun g=>debt R d live Y o v s U+g)
  apply sum_congr rfl
  intro a _
  apply congrArg (fun g=>g*peer R d live Y o v s a U)
  change mean R.family N (raw₀ a) f U - mean R.family N (seat a) f U = _
  simp only [mean,dif_pos ((k₀).trans live),dif_pos k₀]
  exact WilsonOriginalMicroscopicEntranceGridRow.original R d live Y o v a (mature a) (B a) (z a) (filed a) U

end YM.Integration.WilsonOriginalMicroscopicEntranceGridStock
end
