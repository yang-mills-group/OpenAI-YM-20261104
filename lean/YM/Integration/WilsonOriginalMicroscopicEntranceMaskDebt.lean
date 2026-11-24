import YM.Integration.WilsonOriginalMicroscopicEntranceResidualHearing

/-! On each original law account separately for its full measured
face and the three signed singleton remainders on the actual masked peers. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceMaskDebt
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
open WilsonOriginalMicroscopicEntranceGridStock (debt peer Filed account old_paid entered_paid panel)
open WilsonOriginalMicroscopicEntranceResidualStock (remainder)
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


variable (B:Fin 3→ℝ)(Z:∀a:Fin 3,store R.family (d a) p f)

def reserve (full:ℂ)(x assigned E:Fin 3→ℂ)(s:(J).Mode):ℂ:=
  (full-∏a∈s.val,assigned a)-∑a:Fin 3,(x a-assigned a)*E a

private theorem exchange (A B:ℂ)(a b l r:Fin 3→ℂ)(s:(J).Mode):
    let E:=fun i=>share l r i s
    reserve A a l E s-reserve B b r E s=(A-B)-∑i:Fin 3,(a i-b i)*E i:=by
  intro E
  have cut:=WilsonThermometerSolitaryExchange.ordinary l r s
  rw [WilsonOriginalMicroscopicEntranceExchange.word_value,WilsonOriginalMicroscopicEntranceExchange.word_value] at cut
  change (∏i∈s.val,l i)-(∏i∈s.val,r i)=∑i:Fin 3,(l i-r i)*E i at cut
  simp only [reserve,sub_mul,Finset.sum_sub_distrib] at cut ⊢
  linear_combination -cut

def debit {k:ℕ}(source:Fin 3→X k→ℂ)(post:f≤k)(assigned:X f→Fin 3→ℂ)
    (E:Fin 3→X f→ℂ)(s:(J).Mode)(U:X f):ℂ:=
  reserve (actualTransport R.family (N:=N) (face source s) post U)
    (fun a=>mean R.family N (source a) f U) (assigned U) (fun a=>E a U) s

theorem original (mature:∀a,R.family.ref (d a)≤f)(filed:Filed R d (N:=N) (n:=n) Y o v B Z)
    (first second:X f→Fin 3→ℂ)(s:(J).Mode)(U:X f):
    let E:=fun a W=>share (first W) (second W) a s
    remainder R d live Y o v Z s E U=debit R (N:=N) raw₀ ((k₀).trans live) first E s U-
        debit R (N:=N) seat k₀ second E s U:=by
  intro E
  let x:=fun a=>mean R.family N (raw₀ a) f U
  let y:=fun a=>mean R.family N (seat a) f U
  have own(a:Fin 3):x a-y a=signed R d (N:=N) a (o a) (Z a) U:=by
    simp only [x,y,mean,dif_pos ((k₀).trans live),dif_pos k₀]
    exact WilsonOriginalMicroscopicEntranceGridRow.original R d live Y o v a (mature a) (B a) (Z a) (filed a) U
  let top:=actualTransport R.family (N:=N) (face raw₀ s) ((k₀).trans live) U
  let restored:=actualTransport R.family (N:=N) (face seat s) k₀ U
  have joint:top-restored=account R d live Y o v Z s U:=by
    have eligible:=WilsonOriginalMicroscopicEntranceExchange.original R.family R.makes live k₀ raw₀ seat
      (old_paid R d live Y o) (entered_paid R d (N:=N) (n:=n) o v) s U
    apply eligible.trans
    apply congrArg (fun g=>debt R d live Y o v s U+g)
    apply sum_congr rfl
    intro a _
    exact congrArg (fun g=>g*peer R d live Y o v s a U) (own a)
  change _=reserve top x (first U) (fun a=>E a U) s-reserve restored y (second U) (fun a=>E a U) s
  rw [exchange top restored x y (first U) (second U) s]
  simp only [own]
  rw [joint,WilsonOriginalMicroscopicEntranceResidualStock.total R d live Y o v Z s E U]
  abel

end YM.Integration.WilsonOriginalMicroscopicEntranceMaskDebt
end
