import YM.Integration.WilsonOriginalMicroscopicEntranceResidualHearing
import YM.Integration.WilsonThermometerSolitaryReadWallet

/-! Fixed masks and both original peer books remain inside the signed hearing.
All charges are taken after integrating against a single true earlier field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceFlatBalance
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
open WilsonOriginalMicroscopicEntranceSockets (read)
open WilsonOriginalMicroscopicGuardedTrial (gap raw)
open Analysis Table Extraction GapsContact GapsContact.Seams GapsContact.Stamps GapsContact.Ascent
open WilsonCoeffUV.Embroider
open WilsonOriginalMicroscopicEntranceResidualHearing (originField)
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


theorem original {h:Fin 3→ℕ}(κ:(a:Fin 3)→Knob (h a))(pt:Fin 3→Chamber)(mature:∀a,R.family.ref (d a)≤f)
    (filed:Filed R d (N:=N) (n:=n) Y o v B Z)(s:(J).Mode)(first second:X f→Fin 3→ℂ)(fees:Fin 3→ℝ)
    {u:ℕ}(uf:u≤f)(W:X u):
    let E:=fun a U=>share (first U) (second U) a s
    let target:=fun a U=>signed R d (N:=N) a (o a) (Z a) U*E a U
    (∀a∈s.val, Integrable (fun U=>originField R d (N:=N) (n:=n) Y v a (Lattice.translate (o a) U)*E a U) (prior G _) ∧
       ‖actualTransport R.family (N:=N) (target a) uf W‖≤fees a) →
    let upper:=pin R ((k₀).trans live) o
    let sites:=pin R k₀ o
    let left:=actualTransport R.family (N:=N) (remainder R d live Y o v Z s E) uf W
    let halo:=units R d K s*actualTransport R.family (N:=N) (gap R d N p K sites v s.val) (uf.trans k₀) W
    ‖read R d Y upper live (uf.trans k₀) mask s W-left‖≤∑a∈s.val,fees a ∧
    ‖read R d Y upper live (uf.trans k₀) (raw R d N p K sites v) s W-(left-halo)‖≤∑a∈s.val,fees a:=by
  intro E target charged upper sites left halo
  let priced:=fun a=>actualTransport R.family (N:=N) (target a) uf W
  have none {a:Fin 3}(away:a∉s.val)(U:X f):E a U=0:=
    WilsonThermometerSolitaryReadWallet.absent (first U) (second U) a s away
  have blanks {a:Fin 3}(away:a∉s.val):priced a=0:=by
    have vanish:target a=fun _=>0:=funext fun U=>by change _*_=0;rw [none away,mul_zero]
    exact (congrFun (congrArg (fun w:X f→ℂ=>actualTransport R.family (N:=N) w uf) vanish) W).trans
      (actualTransport_const R.family R.makes ((k₀).trans live) (0:ℂ) uf W)
  have earned:∀a,Integrable (fun U=>originField R d (N:=N) (n:=n) Y v a (Lattice.translate (o a) U)*E a U) (prior G _):=by
    intro a
    by_cases used:a∈s.val
    · exact (charged a used).1
    · simp only [none used,mul_zero]
      exact integrable_zero ..
  obtain ⟨guardedRead,uncutRead⟩:=WilsonOriginalMicroscopicEntranceResidualHearing.original R d live Y o v B Z κ pt mature filed s E earned uf W
  change read R d Y upper live (uf.trans k₀) mask s W=left+∑a:Fin 3,priced a at guardedRead
  change read R d Y upper live (uf.trans k₀) (raw R d N p K sites v) s W=left+(∑a:Fin 3,priced a)-halo at uncutRead
  have small:‖∑a:Fin 3,priced a‖≤∑a∈s.val,fees a:=by
    rw [←Finset.sum_subset (Finset.subset_univ s.val) (fun i _ no=>blanks no)]
    exact (norm_sum_le ..).trans (Finset.sum_le_sum fun a used=>(charged a used).2)
  constructor
  · rw [guardedRead,add_sub_cancel_left];exact small
  · rw [uncutRead,show left+(∑a:Fin 3,priced a)-halo-(left-halo)=∑a:Fin 3,priced a by abel]
    exact small

end YM.Integration.WilsonOriginalMicroscopicEntranceFlatBalance
end
