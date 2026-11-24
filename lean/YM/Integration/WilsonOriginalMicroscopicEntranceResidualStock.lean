import YM.Integration.WilsonOriginalMicroscopicEntranceGridStock

/-! Separate on the elected f-grid the signed fibers tested on purchased peers from
the complete original mixed and unequal-peer contribution. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceResidualStock
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
def remainder (s:(J).Mode)(E:Fin 3→X f→ℂ)(U:X f):ℂ:=
  debt R d live Y o v s U+∑a:Fin 3,signed R d (N:=N) a (o a) (Z a) U*(peer R d live Y o v s a U-E a U)

theorem total (s:(J).Mode)(E:Fin 3→X f→ℂ)(U:X f):
    account R d live Y o v Z s U=remainder R d live Y o v Z s E U+
       ∑a:Fin 3,signed R d (N:=N) a (o a) (Z a) U*E a U:=by
  simp only [account,remainder,mul_sub,Finset.sum_sub_distrib]
  abel

theorem original (mature:∀a,R.family.ref (d a)≤f)(filed:Filed R d (N:=N) (n:=n) Y o v B Z)(s:(J).Mode):
    Integrable (fun U=>(R.family.path.rep N p f).eval U • account R d live Y o v Z s U) (prior G _):=by
  let source:=face raw₀ s
  let entered:=face seat s
  have first:=salary raw₀ (old_paid R d live Y o) s
  have second:=salary seat (entered_paid R d (N:=N) (n:=n) o v) s
  obtain ⟨M,mcap⟩:=first.2
  obtain ⟨L,lcap⟩:=second.2
  have unm:=actualTransport_weighted_integrable R.family R.makes (le_refl N) first.1.aestronglyMeasurable mcap ((k₀).trans live)
  have fit:=actualTransport_weighted_integrable R.family R.makes live second.1.aestronglyMeasurable lcap k₀
  apply (unm.sub fit).congr (ae_of_all _ fun U=>?_)
  change (R.family.path.rep N p f).eval U • actualTransport R.family (N:=N) source ((k₀).trans live) U-
    (R.family.path.rep N p f).eval U • actualTransport R.family (N:=N) entered k₀ U=_
  rw [←smul_sub]
  apply congrArg (fun w:ℂ=>(R.family.path.rep N p f).eval U • w)
  have read:=WilsonOriginalMicroscopicEntranceFiling.original R d Y (pin R ((k₀).trans live) o) live mask
    (fun a=>(supplied R d (N:=N) (pin R k₀ o) v a).1) k₀ s U
  rw [←panel R d (N:=N) (n:=n) o v s] at read
  have hear:=WilsonOriginalMicroscopicEntranceGridStock.original R d live Y o v B Z mature filed s (le_rfl:f≤f) U
  rw [actualTransport_base R.family R.makes ((k₀).trans live)] at hear
  exact read.symm.trans hear

end YM.Integration.WilsonOriginalMicroscopicEntranceResidualStock
end
