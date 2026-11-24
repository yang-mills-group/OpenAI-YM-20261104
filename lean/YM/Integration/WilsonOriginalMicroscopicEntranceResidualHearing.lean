import YM.Integration.WilsonOriginalMicroscopicEntranceCropFields
import YM.Integration.WilsonOriginalMicroscopicEntranceResidualStock

/-! The remaining genuine mixed income and the fully heard masked field terms
share a single physical older conditional and its actual positive denominator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceResidualHearing
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

def originField (a:Fin 3):X f→ℂ:=
  track R (d a) N p K (numerator R (d a) N p K 0 (v a)) f-
      calValues (C:=R.family) (d a) N p f ((R.family.factory (d a) N p).terminal.symm (Y a))

theorem original {h:Fin 3→ℕ}(κ:(a:Fin 3)→Knob (h a))(pt:Fin 3→Chamber)(mature:∀a,R.family.ref (d a)≤f)
    (filed:Filed R d (N:=N) (n:=n) Y o v B Z)(s:(J).Mode)(E:Fin 3→X f→ℂ)
    (paid:∀a,Integrable (fun U=>originField R d (N:=N) (n:=n) Y v a (Lattice.translate (o a) U)*E a U) (prior G _))
    {u:ℕ}(uf:u≤f)(W:X u):
    let upper:=pin R ((k₀).trans live) o
    let sites:=pin R k₀ o
    let left:=actualTransport R.family (N:=N) (remainder R d live Y o v Z s E) uf W
    let charge:=∑a:Fin 3,actualTransport R.family (N:=N) (fun U=>signed R d (N:=N) a (o a) (Z a) U*E a U) uf W
    read R d Y upper live (uf.trans k₀) mask s W=left+charge ∧
    read R d Y upper live (uf.trans k₀) (raw R d N p K sites v) s W=left+charge-
      units R d K s*actualTransport R.family (N:=N) (gap R d N p K sites v s.val) (uf.trans k₀) W:=by
  intro upper sites left charge
  let crop:=fun a (U:X f)=>signed R d (N:=N) a (o a) (Z a) U*E a U
  have act:=WilsonOriginalMicroscopicEntranceResidualStock.original R d live Y o v B Z mature filed s
  have lenses:=WilsonOriginalMicroscopicEntranceCropFields.original R d ((k₀).trans live) o Z E B
    (originField R d (N:=N) (n:=n) Y v) filed paid uf W
  have forced:(fun U=>account R d live Y o v Z s U-∑a:Fin 3,crop a U)=remainder R d live Y o v Z s E:=by
    funext U
    rw [WilsonOriginalMicroscopicEntranceResidualStock.total R d live Y o v Z s E U]
    exact add_sub_cancel_right .. 
  have split:=congrFun (ActualWilsonAbsoluteTransport.sub R.family R.makes ((k₀).trans live) act lenses.1 uf) W
  change actualTransport R.family (N:=N) (fun U=>account R d live Y o v Z s U-∑a:Fin 3,crop a U) uf W =
    actualTransport R.family (N:=N) (account R d live Y o v Z s) uf W-actualTransport R.family (N:=N) (fun U=>∑a:Fin 3,crop a U) uf W at split
  rw [forced,lenses.2] at split
  have receive:=WilsonOriginalMicroscopicEntranceGridStock.original R d live Y o v B Z mature filed s uf W
  have heard:read R d Y upper live (uf.trans k₀) mask s W=left+charge:=
    receive.trans (eq_sub_iff_add_eq.mp split).symm
  have repair:=WilsonOriginalMicroscopicEntranceSockets.correction R d κ pt Y upper sites v live (uf.trans k₀) s W
  rw [heard] at repair
  exact ⟨heard,by linear_combination repair⟩

end YM.Integration.WilsonOriginalMicroscopicEntranceResidualHearing
end
