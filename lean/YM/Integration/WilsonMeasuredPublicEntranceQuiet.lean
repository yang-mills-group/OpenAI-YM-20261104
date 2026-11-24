import YM.Integration.WilsonMeasuredPublicEntranceSignedAtK
/-! The empty occupied face of the original source and the printed section has zero
signed difference at every held field. No marked root has to be selected. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceQuiet
open Function Finset Lattice Wilson RG Marker Labels Source QuadraticLocal
open MeasureTheory PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonMeasuredPublicEntranceOrder WilsonMeasuredPublicEntranceSignedEar
open WilsonAddressedFiniteGuardTrial (printed submitted)
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){V:Type}[Fintype V][DecidableEq V](d:V → ℕ)
  {N per K u:ℕ}(kn:K ≤ N)(uk:u ≤ K)(sites:V → Site (R.family.side K per))
  (v:∀a,R.family.label (d a))(z:V → ℂ)
local notation "C" => R.family
local notation "fired" => WilsonOriginalAlternativeFiniteSource.fired (V:=V)

theorem original (label:∀a,(C).label (d a))(o:V → Site ((C).side N per))(dose:V → ℂ)
    (s:(Stock.census V).Mode)(empty:s.val=∅)(W:Config G ((C).side u per)):
    let raw:=fun U=>∏a∈s.val,dose a*(C).O N per (label a) (o a) U
    let trial:=printed R d (N:=N) sites v z fired s
    actualTransport (C) (N:=N) (fun U=>actualTransport (C) (N:=N) raw kn U-trial U) uk W=0:=by
  intro raw trial
  have filed:=WilsonMeasuredPublicEntranceSignedAtK.original R d kn uk sites v z label o dose s W
  change actualTransport (C) (N:=N) (fun U=>actualTransport (C) (N:=N) raw kn U-trial U) uk W=
    actualTransport (C) (N:=N) raw (uk.trans kn) W-actualTransport (C) (N:=N) trial uk W at filed
  have absent:trial=(fun _=>1):=by
    funext U
    simp only [trial,WilsonAddressedFiniteGuardTrial.printed,empty,Finset.prod_empty]
  rw [filed,absent]
  simp only [raw,empty,Finset.prod_empty]
  rw [actualTransport_const (C) R.makes (le_refl N) (1:ℂ) (uk.trans kn) W,
    actualTransport_const (C) R.makes kn (1:ℂ) uk W,sub_self]

end YM.Integration.WilsonMeasuredPublicEntranceQuiet
end
