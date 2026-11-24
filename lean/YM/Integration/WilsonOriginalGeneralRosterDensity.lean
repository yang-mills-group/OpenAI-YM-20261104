import YM.Integration.WilsonMeasuredPublicEntranceCutoffHearing
import YM.Integration.WilsonOriginalMicroscopicEntranceSockets
import YM.Integration.WilsonReflectedPublicOrientedFaces

/-! Removing all marker normalizations from a physical panel recovers its full original
numerator at each held configuration, simultaneously on every deletion face. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterDensity
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open PhysicalNext.Repeat.Legato Marker MergeProof RG05Readout RG05Readout.Address
open RG05Readout.Records Extra.Trajectories WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMeasuredPublicEntranceCellWords (physical)
open scoped Classical BigOperators Topology

variable {G:Gauge}{R:Run G}{n N per f K requested power t:ℕ}{d:Fin n→ℕ}
    {fk:f≤K}{cut:K≤N}{B:ℝ}(A:Panel R d N per f K fk cut requested power t B)
local notation "C" => R.family
local notation "modes" => Stock.census (Fin n)
local notation "offered" v:max => offer R (A.names v) (A.home v) (fk.trans cut)

def Restored:Prop:=
  ∀j (hj:j≤N)(s:(modes).Mode)(W:Config G ((C).side j per)),
    (∏i∈s.val,(charge (offered i):ℂ))*
      (WilsonThermometerReflectedRoster.density R d (fun _=>0) A.turn A.loc
        (fun i=>reduce (offered i)) A.stamps (modes) (fk.trans cut) hj W).part s=
    ((C).path.rep N per j).eval W • actualTransport (C) (N:=N)
      (physical R d A.names A.turn A.loc s) hj W

theorem original (refs:∀i e,e≤d i→(C).ref e≤N):Restored A:=by
  intro j hj s W
  let x:=physical R d (N:=N) A.names A.turn A.loc s
  let c:ℂ:=∏i∈s.val,(charge (offered i):ℂ)
  have nz:c≠0:=prod_ne_zero_iff.mpr fun i _=>Complex.ofReal_ne_zero.mpr (charged (offered i)).ne'
  have hcont:Continuous x:=continuous_finsetProd _ fun i _=>(C).continuousO _ _ _ _ _
  obtain ⟨price,cap⟩:=(isCompact_range hcont.norm).bddAbove
  have bounded:WilsonOriginalMicroscopicEntranceDeposits.funded x:=
    ⟨hcont.measurable,price,fun U=>cap ⟨U,rfl⟩⟩
  have collect:(fun U=>∏i∈s.val,(charge (offered i):ℂ)⁻¹*
      (C).O N per (WilsonReflectedPublicOrientedFaces.displayed R (d i) (A.names i) (A.turn i))
        (WilsonThermometerReflectedTrajectory.anchorAt R (A.loc i) N) U)=fun U=>c⁻¹*x U:=by
    funext U
    simp only [x,c,physical,prod_mul_distrib,prod_inv_distrib]
  rw [WilsonReflectedPublicOrientedFaces.original R d A.names A.sensors A.stamps A.home
    (fk.trans cut) A.enrolled refs A.turn A.loc (modes) t A.filed j hj s W, collect,
    WilsonOriginalMicroscopicEntranceSockets.scaled R le_rfl hj x bounded c⁻¹ W]
  change c * (_ • (c⁻¹ * _))=_
  simp only [Complex.real_smul]
  field_simp [nz]
  rfl

end YM.Integration.WilsonOriginalGeneralRosterDensity
end
