import YM.Integration.WilsonReceivedChronologicalFixedRoseDatedSalary
import YM.Integration.WilsonReceivedChronologicalFixedRoseTerminalSalary
import YM.Integration.WilsonReceivedChronologicalFixedRoseBothFees

/-! The full original six-entry bill on the fitted physical panel, including the separate
captured ear, both endpoint fees, and the terminal income of that very file. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseWholeSalary
open Function Filter Finset Lattice Wilson RG Pert.Asymptotics PhysicalNext.Repeat.Legato
open WilsonReceivedCanonicalVersePortfolio (wallet)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOlderFreshSoftSocketMeasuredCash (packet)
open WilsonReceivedChronologicalLastFlat (wage)
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonAddressedHomeDose (ceiling)
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G)(simple:G.Simple){n:ℕ}
local notation "H" => R.family.path.levels.clock.hatBeta

private theorem six {z g a b c d e f:ℝ}{t:ℕ}(gp:0≤g)(limit:6*g≤1)
    (ha:z*a≤g^(t+1))(hb:z*b≤g^(t+1))(hc:z*c≤g^(t+1))(hd:z*d≤g^(t+1))
    (he:z*e≤g^(t+1))(hf:z*f≤g^(t+1)):z*((a+b+c+d+e)+f)≤g^t:=by
  calc _ ≤ 6*g^(t+1):=by linarith only [ha,hb,hc,hd,he,hf]
       _ = (6*g)*g^t:=by rw [pow_succ];ring
       _ ≤ 1*g^t:=mul_le_mul_of_nonneg_right limit (pow_nonneg gp _)
       _ = _:=one_mul _

include simple in
theorem original (d power:Fin n→ℕ)(s:(Stock.census (Fin n)).Mode)(M:Fin n→ℝ)(one:∀i,1≤M i)
    (A pole P p middle order topOrder E capE count bank mesh goal t:ℕ)(B C α η θ capC packetC:ℝ)
    (bp:0≤B)(pp:0≤packetC)(head:t+1+1≤order)
    (edge:t+1+1+2*pole*n≤P)(switch:t+1+1+2*pole*n≤p)(month:t+1+1+2*pole*n≤ middle)
    (tail:t+1+1+bank+(mesh*(∑i∈s.val,d i)+1)≤goal):
    ∀ᶠ v:ℕ in atTop,∀{c f K N per:ℕ},0<v → v≤c → c≤f → ∀(fk:f≤K)(kn:K≤N),
    R.family.S.scale K-R.family.S.scale (v-1)≤(A:ℝ)*(1+Real.log (H v)) →
    ∀{request cards:ℕ}(panel:Panel R d N per f K fk kn request pole cards B)(file:Filed R d K),
    panel.M=M → ∀r:ℝ,0≤r → r≤1 →
    let g:=regulatorRun R.family N per v
    let h:=∑i∈s.val,d i
    let w:=votes R d (N:=N) (per:=per) file panel.names panel.turn
    let capital:=∑q:Columns R (fun i:s.val=>d i.val),‖packet R d s.val w N per K q‖
    let due:=wallet R d (fun _=>B*(H K)^pole) s.val
    r^h*capital≤packetC*(g⁻¹)^bank*(g⁻¹)^(mesh*h+1) →
    r^h*((((∏i∈s.val,ceiling (R:=R) (d i) (panel.M i))*((H f)^order)⁻¹)+
        due*((4*((2*A:ℕ):ℝ)/Real.log 3)*wage s P 1 η*g^middle)+
        due*(WilsonOriginalTwoFlatIRSocketRose.charge R d power P C α E s*(regulatorRun R.family N per c)^p)+
        due*(WilsonOriginalOneArmClearCash.wage s P θ*g^P)+due*(wage s P 1 θ*g^P))+
      (capital*WilsonOlderFreshSoftSocketCensus.fee R d s.val)*
        (g^goal*WilsonOriginalTwoFlatIRSocketPower.ceiling n topOrder (∑i,d i) capE count capC))≤g^t:=by
  filter_upwards [WilsonReceivedChronologicalFixedRoseCutoffSalary.original R simple d M one,
    WilsonReceivedChronologicalFixedRoseDatedSalary.original R simple d power s A pole P p middle (t+1) E
      B C α η θ bp edge switch month,
    WilsonReceivedChronologicalFixedRoseTerminalSalary.original R simple d s.val topOrder capE count bank mesh
      (∑i∈s.val,d i) goal (t+1) capC packetC pp tail,
    WilsonOriginalOpticalCouplingBand.cold R simple 6]
    with v cutoff dated terminal desk c f K N per vp vc cf fk kn span request cards panel file fixed r rp small
  intro g h w capital due received
  have vn:=vc.trans (cf.trans (fk.trans kn))
  have gp:0<g:=ActualRunKernelPackets.regulator_pos R N per v vn
  have limit:6*g≤1:=(mul_le_mul_of_nonneg_right (desk N per vn) gp.le).trans_eq (inv_mul_cancel₀ gp.ne')
  have scale {x:ℝ}(cash:x≤g^(t+1)):r^h*x≤g^(t+1):=by
    exact (mul_le_mul_of_nonneg_left cash (pow_nonneg rp _)).trans
      (mul_le_of_le_one_left (pow_nonneg gp.le _) (pow_le_one₀ rp small))
  obtain ⟨old,young,allDates,atC⟩:=dated (N:=N) (per:=per) vp vc (cf.trans (fk.trans kn)) kn span
  exact six gp.le limit (cutoff (vc.trans cf) fk kn panel fixed s.val rp small head)
    (scale allDates) (scale atC) (scale old) (scale young) (terminal (K:=K) vn w r rp received)

end YM.Integration.WilsonReceivedChronologicalFixedRoseWholeSalary
