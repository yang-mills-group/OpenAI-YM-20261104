import YM.Integration.WilsonGeometricSignedPrimary
import YM.Integration.WilsonOriginalScalarGallery

/-! Capture the complete actually received gallery on its own vacuum. The original
    regular and hard entries can be invoiced directly at the submitted marker radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerUnpaintedCapture
open Filter Finset Lattice RG Wilson Marker Multi QuadraticLocal Ac Source Labels Extra.Histories
open Push.Local Planned.GuardedAtom WilsonCenteredFiledAtoms WilsonRootedKioskOccupiedSlip
open WilsonGeometricSignedCapture
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {P:Rep G n} {F:Frame G 0} {o:Fin 3→Site n}
local notation "J" => Stock.census (Fin 3)
variable {X I:Type} [Countable I]

theorem original (A:Gallery X I o P (J))(x:X)(w:Fin 3→ℝ)(hp:∀j,0<w j)
    (c:(J).Mode→ℂ) (keeper:Guard.Keeper P.p P.activities){σ C Λ δ v κ μ α z e:ℝ}
    (law:P.Lawful σ C Λ δ v)(div:0<κ)(hv:0 ≤ v)(room:hitWidth P.p*v ≤ 1)
    (reserve:hitWidth P.p*v/κ ≤ 1)(S:SectionData F)(Y:Hol G)(reader:Readable Y S P.p n μ)
    (y:Site n)(Z:Support n)(atCenter:y∈Z)(resident:∀v,o v∈Z)(housed:Z⊆halo P.p.B {y})
    (rad:ℕ)(near:∀v,separation (o v) y ≤ rad)(radius:rad ≤ P.p.B)
    (strength:P.p.supportExponent ≤ α)(hz:1 ≤ z)(motion:WilsonReportRetainedAnchor.reprice P.p P.p.B ≤ 2*z^2)
    (mp:0 ≤ μ)(rd:μ ≤ 4*z^2)(ep:0 ≤ e)(size:e ≤ 1)(hardFee:e ≤ κ)
    (soft:A.E.Paid w P.p.B (P.p.supportExponent+2) 1)
    (hard:A.K.Paid w P.p.B P.p.supportExponent e):
    let rem:=weightBill c w*(|WilsonFullFaceSignedPower.constants S Y α 4| *z^87*3)
    let unit:=weightBill c w*(WilsonFullFaceSignedPower.inter*((Fintype.card (parts (J)).Mode:ℝ)*27))
    ∃ h:Coefficient F n,h.Format y Y P ∧ h.remBound y P κ rem ∧
      (∀U,h.density y S P U=take c (A.density x U)-(P.eval U:ℂ)*take c (Poly.pass (0:Poly (J)))) ∧
      F.coeffSize h.x ≤ testPrice F*unit:=by
  intro rem unit
  let E:=WilsonOriginalScalarGallery.empty P o (J) X
  have paid:E.Paid w P.p.B (P.p.supportExponent+2) 0:=by
    refine ⟨fun i=>i.elim,fun i=>i.elim,fun i=>i.elim,fun t=>?_⟩
    exact ⟨fun i=>i.elim,(hasSum_fintype _).summable,by rw [tsum_empty]⟩
  have allFields:Gross E w P.p.B (P.p.supportExponent+2) 0:=by
    refine ⟨fun i=>i.elim,fun i=>i.elim,fun i=>i.elim,fun t=>?_⟩
    exact ⟨fun i=>i.elim,(hasSum_fintype _).summable,by rw [tsum_empty]⟩
  have joined:(E.join A.E).Paid w P.p.B (P.p.supportExponent+2) 1:=by
    simpa only [zero_add] using Lamps.joinPaid paid soft
  let AG:Gallery X (Empty⊕I) o P (J):=⟨E.join A.E,A.K⟩
  have bare0 (U:Config G n):bare E x U=0:=by simp only [WilsonRootedKioskOccupiedSlip.bare,tsum_empty]
  have actual (U:Config G n):AG.density x U=A.density x U:=by
    have h0:0 ≤ P.p.supportExponent+2:=by linarith only [P.p.exponent_pos]
    have logs:(E.join A.E).log x U=A.E.log x U:=by
      rw [Lamps.joinLog x U (paid.sums h0 hp x U) (soft.sums h0 hp x U)]
      simp only [Lamps.log,tsum_empty,zero_add]
    change _ • (Poly.pass ((E.join A.E).log x U)*A.gas x U)=_ • (Poly.pass (A.E.log x U)*A.gas x U)
    rw [logs]
  let fee (s:(J).Mode):=WilsonFullFaceSignedCapture.fare P.p S Y Z w w s rad 0 1 0 e 1 v κ μ
  have faces (s:(J).Mode):Store P S Y y κ (fee s)
      (fun U=>(A.density x U).part s-(P.eval U:ℂ)*(Poly.pass (0:Poly (J))).part s):=by
    have sold:=WilsonFullFaceSignedCapture.face E A.E A.K x s w w hp hp zero_lt_one paid soft allFields joined hard keeper
      law div hv room S Y reader y Z atCenter (fun j _=>resident j) rad (fun j _=>near j)
    change Store P S Y y κ (fee s) (fun U=>(AG.density x U).part s-(P.eval U:ℂ)*(Poly.pass (bare E x U)).part s) at sold
    simpa only [actual,bare0] using sold
  let M:=WilsonFullFaceSignedPower.constants S Y α 4
  have w0:0 ≤ weightBill c w:=sum_nonneg fun s _=>div_nonneg (norm_nonneg _) (Poly.worth hp s).le
  have z0:0 ≤ z:=zero_le_one.trans hz
  have K:3 ≤ (4:ℝ)*z^17:=by nlinarith only [one_le_pow₀ hz (n:=17)]
  have eK:e/κ ≤ 1:=(div_le_one div).2 hardFee
  have rate (s:(J).Mode):Poly.toll w s*fee s ≤ |M| *z^87*3:=by
    have incoming:=WilsonFullFaceSignedPower.face P.p S Y w hp s y Z housed rad radius (K:=4) (x:=z) (shrink:=1)
      strength (by norm_num) hz le_rfl le_rfl zero_le_one le_rfl zero_le_one (by simpa only [zero_add] using K)
      ((by norm_num : (0:ℝ) ≤ 3).trans K) ((by norm_num : (1:ℝ) ≤ 3).trans K) le_rfl
      (by nlinarith only [one_le_pow₀ hz (n:=12)]) ep size div hv room reserve motion mp rd
    simp only [div_one] at incoming
    have h1:M*z^87 * (1+e/κ+hitWidth P.p*v/κ)  ≤  |M| *z^87*(1+e/κ+hitWidth P.p*v/κ):=by
      have pos:0 ≤ 1+e/κ+hitWidth P.p*v/κ:=by
        have gw:0 ≤ hitWidth P.p:=by unfold hitWidth;positivity
        positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self M) (pow_nonneg z0 _)) pos
    exact incoming.trans (h1.trans (mul_le_mul_of_nonneg_left (by linarith only [reserve,eK]) (mul_nonneg (abs_nonneg _) (pow_nonneg z0 _))))
  have total:(∑s,‖c s‖*fee s) ≤ rem:=by
    calc _  ≤  ∑s, ‖c s‖/Poly.toll w s*(|M| *z^87*3):=by
           apply sum_le_sum
           intro s _
           have r:fee s ≤ (|M| *z^87*3)/Poly.toll w s:=(le_div_iff₀ (Poly.worth hp s)).2 ((mul_comm ..).le.trans (rate s))
           exact (mul_le_mul_of_nonneg_left r (norm_nonneg _)).trans_eq (by ring)
         _ = _ := (sum_mul ..).symm
  obtain ⟨h,fmt,charge,out,scalar⟩:=WilsonGeometricSignedCapture.pooled S Y y div law reader c
    (A.density x) (fun _=>Poly.pass (0:Poly (J))) fee faces
  have bound:=WilsonGeometricSignedCapture.scalar E A.E A.K w hp zero_lt_one le_rfl le_rfl paid soft x c
  change ‖(P.eval 1:ℂ)⁻¹*(take c (AG.density x 1)-(P.eval 1:ℂ)*take c (Poly.pass (bare E x 1)))‖ ≤ _ at bound
  have unitPrice:=WilsonGeometricSignedPrimary.unit h _ scalar (by simpa only [actual,bare0,zero_add,one_mul] using bound)
  obtain ⟨a,b,h0,h1,tariff,extra⟩:=charge
  refine ⟨h,fmt,⟨a,b,h0,h1,tariff.trans total,extra⟩,out,?_⟩
  convert unitPrice using 2
  norm_num [unit]

end YM.Integration.WilsonThermometerUnpaintedCapture
end
