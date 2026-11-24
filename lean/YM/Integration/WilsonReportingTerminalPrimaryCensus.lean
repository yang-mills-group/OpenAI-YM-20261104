import YM.Integration.WilsonReportingTerminalPrimaryStencil
import YM.RG05Readout.Pulse.Openly

/-! The actual joint position observable on primary input at any reporting
origin. The original local angular basis, fine sites and signed common center
integral are retained. The fine engineering powers cancel exactly. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportingTerminalPrimaryCensus
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source RG05Readout
open Address Native Records Flatten Pulse PhysicalNext.Repeat.Legato WilsonReportingUnitOrbit
open scoped Classical Topology BigOperators
variable {G:Gauge} {C:Family G} {I:Type} [Fintype I] [DecidableEq I]
variable {b N per:ℕ}

def location (o:I→Site (C.side b per)) (h:b≤N) (r:ℝ)
    (u:I→Site (C.S.toDepth h per).count) (z:E4) : Cloud I :=
  (fun i=>r⁻¹ • (C.S.place (o i)-C.S.a b • z))+
    (r⁻¹*C.S.a b) • (fun i=>placeR (C.S.toDepth h per) (u i))

def fiber (s:I→ℕ) (x:(i:I)→C.label (s i)) (o:I→Site (C.side b per)) (h:b≤N)
    (r:ℝ) (Φ:Wave I) (z:E4) (U:Config G (C.side N per)) :ℂ:=
  ∑u:I→Site (C.S.toDepth h per).count,(perform s (fun i=>primary (s i)) Φ).val
    (location o h r u z) * ∏i,C.O N per (x i) ((C.S.toDepth h per).assemble (o i,u i)) U

omit [Fintype I] [DecidableEq I] in
private theorem zeroRanks (s:I→ℕ) (L:List I) : pegs s (fun i=>primary (s i)) L=0:=by
  induction L with
  | nil=>rfl
  | cons i L hyp=>
    change 0+pegs s (fun i=>primary (s i)) L=0
    rw [zero_add,hyp]

private theorem sampled (s:I→ℕ) (o:I→Site (C.side b per)) (h:b≤N)
    (u:I→Site (C.S.toDepth h per).count) (r:ℝ) (Φ:Wave I) (z:E4) :
    (perform s (fun i=>primary (s i)) (fork ((↑(C.S.toDepth h per).count.val:ℝ)⁻¹)
      (fun i=>placeR (C.S.toDepth h per) (u i)) (cropX Φ o r z))).val 0=
      (perform s (fun i=>primary (s i)) Φ).val (location o h r u z) := by
  unfold cropX;rw [fly_fork]
  unfold perform;rw [machine_roll,zeroRanks,pow_zero,one_smul]
  change (machine s (fun i=>primary (s i)) Finset.univ.toList Φ).val (location o h r u z+_ • (0:Cloud I))=_
  rw [smul_zero,add_zero]

theorem field (made:C.Makes) (s:I→ℕ) (x:(i:I)→C.label (s i)) (o:I→Site (C.side b per))
    (h:b≤N) (r:ℝ) (Φ:Wave I) (z:E4) (U:Config G (C.side N per)) :
    scalp (C:=C) s (fun i=>WilsonReportingTerminalPrimaryStencil.upper (N:=N) (per:=per) (x i)) o h
      (cropX Φ o r z) U=
      (∏i,ratioX (C.S.toDepth h per) (s i)*(C.S.a N:ℂ)^(s i))*fiber s x o h r Φ z U := by
  unfold scalp fiber
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [WilsonReportingTerminalPrimaryStencil.joint s x made,sampled s o h u r Φ z,Finset.prod_mul_distrib,Finset.prod_mul_distrib]
  ring

omit [DecidableEq I] in
private theorem scale (s:I→ℕ) (m:ℕ) (h:b≤N) (r:ℝ) :
    premiums C s m b r*(∏i,ratioX (C.S.toDepth h per) (s i)*(C.S.a N:ℂ)^(s i))=
      ∏i,((r:ℂ)⁻¹^4*(C.S.a m:ℂ)^(s i)*(C.S.a N:ℂ)^4) := by
  rw [premiums,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  let A:=C.S.toDepth h per
  have eq:(C.S.a N:ℂ)*(A.count.val:ℂ)=(C.S.a b:ℂ):=by exact_mod_cast C.S.embeds_scale A
  have n0:(C.S.a N:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne'
  have l0:(A.count.val:ℂ)≠0:=by exact_mod_cast A.count.property.ne'
  change ((r:ℂ)⁻¹^4*((C.S.a b:ℂ)^4*((C.S.a m:ℂ)/(C.S.a b:ℂ))^(s i)))*
    (((((A.count.val:ℝ)^(s i)/(A.count.val:ℝ)^4):ℝ):ℂ)*(C.S.a N:ℂ)^(s i))=_
  rw [←eq,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_pow,div_pow,mul_pow,mul_pow]
  push_cast
  field_simp

theorem original (made:C.Makes) (s:I→ℕ) (x:(i:I)→C.label (s i)) (h:b≤N) (m:ℕ)
    (r:ℝ) (Φ:Wave I) (g:Body) (U:Config G (C.side N per)) {cap:ℝ} (rp:0<r)
    (enclosed:∀u∈tsupport Φ.val,∀i,‖u i‖≤cap) (J:ℕ) (cut:r*cap+2*C.S.a b≤C.S.a b*(J:ℝ)) :
    constellation (C:=C) (p:=per) s (fun i=>WilsonReportingTerminalPrimaryStencil.upper (N:=N) (per:=per) (x i))
      r Φ h m g U =
      (∏i,((r:ℂ)⁻¹^4*(C.S.a m:ℂ)^(s i)*(C.S.a N:ℂ)^4))*
      ∑ o∈area (C:=C) (p:=per) (b:=b) (V:=I) J,
        ∫z in Native.box,g.val z * fiber s x o h r Φ z U := by
  let w:=fun i=>WilsonReportingTerminalPrimaryStencil.upper (N:=N) (per:=per) (x i)
  let Q:=∏i,ratioX (C.S.toDepth h per) (s i)*(C.S.a N:ℂ)^(s i)
  have one (o:I→Site (C.side b per)):meet s w r Φ h o g U=
      Q*(∫ z in Native.box,g.val z * fiber s x o h r Φ z U):=by
    unfold meet
    rw [←integral_const_mul]
    apply setIntegral_congr_fun Pert.Cellular.cells_compact.measurableSet
    intro z _
    change g.val z*(scalp (C:=C) s (fun i=>WilsonReportingTerminalPrimaryStencil.upper (N:=N) (per:=per) (x i)) o h (cropX Φ o r z) U)=_
    rw [field made s x o h r Φ z U]
    unfold Q;ring
  rw [stanza h s w r Φ rp enclosed J m cut g,Pi.smul_apply,smul_eq_mul,Finset.sum_apply]
  simp_rw [one]
  rw [←Finset.mul_sum,←mul_assoc,scale s m h r]

end YM.Integration.WilsonReportingTerminalPrimaryCensus
