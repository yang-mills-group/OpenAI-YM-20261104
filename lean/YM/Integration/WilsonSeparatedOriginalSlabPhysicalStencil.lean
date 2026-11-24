import YM.Integration.WilsonSeparatedOriginalSlabPrimaryWave
import YM.Integration.WilsonReportingTerminalProfileQuadrature
import YM.Integration.WilsonPositionSeparatedProfileCenteredOrbit

/-! The elected ultraviolet primary on a genuine joint test is a physical Wilson site census. Its phase and engineering normalization are explicit, including each input's true site. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabPhysicalStencil
open Function Set Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Pulse RG05Readout.Records
open WilsonReportingUnitOrbit WilsonReportingTerminalPrimaryStencil WilsonSeparatedOriginalSlabPrimaryWave
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {C:Family G} {I:Type}[Fintype I][DecidableEq I] {N per:ℕ}

/-- The gauge-dependent part of the true finite test, with its full upper sum of jointly positioned points. -/
def sample (s:I→ℕ)(v:(i:I)→C.label (s i))(Φ:Wave I)(U:Config G (C.side N per)):ℂ:=
  ∑x:I→Site (C.side N per), Φ.val (C.S.place ∘ x)*∏i,C.O N per (v i) (x i) U

def mesh (s:I→ℕ)(m N:ℕ):ℂ:= (phase⁻¹)^Fintype.card I * ∏i,((C.S.a m:ℂ)^(s i)*(C.S.a N:ℂ)^4)

theorem regular (h:C.Makes)(s:I→ℕ)(v:(i:I)→C.label (s i))(z:I→Site (C.side N per))(Φ:Wave I)(U:Config G (C.side N per)):
    harpoon s (fun i=>upper (N:=N) (per:=per) (v i)) z (fork (C.S.a N) (C.S.place ∘ z) Φ) U=
      ((phase⁻¹)^Fintype.card I * ∏i,(C.S.a N:ℂ)^(s i)) * (Φ.val (C.S.place ∘ z)*∏i,C.O N per (v i) (z i) U):=by
  rw [WilsonReportingTerminalPrimaryStencil.joint s v h z _ U,waveform,Finset.prod_mul_distrib]
  change ((phase⁻¹)^Fintype.card I * Φ.val ((C.S.place ∘ z)+C.S.a N • (0:Cloud I))) * _ = _
  rw [smul_zero,add_zero];ring

theorem joint (h:C.Makes)(s:I→ℕ)(v:(i:I)→C.label (s i))(m:ℕ)(Φ:Wave I)(U:Config G (C.side N per)):
    multi C m N per s (fun i=>upper (N:=N) (per:=per) (v i)) Φ U=mesh (C:=C) s m N * sample s v Φ U:=by
  have census:(∏i,gate C m N (s i))*(∏i,(C.S.a N:ℂ)^(s i))=∏i,((C.S.a m:ℂ)^(s i)*(C.S.a N:ℂ)^4):=by
    rw [←Finset.prod_mul_distrib];apply Finset.prod_congr rfl;intro i _
    have hn:(C.S.a N:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (C.S.a_pos N).ne'
    rw [gate,div_pow];field_simp
  simp only [multi,LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.comp_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  have each (z:I→Site (C.side N per)):
      harpoon s (fun i=>upper (N:=N) (per:=per) (v i)) z (fork (C.S.a N) (fun i=>C.S.place (z i)) Φ) U=
        ((phase⁻¹)^Fintype.card I * ∏i,(C.S.a N:ℂ)^(s i)) * (Φ.val (C.S.place ∘ z)*∏i,C.O N per (v i) (z i) U):=regular h s v z Φ U
  simp_rw [each]
  rw [←Finset.mul_sum];unfold mesh sample;rw [←census];ring

end YM.Integration.WilsonSeparatedOriginalSlabPhysicalStencil
