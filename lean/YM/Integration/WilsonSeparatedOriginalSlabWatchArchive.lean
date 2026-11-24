import YM.Integration.WilsonSeparatedOriginalSlabWatchInvoice
import YM.Integration.WilsonSeparatedOriginalSlabWatchOrder

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchArchive
open Set Function Filter MeasureTheory Spec OPE OPE.Orbits PhysMS Lattice Wilson Next.UVStress RG05Readout RG05Readout.Native RG05Readout.Pulse
open WilsonSeparatedOriginalSlabWatchBorn WilsonSeparatedOriginalSlabWatchMean WilsonSeparatedOriginalSlabWatchNormalization WilsonReportingUnitOrbit
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{n:ℕ}

def average (F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (s:Fin n→ℕ)(h:ℕ)(r:ℝ)(a:(i:Fin n)→S.Field (s i))(φ:Test n):S.Field h:=
  ∫y:Points n,φ y • R.packet h (fun i=>r • y i) a 0

theorem settled (F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (s:Fin n→ℕ)(h:ℕ)(r:ℝ)(a:(i:Fin n)→S.Field (s i))(m:ℕ)
    {θ:ℝ}(ht:θ∈Icc (0:ℝ) 1)(A:Set (Cloud (Fin n)))(closed:IsCompact A)
    (Ψ:Wave (Fin n))(filed:tsupport Ψ.val⊆A)(g:Body){η M:ℝ}(pos:0<η)
    (apart:∀x∈A,∀i j:Fin n,i≠j→η≤‖x i-x j‖)(size:∀x∈A,∀i,‖x i‖≤M):
    WilsonSeparatedOriginalSlabWatchInvoice.calibrated F R s h r a m (wave θ Ψ g)=
      factor C s m • average F R s h r a (WilsonSeparatedOriginalSlabWatchTest.physical ht A closed Ψ filed g pos apart size):=by
  apply congrArg (factor C s m • ·)
  exact WilsonSeparatedOriginalSlabWatchOrder.read (fun y=>(wave θ Ψ g).val y • R.packet h (fun i=>r • y i) a 0)

theorem live (C:Family G)(s:Fin n→ℕ)(m:ℕ):factor C s m≠0:=by
  unfold factor
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (Suede.pitch_pos _))) (Finset.prod_ne_zero_iff.mpr (fun i _=>pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos m).ne')))

theorem currency (C:Family G)(s:Fin n→ℕ)(m:ℕ):
    ‖(factor C s m)⁻¹‖=‖phase‖^n/((C.S.a m)^(∑i,s i)):=by
  simp only [factor,norm_inv,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (C.S.a_pos m),Finset.prod_pow_eq_pow_sum,Fintype.card_fin]
  simp [div_eq_mul_inv,inv_pow,mul_comm]

theorem hearing (W:Watch C)(h:ℕ)(s:Fin n→ℕ)(m:ℕ)(v q:S.Field h):
    ‖W.tester S h ((factor C s m)⁻¹ • v-q)‖=(‖phase‖^n/(C.S.a m)^(∑i,s i))*‖W.tester S h (v-factor C s m • q)‖:=by
  rw [←currency C s m,←norm_smul,←map_smul,smul_sub,smul_smul,inv_mul_cancel₀ (live C s m),one_smul]

end YM.Integration.WilsonSeparatedOriginalSlabWatchArchive
