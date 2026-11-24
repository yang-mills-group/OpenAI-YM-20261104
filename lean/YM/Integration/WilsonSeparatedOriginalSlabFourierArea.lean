import YM.Integration.WilsonSeparatedOriginalSlabFourierFilm
import YM.Integration.WilsonSeparatedOriginalSlabActiveWeights

/-! Restrict the actual joint measurement to its own physical parent region before taking any Fourier expansion. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabFourierArea
open PhysicalNext.Repeat.Legato WilsonSeparatedOriginalSlabReplicaFilm
open Function Finset Set MeasureTheory RG Lattice Wilson Source RG05Readout RG05Readout.Native RG05Readout.Pulse
open RG05Readout.Address RG05Readout.Flatten WilsonSeparatedOriginalSlabReplicaStencil WilsonSeparatedOriginalSlabPlaneTest
open WilsonSeparatedOriginalSlabFourierDeposit WilsonSeparatedOriginalSlabDriven
open scoped BigOperators Classical Topology
local notation "I"=>Fin 3
variable {G:Gauge}(R:Run G){b N per:ℕ}(top:b+1≤N)(s:I→ℕ)
local notation "C"=>R.family
local notation "step"=>b.le_succ.trans top
local notation "Parents"=>I→Site ((C).side b per)
local notation "T"=>I→Site (((C).S.toDepth step per).count)
local notation "L"=>(i:I)→Mark C (s i)

def onArea (v:(i:I)→Palette C (s i))(Y:Finset Parents)(r:ℝ)(m:ℕ)(g:Body):Wave I→ₗ[ℂ]ℂ:=
  premiums C s m b r • ∑y∈Y,∑t:T,∑a:L,measured s R (per:=per) top v y t a • weight s y step r t a g

theorem original (v:(i:I)→Palette C (s i)){r cap:ℝ}(rp:0<r)(Ψ:Wave I)
    (shape:∀x∈tsupport Ψ.val,∀i,‖x i‖≤cap)(m:ℕ)(g:Body):
    WilsonSeparatedOriginalSlabReplicaFiscal.observable R (per:=per) top s v r Ψ m g=
      onArea R (per:=per) top s v (Pulse.area (WilsonSeparatedOriginalSlabActiveWeights.range C b r cap)) r m g Ψ:=by
  rw [WilsonSeparatedOriginalSlabReplicaStencil.original]
  simp only [stencil,onArea,LinearMap.smul_apply,LinearMap.sum_apply,smul_eq_mul]
  congr 1
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro y _ hy; apply Finset.sum_eq_zero; intro t _; apply Finset.sum_eq_zero; intro a _
  rw [WilsonSeparatedOriginalSlabActiveWeights.original s y step rp Ψ shape hy t a g,mul_zero]

def frequency (v:(i:I)→Palette C (s i))(Y:Finset Parents)(r:ℝ)(m:ℕ)(w:I→Axis→ℝ):ℂ:=
  premiums C s m b r * ∑y∈Y,∑t:T,∑a:L,measured s R (per:=per) top v y t a * price s y step w t a

theorem mode (v:(i:I)→Palette C (s i))(Y:Finset Parents)(w:I→Axis→ℝ){r:ℝ}(rp:0<r)(m:ℕ)(g:Body):
    onArea R (per:=per) top s v Y r m g (packet w (r/(C).S.a b))=
      frequency R (per:=per) top s v Y r m w *((tariff:ℂ)*filed w g):=by
  rw [restored]
  simp only [onArea,LinearMap.smul_apply,LinearMap.sum_apply,smul_eq_mul]
  simp_rw [WilsonSeparatedOriginalSlabFourierDeposit.original s _ step w r rp]
  simp only [frequency,mul_assoc,Finset.sum_mul]

theorem film (v:(i:I)→Palette C (s i))(Y:Finset Parents){V:Type*}(B:Finset V)(w:V→I→Axis→ℝ)(c:V→ℂ)
    {r:ℝ}(rp:0<r)(m:ℕ)(g:Body):
    onArea R (per:=per) top s v Y r m g (∑j∈B,c j • packet (w j) (r/(C).S.a b))=
      ∑j∈B,c j*(frequency R (per:=per) top s v Y r m (w j)*((tariff:ℂ)*filed (w j) g)):=by
  simp only [map_sum,map_smul,smul_eq_mul,mode R top s v Y _ rp]

end YM.Integration.WilsonSeparatedOriginalSlabFourierArea
