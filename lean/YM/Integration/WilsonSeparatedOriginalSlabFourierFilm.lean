import YM.Integration.WilsonSeparatedOriginalSlabDriven

/-! Each finite Fourier superposition is reported on all three genuine child residues and all original gauge fields. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabFourierFilm
open PhysicalNext.Repeat.Legato WilsonSeparatedOriginalSlabReplicaFilm
open Function Finset Set MeasureTheory RG Lattice Wilson Source RG05Readout RG05Readout.Native RG05Readout.Pulse
open RG05Readout.Address RG05Readout.Flatten WilsonSeparatedOriginalSlabReplicaStencil WilsonSeparatedOriginalSlabPlaneTest
open WilsonSeparatedOriginalSlabFourierDeposit WilsonSeparatedOriginalSlabDriven
open scoped BigOperators Classical Topology
local notation "I"=>Fin 3
variable {G:Gauge}(R:Run G){b N per:ℕ}(top:b+1≤N)(s:I→ℕ)
local notation "C"=>R.family
local notation "step"=>b.le_succ.trans top

def frequency (actual:(i:Fin 3)→Palette R.family (s i))(r:ℝ)(m:ℕ)(w:I→Axis→ℝ):ℂ:=
  premiums C s m b r * ∑y:I→Site ((C).side b per), ∑t:I→Site (((C).S.toDepth step per).count), ∑a:(i:I)→Mark C (s i), measured s R (per:=per) top actual y t a * price s y step w t a

theorem mode (actual:(i:Fin 3)→Palette R.family (s i))(r:ℝ)(hr:0<r)(m:ℕ)(w:I→Axis→ℝ)(g:Body):
    WilsonSeparatedOriginalSlabReplicaFiscal.observable R (per:=per) top s actual r (packet w (r/(C).S.a b)) m g=
      frequency R (per:=per) top s actual r m w * ((tariff:ℂ)*filed w g):=by
  rw [WilsonSeparatedOriginalSlabReplicaStencil.original,restored]
  simp only [stencil,LinearMap.smul_apply,LinearMap.sum_apply,smul_eq_mul]
  simp_rw [WilsonSeparatedOriginalSlabFourierDeposit.original s _ step w r hr]
  simp only [frequency,mul_assoc,Finset.sum_mul]

theorem original (actual:(i:Fin 3)→Palette R.family (s i)){V:Type}(B:Finset V)(w:V→I→Axis→ℝ)(c:V→ℂ)(r:ℝ)(hr:0<r)(m:ℕ)(g:Body):
    WilsonSeparatedOriginalSlabReplicaFiscal.observable R (per:=per) top s actual r
      (∑j∈B,c j • packet (w j) (r/(C).S.a b)) m g=
      ∑j∈B,c j * (frequency R (per:=per) top s actual r m (w j) * ((tariff:ℂ)*filed (w j) g)):=by
  rw [WilsonSeparatedOriginalSlabReplicaStencil.original]
  simp only [map_sum,map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [←WilsonSeparatedOriginalSlabReplicaStencil.original,mode R top s actual r hr]

end YM.Integration.WilsonSeparatedOriginalSlabFourierFilm
