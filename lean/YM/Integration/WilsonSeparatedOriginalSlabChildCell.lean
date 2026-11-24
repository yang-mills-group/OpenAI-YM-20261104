import YM.Integration.WilsonSeparatedOriginalSlabChildJoint
import YM.Integration.WilsonPositionSeparatedProfileCenteredReadout
import YM.Integration.WilsonSeparatedOriginalSlabWholeProfile

/-! The original clamped cell at its actual observation date equals the normalized finite sum of its complete child wave measurements. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabChildCell
open Function Set Finset MeasureTheory Lattice Wilson RG Source Extraction RG05Readout RG05Readout.Address RG05Readout.Native
open RG05Readout.Nuclear RG05Readout.Pulse RG05Readout.Records RG05Readout.Flatten PhysicalNext.Repeat.Legato
open WilsonSeparatedOriginalSlabChildSites
open scoped BigOperators Classical Topology
variable {G:Gauge}(R:Run G){b N per:ℕ}(s:Fin 3 → ℕ)(v:(i:Fin 3) → Palette R.family (s i))(top:b+1 ≤ N)
local notation "C"=>R.family
local notation "HH"=>Config G (R.family.side N per)
local notation "Bud₀"=>Bud R.family per b
local notation "A₀"=>R.family.S.oneStep b per

def sensor (o:Fin 3 → Site (R.family.side (b+1) per))(c:Site (R.family.side (b+1) per)):Wave (Fin 3) →ₗ[ℂ] ℂ:=
  WilsonSeparatedOriginalSlabWave.scan R s v (site A₀ o c) top top 1

private def field (r:ℝ)(Ψ:Wave (Fin 3))(m:ℕ)(g:Body)(i:Bud₀):C(HH,ℂ):=
  ⟨Pulse.constellation (p:=per) s v r Ψ top m (Many.headFee R.family per b i g) ∘
    pull 1 ((R.family.S.toDepth top per).embed (child R.family per b i)),
    (WilsonSeparatedOriginalReplicaRegularity.physical s v top Ψ r m _).comp (continuous_pull ..)⟩

private def base (r:ℝ)(Ψ:Wave (Fin 3))(m:ℕ)(g:Body):C(HH,ℂ):=
  ⟨Pulse.constellation (p:=per) s v r Ψ (b.le_succ.trans top) m g,WilsonSeparatedOriginalReplicaRegularity.physical s v _ Ψ r m g⟩

theorem average {r cap:ℝ}(rp:0<r)(Ψ:Wave (Fin 3))(shape:∀x∈tsupport Ψ.val,∀i:Fin 3,‖x i‖≤cap)
    (enclosed:r*cap+2*(C).S.a b<(C).S.radius per)(m:ℕ)(g:Body):
    actualTransport R.family (N:=N) (p:=per) (Pulse.constellation (p:=per) s v r Ψ (b.le_succ.trans top) m g) (b.le_succ.trans top) 1=
      (Fintype.card Bud₀:ℂ)⁻¹ * ∑i:Bud₀,actualTransport R.family (N:=N) (p:=per)
        (field R (per:=per) s v top r Ψ m g i:HH→ℂ) (b.le_succ.trans top) 1:=by
  let Z:=WilsonSeparatedOriginalResidentExpectation.mean R (per:=per) top 1
  let B:=base R (per:=per) s v top r Ψ m g
  let Y:=field R (per:=per) s v top r Ψ m g
  have assembled:B=(Fintype.card Bud₀:ℂ)⁻¹ • ∑i:Bud₀,Y i:=by
    ext U
    simp only [ContinuousMap.smul_apply,ContinuousMap.sum_apply,smul_eq_mul]
    exact (WilsonPositionSeparatedProfileCenteredSource.assembled R.family s v r Ψ top rp shape enclosed m g U).symm
  have held (i:Bud₀):Z (Y i)=actualTransport R.family (N:=N) (p:=per) (Y i:HH→ℂ) (b.le_succ.trans top) 1:=
    WilsonSeparatedOriginalResidentExpectation.value R top 1 (Y i)
  change actualTransport R.family (N:=N) (p:=per) (B:HH→ℂ) _ 1=_
  rw [←WilsonSeparatedOriginalResidentExpectation.value R top 1 B]
  change Z B=(Fintype.card Bud₀:ℂ)⁻¹ * ∑i:Bud₀,actualTransport R.family (N:=N) (p:=per) (Y i:HH→ℂ) _ 1
  rw [assembled,map_smul,map_sum,smul_eq_mul];simp_rw [held]

theorem original {r η X cap:ℝ}(rp:0<r)(room:r ≤ (C).S.a (b+1))(ep:0<η)(small:η ≤ 1)(Ψ:Wave (Fin 3))
    (rank:ℕ)(grade:(∑i:Fin 3,(s i+2))+4*Fintype.card (Fin 3)<rank+1)(scatter:Scattering Ψ η)(xp:0 ≤ X)
    (sizeX:Tall Ψ (rank+1) 1 X)(shape:∀x∈tsupport Ψ.val,∀i:Fin 3,‖x i‖≤cap)(enclosed:r*cap+2*(C).S.a b<(C).S.radius per)
    (m:ℕ)(g:Body):
    actualTransport R.family (N:=N) (p:=per) (Pulse.constellation (p:=per) s v r Ψ (b.le_succ.trans top) m g) (b.le_succ.trans top) 1=
      (Fintype.card Bud₀:ℂ)⁻¹*∑i:Bud₀,WilsonSeparatedOriginalSlabWholeProfile.whole R s
        (sensor R (per:=per) s v top) r Ψ m (Many.headFee R.family per b i g) (child R.family per b i):=by
  rw [average R s v top rp Ψ shape enclosed]
  congr 1;apply sum_congr rfl;intro i _
  exact WilsonSeparatedOriginalSlabChildJoint.original R s v top le_rfl A₀ (child R.family per b i) rp room ep small Ψ
    rank grade scatter xp sizeX (Many.headFee R.family per b i g) m

end YM.Integration.WilsonSeparatedOriginalSlabChildCell
