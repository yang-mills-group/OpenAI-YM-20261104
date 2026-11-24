import YM.Integration.WilsonSeparatedOriginalSlabReplicaFiscal

/-! Fixed cutoff words in the signed three-copy measurement. The test acts only through its actual integrated derivative at each cell. -/
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option quotPrecheck false

namespace YM.Integration.WilsonSeparatedOriginalSlabReplicaStencil
open Function Finset Set MeasureTheory Lattice Wilson RG Source
open PhysicalNext.Repeat.Legato RG05Readout Address Native Pulse Flatten
open WilsonSeparatedOriginalSlabReplicaReading WilsonSeparatedOriginalSlabReplicaFilm
open private coefficient entry exposed from YM.Integration.WilsonSeparatedOriginalReplicaRegularity
open private tested finite_meet from YM.Integration.WilsonSeparatedOriginalReplicaRegularity
open scoped Classical Topology BigOperators
variable {G:Gauge}{C:Family G}{b N per:ℕ}
local notation "I"=>Fin 3
variable (s:I→ℕ)(o:I→Site (C.side b per))(h:b≤N)
local notation "A"=>C.S.toDepth h per
local notation "Sites"=>I → Site (A).count
local notation "Letters"=>(i:I) → Mark C (s i)

def atSite (r:ℝ)(t:Sites)(z:E4)(a:Letters):Wave I→ₗ[ℂ]ℂ where
  toFun Ψ:=coefficient s o h Ψ r t z a
  map_add' f k:=by
    simp only [coefficient,exposed,map_add,AddMemClass.coe_add,Pi.add_apply,mul_add]
  map_smul' c f:=by
    simp only [coefficient,exposed,map_smul,SetLike.val_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    ring

def weight (r:ℝ)(t:Sites)(a:Letters)(g:Body):Wave I→ₗ[ℂ]ℂ where
  toFun f:=∫z in Native.box,g.val z*atSite s o h r t z a f
  map_add' f k:=by
    simp only [map_add,mul_add]
    exact integral_add (tested s o h f r t a g) (tested s o h k r t a g)
  map_smul' c f:=by
    simp only [map_smul,smul_eq_mul,RingHom.id_apply]
    simp_rw [mul_left_comm (g.val _) c]
    exact integral_const_mul ..

variable (v:(i:I)→Palette C (s i))
theorem deposited (r:ℝ)(g:Body)(f:Wave I):
    film s v o h f r g=∑t:Sites,∑a:Letters,weight s o h r t a g f • cell s v o h t a:=by
  ext U
  simp only [ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
  exact finite_meet s v o h f r g U

variable (R:Run G)(top:b+1≤N)
local notation "S"=>R.family
local notation "step"=>b.le_succ.trans top
local notation "Origins"=>I → Site ((S).side b per)
local notation "children"=>I → Site (((S).S.toDepth step per).count)
local notation "alphabet"=>(i:I) → Mark (S) (s i)
local notation "μ"=>WilsonMacroscopicRichFlatPosteriorLaw.law R N per top (1:Config G ((S).side b per))
local instance probability:IsProbabilityMeasure μ:=WilsonMacroscopicRichFlatPosteriorLaw.prob R top le_rfl 1

def measured (v:(i:I)→Palette (S) (s i))(y:Origins)(t:children)(a:alphabet):ℂ:=
  WilsonSeparatedOriginalReplicaFunctional.listener μ (cell s v y step t a)

def stencil (v:(i:I)→Palette (S) (s i))(r:ℝ)(m:ℕ)(g:Body):Wave I→ₗ[ℂ]ℂ:=
  premiums (S) s m b r • ∑y:Origins,∑t:children,∑a:alphabet,measured s R top v y t a • weight s y step r t a g

theorem original (v:(i:I)→Palette (S) (s i))(r:ℝ)(f:Wave I)(m:ℕ)(g:Body):
    WilsonSeparatedOriginalSlabReplicaFiscal.observable R (per:=per) top s v r f m g=stencil s R (per:=per) top v r m g f:=by
  unfold WilsonSeparatedOriginalSlabReplicaFiscal.observable
  rw [WilsonSeparatedOriginalSlabReplicaSurface.register]
  simp only [deposited,map_smul,map_sum,smul_eq_mul,stencil,LinearMap.smul_apply,LinearMap.sum_apply]
  congr 1
  apply Finset.sum_congr rfl;intro y _
  apply Finset.sum_congr rfl;intro t _
  apply Finset.sum_congr rfl;intro a _
  exact mul_comm ..

end YM.Integration.WilsonSeparatedOriginalSlabReplicaStencil
