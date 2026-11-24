import YM.Integration.PhysicalWilsonPeriodizedProgram

/-! The original coarse mean of the finite nonlinear step has a covering
prescription on the same registry as the heat covariance. The subtracted
coarse copy is retained in each actual input direction. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.PhysicalWilsonPeriodizedAffine
open Finset Function Matrix Lattice Wilson RG RG.Supply Precision Tree Exterior Laurent Bloch Stationary
open Marker Multi PhysicalNext.Repeat.Legato Comparison.RG02 Comparison.RG02.Order
open Comparison.RG02.Cumulants Next.Rank Next.SectorChange WilsonCoeffUV FreeResolvent MeasureTheory
open Stationary
open scoped Classical BigOperators Matrix.Norms.Frobenius

variable {G:Gauge} (R:Run G) (N m p:ℕ) (hm:m<N)
local notation "A" => R.family.path.levels
local notation "S" => (A).clock.op m p
local notation "F₀" => repeatF (S)
local notation "t₀" => PhysicalWilsonPeriodizedProgram.branch (S)
local notation "I" => Key (F₀) G
local notation "K₀" => (RunFormalChain.fromRun R).step N m p hm

def prediction:=((feedA (A) N m).acts ((A).S.side m p)).submatrix (unitSplit G (S) 1) id

include hm in
theorem matrix : prediction R N m p=
    tensor G (extracted (S) (F₀) (installed (S).ratio (predictionA (A) N m))):=by
  unfold prediction
  rw [feed_period (A) N m hm _ _ (S).sizes]
  ext i j
  simp only [repackM,Matrix.submatrix_apply,Equiv.refl_symm,Equiv.refl_apply,id_eq]
  change tensor G (extracted (S) (F₀) (installed (S).ratio (predictionA (A) N m)))
    ((unitSplit G (S) 1).symm (unitSplit G (S) 1 i)) j = _
  rw [Equiv.symm_apply_apply]

variable (B:fieldDir G (R.family.side m p) 1)
def relativeMean : (I)→ℝ :=
  reduce G (S) (F₀) *ᵥ(prediction R N m p *ᵥflatten B) -
    OriginalMarkedHeatCovariance.copyCharge R m p (F₀) B

theorem field : fderiv ℝ ((K₀).b (F₀)) 0 B=profile (F₀) (relativeMean R N m p B):=by
  have h:=OriginalMarkedHeatCovariance.stationary R N m p hm (F₀) (t₀) B
  rw [← matrix R N m p hm] at h
  funext i
  ext j
  exact congrFun h (i,j)

theorem stage : Bulk.stage (K₀) (F₀) B=((1:ℝ),B,profile (F₀) (relativeMean R N m p B)):=by
  change ((1:ℝ),B,fderiv ℝ ((K₀).b (F₀)) 0 B)=_
  rw [field R N m p hm B]

variable {V:Type} [Fintype V] [DecidableEq V] {Γ:Census V}
variable (W:Bulk.Colors Γ G (R.family.side (m+1) p)) (r:ℕ)
def vertex : Hot (Board Γ r) → Normal.poly (I):=
  Assembly.generator ((1:ℝ),B,profile (F₀) (relativeMean R N m p B)) (Bulk.hinge (F₀)) W.power
    (Bulk.markFn (S) (F₀) W) (Bulk.geometric (K₀) (F₀) (t₀) W) r

theorem vertices : PhysicalWilsonPeriodizedProgram.vertex R N m p hm W B r=
    vertex R N m p hm B W r:=by
  unfold vertex PhysicalWilsonPeriodizedProgram.vertex
  rw [stage R N m p hm B]

def cover : Grade Γ r:=Poly.inject fun s=>
  ∫ z,Cloud.paint z (Cloud.integrand (vertex R N m p hm B W r) s)
    ∂Gaussian.cloud (PhysicalWilsonPeriodizedProgram.kernel R N m p)

variable (F:Forest (R.family.path.levels.clock.op m p).ratio)
variable (tag:(R.family.path.levels.clock.op m p).Choices)
theorem program (hw:Bulk.Well W):
    Bulk.Fk (K₀) F tag W B r=cover R N m p hm B W r:=by
  rw [PhysicalWilsonPeriodizedProgram.measured R N m p hm W B r F tag hw]
  unfold PhysicalWilsonPeriodizedProgram.cover cover
  rw [vertices R N m p hm B W r]

theorem normalized (hw:Bulk.Well W):
    logMarked (Bulk.Fk (K₀) F tag W B r)=logMarked (cover R N m p hm B W r):=
  congrArg logMarked (program R N m p hm B W r F tag hw)

end YM.Integration.PhysicalWilsonPeriodizedAffine
end
