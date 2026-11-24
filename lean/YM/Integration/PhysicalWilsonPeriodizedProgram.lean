import YM.Integration.PhysicalWilsonPeriodizedGaussian
import YM.Comparison.RG02.Laplace.Choice

/-! The full finite normalized Fk on an actual measured input. The forest
change is made on the whole conditional before any normalized projection. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.PhysicalWilsonPeriodizedProgram
open Finset Function Matrix Lattice Wilson RG RG.Supply Precision Tree Exterior Laurent Bloch
open Marker Multi PhysicalNext.Repeat.Legato Comparison.RG02 Comparison.RG02.Order
open Comparison.RG02.Cumulants Next.Rank Next.SectorChange WilsonCoeffUV FreeResolvent MeasureTheory
open Stationary
open scoped Classical BigOperators Matrix.Norms.Frobenius

def branch {c f:Side} (S:StepData c f):S.Choices:=Classical.arbitrary _

private theorem evaluation {V I:Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    {Γ:Census V} (Q:Matrix I I ℝ) (sym:Q.IsSymm) (pos:Q.PosSemidef) (v:Hot Γ→Normal.poly I):
    Cloud.prescription Q sym 0 v=Poly.inject
      (fun s=>∫ z,Cloud.paint z (Cloud.integrand v s) ∂Gaussian.cloud Q):=by
  ext s
  change Cloud.wick Q sym 0 (Cloud.integrand v s)=∫ z,Cloud.paint z (Cloud.integrand v s) ∂Gaussian.cloud Q
  simpa only [zero_add,Cloud.shift_zero] using (Cloud.paid Q sym pos 0 (Cloud.integrand v s)).2.symm

variable {G:Gauge} (R:Run G) (N m p:ℕ) (hm:m<N)
local notation "A" => R.family.path.levels
local notation "S" => (A).clock.op m p
local notation "F₀" => repeatF (S)
local notation "t₀" => PhysicalWilsonPeriodizedProgram.branch (S)
local notation "I" => Key (F₀) G
local notation "K₀" => (RunFormalChain.fromRun R).step N m p hm
local notation "periodic" => (conditional (A) N m).acts ((A).S.side m p)
local notation "addr" => fun i:(I)=>unitSplit G (S) 1 (plant (G:=G) (F₀) i)

def kernel : Matrix (I) (I) ℝ := fun i j=>(periodic) ((addr) i) ((addr) j)

theorem line : (K₀).covariance (F₀) (t₀)=kernel R N m p :=
  PhysicalWilsonPeriodizedGaussian.contractions R N m p hm (t₀) id

variable {V:Type} [Fintype V] [DecidableEq V] {Γ:Census V}
variable (W:Bulk.Colors Γ G (R.family.side (m+1) p))
variable (B:fieldDir G (R.family.side m p) 1) (r:ℕ)
def vertex : Hot (Board Γ r) → Normal.poly (I):=
  Assembly.generator (Bulk.stage (K₀) (F₀) B) (Bulk.hinge (F₀)) W.power
    (Bulk.markFn (S) (F₀) W) (Bulk.geometric (K₀) (F₀) (t₀) W) r

def cover : Grade Γ r:=Poly.inject fun s=>
  ∫z,Cloud.paint z (Cloud.integrand (vertex R N m p hm W B r) s)
    ∂Gaussian.cloud (kernel R N m p)

theorem integrable (s:(Board Γ r).Mode):
    Integrable (fun z=>Cloud.paint z (Cloud.integrand (vertex R N m p hm W B r) s))
      (Gaussian.cloud (kernel R N m p)):=by
  rw [← line R N m p hm]
  simpa only [zero_add] using
   (Cloud.paid ((K₀).covariance (F₀) (t₀)) ((K₀).symm (F₀) (t₀))
    ((K₀).positive (F₀) (t₀)).posSemidef 0 (Cloud.integrand (vertex R N m p hm W B r) s)).1

variable (F:Forest (R.family.path.levels.clock.op m p).ratio)
variable (tag:(R.family.path.levels.clock.op m p).Choices)
theorem canonical:
    Bulk.Fk (K₀) (F₀) (t₀) W B r=cover R N m p hm W B r:=by
  let v:=vertex R N m p hm W B r
  let read (q:Matrix (I) (I) ℝ):Grade Γ r:=
    Poly.inject fun s=>∫ z,Cloud.paint z (Cloud.integrand v s) ∂Gaussian.cloud q
  exact (evaluation ((K₀).covariance (F₀) (t₀)) ((K₀).symm (F₀) (t₀))
    ((K₀).positive (F₀) (t₀)).posSemidef v).trans (congrArg read (line R N m p hm))

theorem reroute (hw:Bulk.Well W):
    Bulk.Fk (K₀) F tag W B r=Bulk.Fk (K₀) (F₀) (t₀) W B r:=
  (Laplace.identical (K₀) F (F₀) tag 0 W B ((R.family.path.rep N p m).p) r hw).2.trans
    (Bulk.fkChoice (K₀) (F₀) tag W B r (t₀))

theorem measured (hw:Bulk.Well W):
    Bulk.Fk (K₀) F tag W B r=cover R N m p hm W B r:=
  (reroute R N m p hm W B r F tag hw).trans (canonical R N m p hm W B r)

theorem normalized (hw:Bulk.Well W):logMarked (Bulk.Fk (K₀) F tag W B r)=
    logMarked (cover R N m p hm W B r):=
  congrArg logMarked (measured R N m p hm W B r F tag hw)

theorem mode (hw:Bulk.Well W) (t:(Board Γ r).Mode):
    (logMarked (Bulk.Fk (K₀) F tag W B r)).part t=(logMarked (cover R N m p hm W B r)).part t:=
  congrArg (fun z=>z.part t) (normalized R N m p hm W B r F tag hw)

end YM.Integration.PhysicalWilsonPeriodizedProgram
end
