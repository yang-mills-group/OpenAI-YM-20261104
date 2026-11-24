import YM.Integration.WilsonIndependentMatchedOpeningColumn
import YM.Integration.WilsonIndependentSpoutMuralBoard

/-! Recover all angular tensors on the literal ordinary torus before the first physical step. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedOpeningBoard
open Function Filter Finset PowerSeries Lattice RG Wilson Tree Source Labels XSpace XSpace.Rose Gauge
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.Bank
open PertExtension RegulatorIR RegulatorIR.Geometry RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.Prim RegulatorIR.Diagram RegulatorIR.Halo RegulatorIR.Oracle RegulatorIR.Cluster
open WilsonIndependentSpoutFiniteStencil (Raw coordinates)
open WilsonIndependentSpoutPrimitiveReport (axis picture)
open WilsonIndependentSpoutAtomicPolar (seats)
open WilsonIndependentSpoutOrdinaryPlate (sample)
open WilsonIndependentMatchedOpeningColumn (column)
open scoped Classical BigOperators
variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G){d D:ℕ}
local notation "F" => R.family.labels.level d

def folded (n:Side)(P:Ranked (Foot G)):Ranked (WilsonIndependentSpoutFiniteStencil.Raw G n):=fun r=>
  Stalk.collect (fun q:Tuple (Foot G) r=>coordinates n∘q) (P r)

theorem read (n:Side)(P:Ranked (Foot G))(cap:ℕ)(v:TreeVars G n)(finite:∀r,Bounded (P r)):
    drums (folded n P) cap (axis v)=drums P cap (sample v):=by
  unfold drums
  apply Finset.sum_congr rfl
  intro r _
  exact picture (coordinates n) (P r) (finite r) (axis v)

theorem recover {h:ℕ}(T:Orders (Foot G))(M:Era G ℝ)(auth:Auth h M)
    (finite:∀e r,Bounded (T e r))(symmetric:gradedSymmetric T)(scope:Ranks h T)
    (n:Side)(ray:∀v:TreeVars G n,WilsonIndependentMatchedOrdinarySeat.here n v (Blue.flash (M.1 n))=
      RegulatorIR.Halo.shelter h T (sample v))(e:ℕ):
    folded n (T e)=fun r z=>M.1 n e r (seats n∘z):=by
  have cap (r)(hr:e+h<r):(M.1 n e) r=0:=auth.span n e r (by omega)
  apply guessed (k:=e+h)
  · exact WilsonIndependentSpoutAtomicPolar.supported _ (scope e)
  · intro r nz
    by_contra! hr;apply nz;funext z
    exact congrFun (cap r hr) (seats n∘z)
  · intro r;exact WilsonIndependentSpoutAtomicPolar.symmetric _ (symmetric e r)
  · intro r σ z;exact auth.pale n e r σ (seats n∘z)
  · intro x
    obtain ⟨y,rfl⟩:=WilsonIndependentSpoutAtomicPolar.all n x
    rw [read n (T e) (e+h) y (finite e)]
    have heard:=congrArg (PowerSeries.coeff e) (ray y)
    simp only [WilsonIndependentMatchedOrdinarySeat.here,PowerSeries.coeff_map,Blue.flash,PowerSeries.coeff_mk,
      RegulatorIR.Halo.shelter] at heard
    exact heard.symm.trans (WilsonIndependentSpoutAtomicPolar.held (seats n) (M.1 n e) (e+h) cap y).symm

theorem original (survey:Bool)(w:d<D)(a:Alma F)(o:Cover)(n:Side)(e:ℕ):
    folded n (WilsonIndependentRawNamedStencil.shifted R W survey d (sheet F a) o e)=
      fun r z=>(column R W survey w a o).1 n e r (seats n∘z):=by
  have m:=WilsonIndependentRawNamedStencil.named R W survey d (sheet F a) o
  exact recover _ _ (WilsonIndependentMatchedOpeningColumn.enrolled R W survey w a o)
    m.1.canopy m.1.symmetry m.2 n (WilsonIndependentMatchedOpeningColumn.ray R W survey w a o n) e

end YM.Integration.WilsonIndependentMatchedOpeningBoard
