import YM.Integration.WilsonIndependentMatchedOpeningCover
/-! Fixed real torus readings of the whole received series determine both fields of an admitted Mer word. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedOpeningFaithful
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
open WilsonIndependentMatchedOrdinarySeat (here)
open scoped Classical Topology
variable {G:Gauge}{h:ℕ}{M N:Era G ℝ}
theorem finite (p:Auth h M)(q:Auth h N)(n:Side)
    (held:∀y:TreeVars G n, here n y (Blue.flash (M.1 n))=here n y (Blue.flash (N.1 n))):
    M.1 n=N.1 n:=by
  funext e r z
  have bound {O:Era G ℝ}(f:Auth h O)(t)(ht:e+h<t):(O.1 n e) t=0:=f.span n e t (by omega)
  have polar: (fun t (y:Tuple (WilsonIndependentSpoutFiniteStencil.Raw G n) t)=>M.1 n e t (seats n∘y))=
    fun t (y:Tuple (WilsonIndependentSpoutFiniteStencil.Raw G n) t)=>N.1 n e t (seats n∘y):=by
    apply guessed (k:=e+h)
    · intro t nz;by_contra! ht;apply nz;funext y;exact congrFun (bound p t ht) (seats n∘y)
    · intro t nz;by_contra! ht;apply nz;funext y;exact congrFun (bound q t ht) (seats n∘y)
    · intro t σ y;exact p.pale n e t σ (seats n∘y)
    · intro t σ y;exact q.pale n e t σ (seats n∘y)
    · intro v
      obtain ⟨y,rfl⟩:=WilsonIndependentSpoutAtomicPolar.all n v
      have test:=congrArg (PowerSeries.coeff e) (held y)
      simp only [WilsonIndependentMatchedOrdinarySeat.here,PowerSeries.coeff_map,Blue.flash,PowerSeries.coeff_mk] at test
      exact (WilsonIndependentSpoutAtomicPolar.held (seats n) _ (e+h) (bound p) y).trans
        (test.trans (WilsonIndependentSpoutAtomicPolar.held (seats n) _ (e+h) (bound q) y).symm)
  have eqn:=congrFun (congrFun polar r) ((seats n).symm∘z)
  simpa only [←Function.comp_assoc,Equiv.self_comp_symm,Function.id_comp] using eqn

theorem original (p:Auth h M)(q:Auth h N)
    (held:∀(n:Side)(y:TreeVars G n),here n y (Blue.flash (M.1 n))=here n y (Blue.flash (N.1 n))):
    M=N:=by
  have all (n:Side):M.1 n=N.1 n:=finite p q n (held n)
  refine Prod.ext (funext all) ?_
  funext e r z
  exact tendsto_nhds_unique ((p.wing e r).point z)
    (((q.wing e r).point z).congr (fun n=>congrFun (congrFun (congrFun (all n).symm e) r) _))
end YM.Integration.WilsonIndependentMatchedOpeningFaithful
