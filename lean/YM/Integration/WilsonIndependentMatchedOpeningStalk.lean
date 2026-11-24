import YM.Integration.WilsonIndependentSpoutMuralBoard
/-! A genuinely bounded angular tensor agrees with its finite periodization at every fixed cover tuple eventually. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedOpeningStalk
open Function Filter Finset Lattice RG RegulatorIR RegulatorIR.Geometry RegulatorIR.Prim
open RegulatorIR.Budget RegulatorIR.Budget.Packet WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonIndependentSpoutFiniteStencil (Raw coordinates)
open scoped Classical Topology
variable {G:Gauge}{r:ℕ}
private theorem separate (x y:Tuple (Foot G) r):
    ∀ᶠ n:Side in atTop,(coordinates n∘x=coordinates n∘y)→x=y:=by
  filter_upwards [eventually_all.mpr (fun i=>lift_ready (x i).1.1),
    eventually_all.mpr (fun i=>lift_ready (y i).1.1)] with n hx hy same
  funext i
  have h:=congrFun same i
  exact Prod.ext (Prod.ext ((hx i).symm.trans ((congrArg (fun z:Raw G n=>lift z.1.1) h).trans (hy i)))
    (congrArg (fun z:Raw G n=>z.1.2) h)) (congrArg (fun z:Raw G n=>z.2) h)

theorem original (T:Packet (Foot G) r)(bounded:Bounded T)(q:Tuple (Foot G) r):
    ∀ᶠ n:Side in atTop,Stalk.collect (fun z:Tuple (Foot G) r=>coordinates n∘z) T (coordinates n∘q)=T q:=by
  let A:=bounded.toFinset
  filter_upwards [(eventually_all_finset A).mpr (fun z _=>separate z q)] with n lawful
  apply tsum_eq_single (⟨q,rfl⟩:Stalk (fun z:Tuple (Foot G) r=>coordinates n∘z) (coordinates n∘q))
  intro z different
  by_contra nz
  apply different
  exact Subtype.ext (lawful z.val (bounded.mem_toFinset.mpr nz) z.property)
end YM.Integration.WilsonIndependentMatchedOpeningStalk
