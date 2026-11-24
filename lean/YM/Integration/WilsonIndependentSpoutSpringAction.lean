import YM.Integration.WilsonIndependentSpoutWilsonAction

/-! Equality of the stored conditional spring energies on the same finite
tree fields, with the true tag and the inversion-orbit factor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentSpoutSpringAction
open Lattice RG Wilson WilsonCoeffUV WilsonCoeffUV.Blue Precision
open RegulatorIR RegulatorIR.Binding RegulatorIR.Geometry RegulatorIR.Laplace
open PertExtension PertExtension.Orb PertExtension.Chart Filter
open WilsonIndependentSpoutWilsonAction
open scoped Classical Topology
variable {G:Gauge}{c f:Side}(S:StepData c f)

theorem directive_price (hc:Even c.val)(hf:Even f.val)(Z:S.patch.Branches S.kernel G)
    (U:spins G f)(V:spins G c):
    noiseTaylor S (orbLift V) (orbLift U) (directive S)=2*bond S U V := by
  let W:=predictor S U
  let D:Edge (Site c)→ℝ:=fun i=>G.price (orbLift V i*(orbLift W i)⁻¹)
  have reflected (i:OEdge c):D (reflect i.val)=D i.val:=by
    simp only [D,show ∀ (v:spins G c) i,orbLift v (reflect i)=(orbLift v i)⁻¹ from lift_flip hc,inv_inv]
    let a:=orbLift V i.val;let b:=orbLift W i.val
    change G.price (a⁻¹*b)=G.price (a*b⁻¹)
    rw [←G.price_inv (a⁻¹*b),show (a⁻¹*b)⁻¹=b⁻¹*(a*b⁻¹)*(b⁻¹)⁻¹ by group,G.price_conj]
  have half:(∑ j,D j)=2*(∑ i:OEdge c,D i.val):=by
    rw [←Equiv.sum_comp (Quadratic.both hc) D,Fintype.sum_sum_type]
    change (∑ i:OEdge c,D i.val)+(∑ i:OEdge c,D (reflect i.val))=_
    simp_rw [reflected,two_mul]
  rw [noiseTaylor,←pec S Z U hf]
  change S.kernel.penalty*(∑ i,D i)=2*(S.kernel.penalty*(∑ i:OEdge c,G.price (V i*(W i)⁻¹)))
  rw [half]
  simp only [D,orbLift,lift_at];ring

theorem groups (hc:Even c.val)(hf:Even f.val)(Z:S.patch.Branches S.kernel G) :
    ∀ᶠ U:spins G f in 𝓝 1,∀ V:spins G c,
      noiseTaylor S (orbLift V) (orbLift U) (tac S)=2*bond S U V := by
  have lift:Tendsto (orbLift:spins G f → Config G f) (𝓝 1) (𝓝 1):=by
    exact lift_one ▸ (lift_cont G).tendsto _
  filter_upwards [lift.eventually (Work.F04.prediction_germ Z (tac S) (directive S))] with U same
  intro V
  rw [←directive_price S hc hf Z U V,noiseTaylor,noiseTaylor,same]

def both (x:Horizon G f)(b:Horizon G c):Lawn (Joint G f c):=Sum.elim (opening x) (opening b)

theorem native (hc:Even c.val)(hf:Even f.val)(Z:S.patch.Branches S.kernel G) :
    ∀ᶠ x:Horizon G f in 𝓝 0,∀ b:Horizon G c,
      jointPen G S (both x b)=2*bond S (climb x) (climb b) := by
  have cont:Continuous (climb: Horizon G f→spins G f):=by
    apply continuous_pi;intro i
    exact G.lieExp_cont.comp (continuous_apply i)
  have ht:Tendsto (climb:Horizon G f→spins G f) (𝓝 0) (𝓝 1):=by
    simpa only [show (climb (0:Horizon G f):spins G f)=1 from expOrigin ..] using cont.tendsto 0
  filter_upwards [ht.eventually (groups S hc hf Z)] with x hx
  intro b
  have field {n:Side}(u:Horizon G n):mantle (opening u)=orbLift (climb u):=
    (mat_expanded u).symm
  change noiseTaylor S (mantle (opening b)) (mantle (opening x)) (tac S)=_
  rw [field,field]
  exact hx (climb b)

end YM.Integration.WilsonIndependentSpoutSpringAction
