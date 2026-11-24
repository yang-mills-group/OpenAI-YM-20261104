import YM.OPE.Compatible.Glim.Ferr
/-! # Diff rank poly. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc
variable {E F I:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable (L:Law E)
-- exp derivative for smooth at 0: uses exact negative log.B
lemma pokeExp (u:E)(X:E→ℝ)(hx:ContDiffAt ℝ ω X 0):
    let f:=Real.exp ∘ fun x=> -X x
    Pry u (Pawn.mold f 0)= -(Pawn.mold f 0) * Pry u (Pawn.mold X 0):=by
       intro f; have hw:ContDiffAt ℝ ω f 0:= hx.neg.exp
       rw [pry_m0 f hw,pry_m0 X hx]; let g:= bat u X; have hv : bat u f=ᶠ[𝓝 0] f * (-g):=by
            filter_upwards [hx.eventually (by simp)] with x h; have hp:= h.differentiableAt (by simp); change fderiv ℝ f x u= f x *-g x; have hv: HasFDerivAt f (Real.exp (-X x) • -(fderiv ℝ X x)) x:=(hp.hasFDerivAt.neg).exp; rw [hv.fderiv];rfl
       let Z:= Pawn.mold g 0; have hz:ContDiffAt ℝ ω g 0:=picked X hx u; have hh : Pawn.mold (-g) 0 = -Z:=by
            funext x; exact ((Pawn.calm (hz.neg.of_le le_top)).stale x).equality (Reads.neg ((Pawn.calm (hz.of_le le_top)).stale x)) -- lemma
       rw [meltSame _ _ hv,meltJ f (-g) hw hz.neg,hh]; unfold Z g; ring
abbrev spur (p:ScriptJ E):ScriptJ E:= low (fun i=>(p i).s)
-- wheel exp in Token ring
lemma PryWheel (v:E)(p: ScriptJ E)(h:p.B):
     Pry v (wheel p)= -(wheel p) * (Pry v p-spur (Pry v p)):=by
       let p1(x:E):=(p x).l; let p2(x:E):=(p x).h; funext x; have hp:DifferentiableAt ℝ p1 x:=(show ContDiff ℝ ω p1 from (h 1).smooth).differentiable (by simp) x; have hx:DifferentiableAt ℝ p2 x:=(show ContDiff ℝ ω p2 from (h 2).smooth).differentiable (by simp) x
       apply eta
       · change fderiv ℝ (fun _:E=>(1:ℝ)) x v=(-1:ℝ)*(_-_); erw [fderiv_const_apply,sub_self, mul_zero];rfl
       · change fderiv ℝ (fun i:E=> -p1 i) x v=(-1:ℝ)*(_-0)+ _*(_-_); rw [fderiv_fun_neg]; simp only[_root_.neg_apply,sub_zero,spur,low,sub_self, mul_zero,add_zero,neg_mul,one_mul];rfl
       let y:E→ℝ:=fun i=>p1 i*p1 i; have hy:DifferentiableAt ℝ y x:=hp.mul hp; change fderiv ℝ (fun i=> -p2 i+(p1 i)^2/2) x v= (-1:ℝ) * (fderiv ℝ p2 x v-0) +(- - (p1 x)) * (fderiv ℝ p1 x v-0)+ _*(_-_); rw [show (fun i=> -p2 i+(p1 i)^2/2)=fun i=>(-p2) i+y i*(2:ℝ)⁻¹ from funext fun i=>by simp [y,pow_two];ring]; erw [fderiv_fun_add hx.neg (hy.mul_const (2:ℝ)⁻¹), fderiv_fun_neg,fderiv_mul_const hy];
       unfold y; rw [fderiv_fun_mul hp hp]; simp [spur,low];ring
lemma billing (x z:E): fderiv ℝ (fun y:E=> L.P y y/2) x z=L.P z x:=by
      let f:E→ℝ:=fun y=>L.P y y/2; let w(t:ℝ):=x+t • z; have hv : HasDerivAt w z 0:= by simpa [w] using! ((hasDerivAt_id' (0:ℝ)).smul_const z).const_add x
      have ht:DifferentiableAt ℝ (fun x:E=>L.P x x) (w 0):=(Libra.Pose.standE L).smooth.differentiable (by simp) (w 0); have hp:DifferentiableAt ℝ f (w 0):= by unfold f; simp_rw [div_eq_mul_inv]; exact ht.mul_const _
      have hg : HasDerivAt (f∘w) (fderiv ℝ f x z) 0:=by have he:=hp.hasFDerivAt.comp_hasDerivAt 0 hv; rw [show w 0=x from by simp [w]] at he; exact he
      apply hg.unique; rw [show f∘w=fun i:ℝ=>f x+L.P z x*i+(L.P z z/2)*i^2 from ?_]; swap
      · funext i; unfold w f; simp only [Function.comp_apply,map_add,LinearMap.add_apply,map_smul,LinearMap.smul_apply,smul_eq_mul, L.turns x z]; ring
      convert! (((hasDerivAt_id' (0:ℝ)).const_mul (L.P z x)).const_add (f x)).add (((hasDerivAt_id' (0:ℝ)).pow 2).const_mul (L.P z z/2)) using 1;ring
end YM.OPE.Variance
