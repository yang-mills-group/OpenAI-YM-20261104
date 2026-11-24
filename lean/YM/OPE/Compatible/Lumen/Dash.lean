import YM.OPE.Compatible.Lumen.Sight
/-!
# Coordinate dilation of Stand and linear-gauge representation. Branch product in single chart by preassign.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace YM.OPE.Cascade
open Function Filter Set Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer
open PertExtension Series Asymptotics
attribute [local instance] Gauge.frobInner
namespace Score.Stand
variable {V D:Type}{B:Set V} {S:Score D V}[Fintype D]
variable (T:S.Stand B)
-- input arranged by D too! tree limbs interpreted as unshifted.
def stepSet (o:Tile G D): Tile G D:= T.crustX ((T.splitSet o),fun i=>o i.val)
def wireHome (G:Gauge): ((T.Stable→G.El)×(T.Free→G.El)) ≃ₜ Tile G D where
    toFun p:= T.cite p.1 p.2
    invFun p:= (T.splitSet p,fun i=>p i.val)
    continuous_toFun := T.citeC
    continuous_invFun := (continuous_pi fun _=>continuous_apply _).prodMk (continuous_pi fun _=>continuous_apply _)
    left_inv := fun p=> Prod.ext (funext fun i=> T.keptZ p.1 p.2 i) (funext fun i=>T.kept p.1 p.2 i)
    right_inv u:= T.keepAll u
omit [Fintype D] in
@[simp] lemma flatStep : T.stepSet (G:=G) 1=1 := by
    change T.crust 1 1=1; rw [crust,setMove,T.dress1,T.sweep1,inv_one,S.dance]
def stepHome (G:Gauge): (Tile G D)≃ₜ(Tile G D):=(T.wireHome G).symm.trans T.crustX
omit [Fintype D] in
lemma step_here (x:Tile G D): (T.stepHome G) x = T.stepSet x:=rfl
lemma rhythmic : MeasurePreserving (T.stepHome G) (Gem G D) (Gem G D):=by
    let p:= T.wireHome G; let μ:= (Gem G T.Stable).prod (Gem G T.Free)
    have he : MeasurePreserving p μ (Gem G D):= T.citeHaar
    have hf : MeasurePreserving p.symm (Gem G D) μ:= ⟨p.symm.measurable,by rw [← he.map_eq, Measure.map_map p.symm.measurable p.measurable, show p.symm ∘ p=id from funext fun i=> p.symm_apply_apply i,Measure.map_id]⟩; exact (T.prod_stamp G).comp hf
lemma sweepRead (i: Keys G D)(p:V): ContDiffAt ℝ ω (fun x:Keys G D=> G.mat (T.setMove (T.splitSet (put x)) p)) i:=by
      refine (T.sweptLog (u:=fun x: Keys G D=> T.cite (T.splitSet (put x)) 1) (fun j=> ?_) p)
      unfold cite; split; exact paintD i _; exact contDiffAt_const
lemma logStep (i: Keys G D)(d:D): ContDiffAt ℝ ω (fun y: Keys G D=> G.mat (T.stepSet (put y) d)) i :=by
     let v := fun y: Keys G D=> T.setMove (T.splitSet (put y))
     let f := fun y:Keys G D=>T.cite 1 (fun i:T.Free=>put y i.val)
     change ContDiffAt ℝ ω (fun y=>G.mat (S.dress (v y)⁻¹ (f y) d)) _; simp only [dress,G.mat_mul, Pi.inv_apply,G.mat_inv]; let L: G.Mat ≃L[ℝ] G.Mat:= starL' ℝ
     have hu: ContDiffAt ℝ ω (fun y=> G.mat ((v y)⁻¹ (S.inn d))) i:= by simp only [Pi.inv_apply,G.mat_inv]; exact L.contDiff.contDiffAt.comp _ (T.sweepRead i _)
     simp only [star_star]; refine (hu.mul ?_).mul (T.sweepRead i _)
     unfold f cite; split; exact contDiffAt_const; exact paintD i _ -- direction
-- Arc from trunk branches variables all
def slotGram : Dimes G D D where
    q:= T.stepHome G
    acts := T.rhythmic
    clan := T.flatStep
    lifted :=by
        apply contDiffAt_pi.mpr; intro i; let f:= fun x:Keys G D=> G.mat ((T.stepHome G) (put x) i); have he:f 0=1:=by unfold f; rw [T.step_here,put_zero,T.flatStep];rfl
        exact ((show ContDiffAt ℝ ω G.plog (f 0) from he.symm ▸ G.plog_diff).comp 0 (T.logStep 0 i (G:=G))).of_le le_top
abbrev skews (G:Gauge): Dimes G D D:= slotGram T
-- retracts pointSet for analytic curves
nonrec def slab (G:Gauge): Keys G D→L[ℝ] Keys G T.Free := ContinuousLinearMap.pi fun i=> ContinuousLinearMap.proj i.val
omit [Fintype D] in
lemma plate0 (x:Keys G D): T.cite (T.splitSet (put x)) (put (T.slab G x))=put x:=T.keepAll (put x)
abbrev dtex (G:Gauge): Keys G D→L[ℝ] Keys G D:= fderiv ℝ (T.skews G).gradient 0
lemma trail : ∀ᶠ x:Keys G D in 𝓝 0, S.dress (T.setMove (T.splitSet (put x)))⁻¹ (put (T.rollX (T.slab G x)))=put ((T.skews G).gradient x):=by
     have h:= (show Tendsto (T.stepHome G ∘ put) (𝓝 0) (𝓝 1) from by simpa only [Function.comp_apply,put_zero,step_here,flatStep] using! ((T.stepHome G).continuous.comp putC).tendsto 0).eventually (sphere (G:=G))
     filter_upwards [(T.skews G).lead_grad,h] with x hx hu; change _= unput (T.stepSet (put x)) at hx; rw [hx]; rw [T.rollPut]; exact hu.symm
lemma pathZ (x: Keys G D): S.Track (fun t:ℝ=> T.rollX (t • T.slab G x)) (fun t=> (T.skews G).gradient (t•x)) (fun t=>(T.setMove (T.splitSet (put (t•x))))⁻¹):=by
    let f(t:ℝ):= t•x; let A:=T.skews G; have hf: ContDiff ℝ ω f := contDiff_id.smul contDiff_const
    have hv : f 0=0:= zero_smul ..; refine ⟨(LinearMap.toContinuousLinearMap T.rollX|>.contDiff.contDiffAt).comp (f:=fun t:ℝ=> t • T.slab G x) _ (contDiffAt_id.smul contDiffAt_const), (show ContDiffAt ℝ ∞ (A.gradient∘ f) 0 from (hv.symm ▸ A.gradC : ContDiffAt ℝ ∞ A.gradient (f 0)).comp _ (hf.of_le le_top).contDiffAt),by simp,by simp,?_,?_⟩
    · simp_rw [← map_smul (T.slab G)]; exact (show Tendsto f (𝓝 0) (𝓝 0) from hv ▸ hf.continuous.continuousAt.tendsto).eventually (p:=fun x=>S.dress (T.setMove (T.splitSet (put x)))⁻¹ (put (T.rollX (T.slab G x)))=put ((T.skews G).gradient x)) T.trail
    intro j; simp only [Pi.inv_apply,G.mat_inv]; exact ((starL' ℝ : G.Mat≃L[ℝ] G.Mat).contDiff.contDiffAt.comp _ ((T.sweepRead (f 0) j).comp 0 hf.contDiffAt)).of_le le_top
end Score.Stand
end YM.OPE.Cascade
