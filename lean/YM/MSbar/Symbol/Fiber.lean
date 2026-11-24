import YM.MSbar.Symbol.Average
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Local temperate extension uniform in fiber. For Laurent calculus, model on the entire open
ε disk at any given order. `AH` does not ignore punctures or mask. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Symbol
open Function Set Filter Metric Complex
open scoped Topology ContDiff BigOperators Classical

variable {E X Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

-- compositional laws for convenience
@[fun_prop] lemma tame_projL : (Prod.fst : X × Y→X).HasTemperateGrowth:=(ContinuousLinearMap.fst ℝ X Y).hasTemperateGrowth
@[fun_prop] lemma tame_projR : (Prod.snd : X × Y→Y).HasTemperateGrowth:=(ContinuousLinearMap.snd ℝ X Y).hasTemperateGrowth
@[fun_prop] lemma tame_pair {f : E→X} {g : E→Y} (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) :
   HasTemperateGrowth (fun x:E=>(f x,g x)) := by
    let i:= ContinuousLinearMap.inl ℝ X Y; let j:=ContinuousLinearMap.inr ℝ X Y
    have he:= (i.hasTemperateGrowth.comp hf).add (j.hasTemperateGrowth.comp hg)
    rw [show (fun x=>(f x,g x))= (i ∘ f)+(j ∘ g) from funext fun x=> by simp [i,j]]; exact he

abbrev Belongs (u : Set X) (f : X × Y → E) := ∀ x∈u,∃ g : X × Y → E,g.HasTemperateGrowth ∧ curry f =ᶠ[𝓝 x] curry g

structure AH (u : Set ℂ) (f : ℂ×X→ℂ) : Prop where
   uses : Belongs u f
   cr (z) (x : X) : z∈u → DifferentiableAt ℂ (fun w=> f (w,x)) z
variable {u U : Set ℂ} {x : X} {a z : ℂ} {f g : ℂ × X → ℂ} {h : ℂ → ℂ}
namespace AH
lemma upon (hf : AH U f) (he : u ⊆ U) : AH u f := ⟨fun x hx=> hf.uses x (he hx),fun z x hz => hf.cr z x (he hz)⟩
lemma locate (hf : ∀ z∈U,∃ A:Set ℂ,z∈A ∧ AH A f) : AH U f := ⟨fun z hz=>by obtain ⟨A,ha,h⟩:= hf z hz; exact h.uses z ha,fun z x hz=>by obtain ⟨A,ha,h⟩:=hf z hz; exact h.cr z x ha⟩
lemma occurrence (hf : AH U f) (he : ∀ z∈U,curry g =ᶠ[𝓝 z] curry f) : AH U g :=
  ⟨fun z hz => by obtain ⟨F,hF,h⟩:=hf.uses z hz; exact ⟨F,hF,(he z hz).trans h⟩,fun z x hz=> (hf.cr z x hz).congr_of_eventuallyEq ((he z hz).mono fun y hy=> congr_fun hy x)⟩
lemma congr (hu : IsOpen U) (hf : AH U f) (hg : ∀ z∈U,∀ x,f (z,x)=g (z,x)) : AH U g := hf.occurrence fun z hz=> (show ∀ᶠ w in 𝓝 z,w∈U from hu.mem_nhds hz).mono fun t ht=> Eq.symm (funext (hg t ht))
lemma slice (hf : AH U f) {z : ℂ} (hz : z∈U) : HasTemperateGrowth (fun x=>f (z,x)):=by
  obtain ⟨F,hF,h⟩:=hf.uses z hz; have H := h.eq_of_nhds
  change HasTemperateGrowth (curry f z); rw [H]; exact hF.comp (by fun_prop : HasTemperateGrowth (fun x:X=>(z,x)))
lemma smooth (hf : AH U f) (z : ℂ × X) (hz : z.1 ∈ U) : ContDiffAt ℝ ∞ f z:=by
  obtain ⟨F,hF,h⟩:=hf.uses z.1 hz
  exact hF.1.contDiffAt.congr_of_eventuallyEq ((continuousAt_fst.tendsto.eventually h).mono fun b hb=>congr_fun hb b.2)
lemma analytic (hf : AH U f) (hu : IsOpen U) (hz : z∈U) (x : X) : AnalyticAt ℂ (fun w=> f (w,x)) z:=
  DifferentiableOn.analyticAt (fun v hv=>(hf.cr v x hv).differentiableWithinAt) (hu.mem_nhds hz)
lemma cr_rule (h : AH U f) (hz : z∈U) (x : X) (a : ℂ) :
    fderiv ℝ f (z,x) (a,0)=a*fderiv ℝ f (z,x) (1,0):=by
    have hp : ∀ v:ℂ, fderiv ℝ f (z,x) (v,0)= (fderiv ℝ (fun y => f (y,x)) z) v := by
        obtain ⟨F,hF,hK⟩:=h.uses z hz; intro v
        have h1 : f =ᶠ[𝓝 (z,x)] F:= ((show Tendsto Prod.fst (𝓝 (z,x)) (𝓝 z) from continuousAt_fst.tendsto).eventually hK).mono fun x hx=>congr_fun hx x.2
        have h2 : (fun y : ℂ=> f (y,x))=ᶠ[𝓝 z] fun y => F (y,x):= hK.mono fun y hy=>congr_fun hy x
        rw [h1.fderiv_eq,h2.fderiv_eq,partialL_fderiv hF.1]; rfl
    simp_rw [hp]; rw [(h.cr z x hz).fderiv_restrictScalars ℝ]; simp

lemma param_tame {g : X → ℂ} (hg : g.HasTemperateGrowth) : AH U (fun p=>g p.2) :=
    ⟨fun _ _=>⟨_,hg.comp tame_projR,EventuallyEq.rfl⟩,fun _ x _=>differentiableAt_const (g x)⟩
lemma constant (c : ℂ) : AH U (fun (_ : ℂ×X)=>c):= param_tame (HasTemperateGrowth.const _)
lemma holomorphic (hu : IsOpen U) (h' : DifferentiableOn ℂ h U) : AH U (fun (x:ℂ×X)=> h x.1):=by
    have hd:= h'.analyticOnNhd hu; refine ⟨fun x hx=>?_,fun z y hz=> (hd z hz).differentiableAt⟩
    obtain ⟨r,hr,ht⟩:= Metric.mem_nhds_iff.mp (hu.mem_nhds hx)
    let c : ContDiffBump x:= ⟨r/4,r/2,by positivity,by linarith⟩
    have hp : HasTemperateGrowth (fun y=> c y • h y):=by
       refine (show HasCompactSupport (fun y=>c y • h y) from c.hasCompactSupport.smul_right).hasTemperateGrowth (contDiff_iff_contDiffAt.mpr fun y=> ?_)
       by_cases hY:y∈ ball x r
       · exact c.contDiff.contDiffAt.smul (((hd y (ht hY)).restrictScalars).contDiffAt)
       refine (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq ?_
       have hM:c.rOut<dist y x:= (half_lt_self hr).trans_le (le_of_not_gt hY)
       filter_upwards [(isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds (show y∈{b : ℂ| c.rOut < dist b x} from hM)] with t ht
       simp only [id_eq] at ht; rw [c.zero_of_le_dist ht.le,zero_smul]
    refine ⟨(fun p=>c p.1 • h p.1),hp.comp tame_projL,?_⟩
    filter_upwards [c.eventuallyEq_one] with t ht
    funext i; simp [ht]

lemma add (hf : AH U f)(hg : AH U g): AH U (f+g):=
    ⟨fun z hz=>by
       obtain ⟨a,ha,h⟩:=hf.uses z hz; obtain ⟨b,hb,h'⟩:=hg.uses z hz; exact ⟨a+b,ha.add hb,h.add h'⟩,
     fun z x hz=> (hf.cr z x hz).add (hg.cr z x hz)⟩
lemma neg (hf : AH U f): AH U (-f) :=
    ⟨fun z hz=>by obtain ⟨a,ha,h⟩:=hf.uses z hz; exact ⟨-a,ha.neg,h.neg⟩, fun z x hz=>(hf.cr z x hz).neg⟩
lemma sub (hf : AH U f)(hg : AH U g): AH U (f-g):= by rw [sub_eq_add_neg]; exact hf.add hg.neg
lemma mul (hf : AH U f)(hg : AH U g): AH U (f*g) :=
    ⟨fun z hz=>by obtain ⟨a,ha,h⟩:=hf.uses z hz; obtain ⟨b,hb,h'⟩:=hg.uses z hz; exact ⟨a*b,ha.mul hb,h.mul h'⟩,
    fun z x hz=> (hf.cr z x hz).mul (hg.cr z x hz)⟩
lemma sum {ι : Type*} {I : Finset ι} {F : ι → ℂ×X→ℂ} (he:∀ i∈ I,AH U (F i)) : AH U (∑ i∈I,F i):=by
   induction I using Finset.induction_on with
   | empty => simpa only [Finset.sum_empty] using! constant (X:=X) (U:=U) 0
   | insert i s h ih => rw [Finset.sum_insert h]; exact (he i (Finset.mem_insert_self ..)).add (ih fun j hj=> he _ (Finset.mem_insert_of_mem hj))

lemma arguments (hf : AH U f) {w : Y → X} (hw : w.HasTemperateGrowth) : AH U (fun p => f (p.1, w p.2)) := by
   refine ⟨fun z hz=>?_,fun z y hz=> hf.cr z (w y) hz⟩
   obtain ⟨a,ha,h⟩:= hf.uses z hz; refine ⟨(fun p => a (p.1,w p.2)), ha.comp (tame_pair tame_projL (hw.comp tame_projR)),h.mono (fun t ht=>funext fun b:Y=>congr_fun ht (w b))⟩
end AH
end YM.MSbar.Symbol
