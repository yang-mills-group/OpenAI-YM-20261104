import YM.OPE.Compatible.Glim.Milo
/-! # Local H registration.Stamp.Powers -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Work.F08
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Page Planned.PrimaryIntegral295.Carrier
variable {i j d k m r l:ℕ}{Z I J:Type}{n:Side}
variable (e:RootEdge)(u:G.ColorIndex)
lemma viewUp (i:ℕ):∀ᶠ n:Side in atTop, i < n.val:=by let x:Side:=⟨i+1,Nat.zero_lt_succ _⟩; exact (eventually_ge_atTop x).mono fun i h=>h
lemma Hood (p:RootEdge): ∀ᶠ n:Side in atTop,∀ x:Site n,sett n x p=sett n x e → p=e:=by
    filter_upwards [viewUp (size (p.1-e.1))] with i hi x hx; have hv:= (show placed i x p=placed i x e from (driftB i).injective hx); have hp: wrap i p.1=wrap i e.1:= add_left_cancel (congr_arg Prod.fst hv); apply Prod.ext _ (show p.2=e.2 from congr_arg (fun z:edgeV i=>z.2) hv); by_contra ht; exact (winds_size (m:=i) _ (by rw [map_sub,hp,sub_self]) (sub_ne_zero.mpr ht)).not_gt hi
variable [Fintype I]
lemma hump (p:I→RootEdge):∃ t: Libra.Keys G I, ∀ᶠ n:Side in atTop,∀ x:Site n, dip p n x (functorE x e u)=t:=by
     refine ⟨fun i=>if p i=e then Phone G u else 0,?_⟩; filter_upwards [eventually_all.mpr (fun i=> Hood e (p i))] with n hn x; funext j; unfold dip; simp only[ContinuousLinearMap.pi_apply,ContinuousLinearMap.proj_apply]; split; next h=> rw [h]; simp [functorE,An];
     next h=> have hg : sett _ x (p j) ≠ sett n x e:=fun hx=>h (hn j x hx); simp [functorE,An,hg]
lemma TakesY (p:I→RootEdge)(F: Libra.Keys G I→ℝ)(hp:ContDiffAt ℝ ω F 0)(l:ℕ):
     Take (Z:=Z) 1 (fun _ n x v=> fderiv ℝ (jet (F∘ dip p n x) l) v (functorE x e u)) l m:=by
        cases l with
        | zero=> refine Take.congr (Take.zero (G:=G) 1) (fun i=>?_); filter_upwards with n; funext x y;rw [show jet (F∘ dip p _ x) 0= _ from (show jet (F∘ dip p _ x) 0=fun _=> (F∘dip p _ x) 0 from funext fun i=> jet_zero ..), fderiv_const_apply];rfl
        | succ i=>
            obtain ⟨t,ht⟩:= hump e u p; refine ((monaJet (bat t F) p (picked _ hp _) i m).raise le_rfl (Nat.le_succ _)).congr ?_; intro w; filter_upwards [ht] with n hn; funext x v; let V:=dip p n x (G:=G); have he:V 0=0:=map_zero _; have hg: ContDiffAt ℝ ω (F ∘ V) 0:= (he.symm ▸ hp : ContDiffAt ℝ ω F _).comp _ V.contDiff.contDiffAt; have hv:bat (functorE x e u) (F ∘ V)=ᶠ[𝓝 0] bat t F∘V:=by
                    filter_upwards [(he ▸ V.continuous.continuousAt.tendsto: Tendsto V (𝓝 0) (𝓝 0)).eventually (hp.eventually (by simp))] with y hT; unfold bat; rw [fderiv_comp y (hT.differentiableAt (by simp)) V.differentiableAt,V.fderiv,ContinuousLinearMap.comp_apply,show V (functorE x e u)=t from hn x];rfl
            change _ = fderiv ℝ (jet (F ∘ V) _) _ _; rw [vast _ i hg]; exact congr_arg JetS.s (congr_fun (meltSame _ _ hv.symm i) v)
end YM.OPE.Variance
