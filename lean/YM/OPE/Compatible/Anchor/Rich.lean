import YM.OPE.Compatible.Anchor.Sect
/-! # instruments rotate.Anchor leg null lifts. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Labels
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Work.F08 Maxwell
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver FreeResolvent WithLp
open Drift Char Silt Silt.Float Module Page Planned.PrimaryIntegral295.Carrier
variable {i j d k m r n l:ℕ}{Z I J M E F:Type}
noncomputable abbrev HornIdx (k:ℕ):= Axis×(Fin k→Axis)
abbrev BoxC (G:Gauge)(k:ℕ):= HornIdx k→ G.Color
noncomputable abbrev bets (G:Gauge)(k:ℕ) : Taylor G (k+1) →ₗ[ℝ] BoxC G k where
     toFun x i:= flame x i.1 (basis ∘ i.2)
     map_add' p q:=by funext x; ext i; exact congr_fun (map_add (pierce G k) p q) (x,i)
     map_smul' c p:=by funext x; ext i; exact congr_fun (map_smul (pierce G k) c p) (x,i)
lemma betaRank : LinearMap.ker (bets G k)= LinearMap.range gaugeJet:=by
     rw [← fangRank]; ext i; constructor; intro h; change _= _;funext x; exact congr_arg (fun y:BoxC G k=>y x.1 x.2) (show bets G k i=0 from h); intro h; change _=_; ext1 p; ext1 j; exact congr_fun (show pierce G k i=0 from h) (p,j)
def Ahorn (s:G.El) : BoxC G k→ₗ[ℝ] BoxC G k:= LinearMap.pi fun i=>G.adjoint s ∘ₗ LinearMap.proj i
lemma μDrive (i:Taylor G l)(s:G.El)(a b:Axis)(u:Fin l→ E4): takeCurl (Taylor.paint s i) a b u= G.adjoint s (takeCurl i a b u):=by unfold takeCurl; simp only[_root_.smul_apply,_root_.sub_apply,ContinuousMultilinearMap.curryLeft_apply,map_smul,map_sub]; rfl
lemma μAxis (i:Taylor G (k+1))(s:G.El): bets G k (Taylor.paint s i)= Ahorn s (bets G k i):=by
    funext x; change flame (Taylor.paint _ _) _ _ = G.adjoint _ (flame _ _ _); unfold flame; rw[_root_.sum_apply,_root_.sum_apply,map_sum]; apply sum_congr rfl; intro i _; exact μDrive .. -- direction
lemma TPaint (i:Taylor G k)(s t:G.El): Taylor.paint (s*t) i=Taylor.paint s (Taylor.paint t i):=Subtype.ext (funext fun a=>ContinuousMultilinearMap.ext fun v=> G.adjoint_mul s t (i.val a v))
lemma TBill (p:Taylor G k): Taylor.paint 1 p=p:=Subtype.ext (funext fun a=>ContinuousMultilinearMap.ext fun v=> G.adjoint_one (p.val a v))
lemma sweet_t : Continuous (fun x:G.El × Taylor G k=> Taylor.paint x.1 x.2) :=by
    obtain ⟨s,v,h⟩:= projectionExists (templateX G k) realmBase; let T(p:Taylor G k)(i:↥s):ℝ:= ledge p.val i.val; let L:(↥s→ℝ)→L[ℝ] Taylor G k:= v.toContinuousLinearMap; let A:= fun x:G.El × Taylor G k=> Taylor.paint x.1 x.2; have ht: A= L ∘ (fun i=>T (A i)):=funext (fun x=>(decisions (A x)).symm.trans (h _)); change Continuous A; nth_rw 1 [ht]; apply L.continuous.comp; apply continuous_pi; intro i
    let g : Taylor G k→ₗ[ℝ] G.Color := { toFun p:= toLp 2 fun j=> ledge p.val (i.val.1,i.val.2.1,j), map_add' _ _:=rfl,map_smul' _ _:=rfl }; have hv (x:G.El × Taylor G k):T (A x) i = G.adjoint x.1 (g x.2) i.val.2.2:=rfl; simp_rw [hv]; apply (EuclideanSpace.proj i.val.2.2).continuous.comp ( (adContour G).comp (continuous_fst.prodMk (g.continuous_of_finiteDimensional.comp continuous_snd)))
end YM.OPE.Variance
