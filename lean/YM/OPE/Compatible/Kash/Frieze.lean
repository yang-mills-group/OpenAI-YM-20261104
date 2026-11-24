import YM.OPE.Compatible.Kash.Tea
import YM.OPE.Compatible.Kash.Trill
import YM.OPE.Compatible.Kash.Lease
import YM.OPE.Compatible.Kash.Sump
import YM.OPE.Compatible.Glim.Xpand
/-! # Uniform supplies of finite-angular scripts. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Page
variable {i j d k m r l:ℕ}{Z I J:Type}
variable {n:Side}{x t:ℝ}
local notation "C!"=> Curtain (Shade G)
local notation "Φ" n:arg=>Bid.Dir G n
section
variable {v c:Side}(h:c.val ∣ n.val)(e:RootEdge)(u:G.ColorIndex)(X:Bid.Dir G c)(x:Site n)
local notation "θ"=> trimT n c h
local notation "W"=> Booklet h G
local notation "ξ"=> trimT n c h x
private lemma helm (k:ℕ)(p:Script (Shade G) (k+1))(f:(n:Side)→ Bid.Dir G n→ℝ)(hp:Summable p)(he:∀ n,ContDiffAt ℝ ω (f n) 0)(hv:∀ n (q:Fin (k+1)→ Bid.Dir G n), library n p (spool G n∘q)=iteratedFDeriv ℝ (k+1) (f n) 0 q) : fderiv ℝ (jet (f n) (k+1)) (W X) (functorE x e u) = fderiv ℝ (jet (f c) (k+1)) X (functorE (θ x) e u):=by simp_rw [Need e u p hp (f _) (he _) (hv _),Food]
variable {K:Sponsor G}{T:Seasons K}(A:Alps K T i t)
lemma heave (r:ℕ): Pry (functorE x e u) (Pawn.mold (Dune A) (r+1)) (W X)=Pry (functorE (θ x) e u) (Pawn.mold (Dune A) (r+1)) X:=by
        have hx(r:ℕ):= helm h e u X x r (A.word (r+1)) (fun _=> Dune A) (by obtain ⟨c,hc,H⟩:= Alps.word_cost K T i (r+1) 0 A.clip; exact sootS (H _ A rfl)) (fun n=> ((A.fullK (r+1)).plot n|>.sub contDiffAt_const)) (fun n v=> by unfold Dune; rw [iteratedFDeriv_sub_apply (((A.fullK (r+1)).plot n).of_le le_top) contDiffAt_const,iteratedFDeriv_const_of_ne (by omega),Pi.zero_apply,sub_zero]; exact ((A.fullK (r+1)).wink n _ le_rfl v))
        exact JetS.eta _ _ (hx r) (hx (r+1)) (hx (r+2))
lemma slotsV (hv:0≤t):Pry (functorE x e u) (Pawn.mold (Rh A) 0) (W X)=Pry (functorE (θ x) e u) (Pawn.mold (Rh A) 0) X:=by
        have hx(r:ℕ):= helm h e u X x r (A.liftZ (r+1)) (fun _=> Rh A) (by obtain ⟨c,hc,H⟩:= Alps.leaf_cash K T i (r+1) 0; exact sootS (H _ hv A)) (fun n=> ((A.fullL (r+1)).plot n)) (fun n v=> (A.fullL (r+1)).wink n _ le_rfl v)
        refine JetS.eta _ _ ?_ (hx 0) (hx 1); change fderiv ℝ (jet (Rh A) 0) _ _= fderiv ℝ (jet (Rh A) 0) _ _; have he(i:Side): jet (Rh A (n:=i)) 0=fun _=>Rh A (0:Bid.Dir G i):=funext fun i=>jet_zero ..; rw [he,he,fderiv_const_apply,fderiv_const_apply];rfl
lemma root_trim :pushB h (sett n x e)=sett c (θ x) e:= Prod.ext ((map_add (θ) _ _).trans (congr_arg _ (lease h e.1))) rfl
variable (p:I→RootEdge)(k:ℕ)
lemma copK : dip p n x (W X)=dip p c (θ x) X:=by funext i; exact congr_fun (congr_arg (fun y: Body 1 c => fun z : Unit=> X y) (root_trim h _ _)) ()
variable [Fintype I]
lemma mouldYield (f:Libra.Keys G I→ℝ)(hp:ContDiffAt ℝ ω f 0): Pawn.mold (f∘dip p n x) k (W X)=Pawn.mold (f∘dip p c (θ x)) k X:=by rw [moldC _ _ hp,moldC _ _ hp]; dsimp only [Function.comp_apply]; rw [copK]
omit [Fintype I] in
lemma mountYield (a:G.Color)(b:Bool): Mount (sett n x e) a b u (W X)=Mount (sett c (θ x) e) a b u X:=by
         let Q(_:Unit):= e; let L:Libra.Keys G Unit→L[ℝ] G.Color:= ContinuousLinearMap.proj (); let f: Libra.Keys G Unit→ℝ:= (Phone G).coord u ∘ Cast b a ∘ L; have hX: ContDiffAt ℝ ω f 0:= ((Phone G).coord u).toContinuousLinearMap.contDiff.contDiffAt.comp 0 ((show ContDiffAt ℝ ω (Cast b a) (L 0) from L.map_zero.symm ▸ cast_sm b a).comp _ L.contDiff.contDiffAt); exact mouldYield h X x Q 0 f hX
-- Alias at the actual registration.Cope
def Anti (c:Side)(e:RootEdge)(p:I→RootEdge):Prop:=∀ i x,sett c x e=sett c x (p i)→ e=p i
omit [Fintype I] in
lemma Needle (H: Anti c e p): dip p n x (functorE x e u)=dip p c (θ x) (functorE (θ x) e u):=by
        funext i; rw [ContinuousLinearMap.pi_apply,ContinuousLinearMap.pi_apply]; by_cases hv:e=p i
        · rw [hv,ContinuousLinearMap.proj_apply,ContinuousLinearMap.proj_apply]; simp [functorE,An]
        have he: sett c (θ x) (p i) ≠ sett c (θ x) e := fun h=>hv (H i (θ x) h.symm); change ((functorE x e u) (sett n x (p i)))= (functorE (θ x) e u) (sett c (θ x) (p i)); have ht: sett n x (p i)≠ sett n x e:= fun hp=>he ((root_trim h _ x).symm.trans ((congr_arg (pushB h) hp).trans (root_trim ..))); simp [functorE,An,he,ht]
lemma PayMask (f:Libra.Keys G I→ℝ)(hp:ContDiffAt ℝ ω f 0)(he:Anti c e p): Pry (functorE x e u) (Pawn.mold (f∘dip p n x) k) (W X)=Pry (functorE (θ x) e u) (Pawn.mold (f∘dip p c (θ x)) k) X:=by
         have ht(j:ℕ):fderiv ℝ (jet (f∘dip p n x) j) (W X) (functorE x e u)= fderiv ℝ (jet (f∘dip p c (θ x)) j) X (functorE (θ x) e u):=by
                    let F:=Tensor.coeff f j 0; have hF:= (Tensor.diag_smooth F ω).differentiable (by simp)
                    rw [ΔJet f hp, ΔJet f hp, fderiv_comp (W X) (hF _) (dip p _ _|>.differentiableAt), fderiv_comp X (hF _) (dip p _ _|>.differentiableAt),(dip p _ _|>.fderiv), (dip p _ _|>.fderiv),ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,copK,Needle h _ u _ p he]
         exact JetS.eta _ _ (ht k) (ht _) (ht _)
end
end YM.OPE.Variance
