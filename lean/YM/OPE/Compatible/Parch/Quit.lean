import YM.OPE.Compatible.Parch.Rook
/-!
# Auth.Surface β_ext lifts into Toll.Space. Conditional currencies.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw
variable {i j d k m r l b:ℕ}{n:Side}{S:Finset Cover}{o:Cover}
namespace Prom
variable (P:Prom S o m) (b:ℕ)
variable (hp:S⊆Lattice.box b)(hb:Board n b)
local notation "W'"=>Tray G S
local notation "Q"=> Bid.Dir G n
set_option quotPrecheck false
local notation "V"=>BlurD G (crossV S) n
-- leading Real Case drives ext and vector
variable (g:Bid.Dir G n→ℝ)
variable (hA:g=Claw.rank g r) (hz:Crisp (crossV S) g)(hv:∀ i:Bid.Dir G n,∀ v:Site n→ G.Color,g (i+gillS (tor n) v)=g i)
local notation "Y!"=>P.Oasis b hp hb g
include hA hz hv
lemma rise : jet (Oasis P b hp hb g∘ BlurD G (crossV S) n) r=g:=by
       let W:=Oasis P b hp hb g∘ BlurD G (crossV S) n; have he: ContDiff ℝ ω W:= (schoolC P b hp hb g ((Tall.tag le_rfl hA).neat)).comp (BlurD G (crossV S) n).contDiff; funext x; change Tensor.diagonal (Tensor.coeff W r 0) x=g x; rw[← WardBin.leading_tensor x W (he.of_le le_top|>.contDiffAt)]; exact WardBin.leading_of_lim ((he.of_le le_top|>.contDiffAt).comp (f:=fun t:ℝ=>t • x) _ (by fun_prop)) (g x) (OasisT P b hp hb g hA hz hv x) -- limit
lemma roseD: Hush (P.Oasis b hp hb g) r:=by
       let B:=dressQ b hp hb (G:=G); let Q₁:=P.Oasis b hp hb g; have ht:ContDiff ℝ ω Q₁:=schoolC P b hp hb g (Tall.tag le_rfl hA).neat
       intro x k hk; have hz(t:ℝ): BlurD G _ n (t • (B x))=t • x:= by rw[map_smul,show BlurD G (crossV S) n (B x)=x from readU G _ (cross_mono hp) hb x];
       change Tensor.diagonal (Tensor.coeff Q₁ k 0) x= _; rw [← WardBin.leading_tensor x Q₁ (ht.of_le le_top|>.contDiffAt)]; apply WardBin.leading_of_lim ((show ContDiff ℝ _ _ from ht).contDiffAt.of_le le_top|>.comp (f:=fun t:ℝ=>t • x) 0 (by fun_prop)); apply Tendsto.congr (fun a=>?_) (WardBin.falls (f:=fun t:ℝ=>Oasis P b hp hb g (BlurD G _ n (t • (B x)))) hk (OasisT P b hp hb g hA (show Crisp _ _ from by assumption) hv (B x))) -- hz shadow
       rw [hz]; rfl
-- compile scalar quanta ρ script.Values exactly. Mark when support external.
lemma Φ_read (he:∀ a i,g (glint _ a i)=g i) : let W:=Oasis P b hp hb g∘BlurD G (crossV S) n; let M:= Pawn.mold W r; (tor n).Marbles M∧(fun i=>(M i).s)=g ∧∀ q:Phase,Crisp (crossV S) (fun i=>(M i).seq q.val) ∧ Tall (fun i=>(M i).seq q.val) (r+q.val):=by
       intro W M; have hp': ContDiffAt ℝ ω (Y!) 0:= (P.schoolC b hp hb _ (Tall.tag le_rfl hA).neat).contDiffAt
       let v:=BlurD G (crossV S) n; have hh:ContDiffAt ℝ ω W 0:= (show ContDiffAt ℝ ω (Y!) (v 0) from v.map_zero.symm ▸ hp').comp (f:=v) _ v.contDiff.contDiffAt
       have ht(x): M x=Pawn.mold (Y!) r (v x):= congr_fun (moldC (BlurD G _ n) (Y!) hp' r) x
       have hS: Hush W r:=by intro x k hk; have h:=roseD P b hp hb g hA hz hv (BlurD G (crossV S) n x) k hk; exact (congr_arg JetS.s (congr_fun (moldC (BlurD _ _ _) (Y!) hp' k) x)).trans h
       refine ⟨Claw.tenure _ W r hh hS (P.rankPure b hp hb g n 0 he), P.rise b hp hb g hA hz hv,fun q=>⟨⟨fun i j he=>?_⟩,?_⟩⟩
       · rw [ht,ht,show v i=v j from he]
       fin_cases q <;> exact Tall.loan (Tensor.coeff W _ 0) le_rfl
-- Aura
omit hA hz hv
section
variable (p:Bid.Dir G n→G.Color)(e:RootEdge)(he:e.1=o)(h:p=Claw.rank p r)(hy:∀ x:Bid.Dir G n,∀ v:Site n→ G.Color,p (x+gillS (tor n) v)=p x)(hs:Crisp (crossV S) p)
include h hy hs
lemma marks_j (j:G.ColorIndex): let f:=(Phone G).coord j∘p; f=Claw.rank f r ∧ Crisp (crossV S) f∧∀ x:Bid.Dir G n,∀ v:Site n→G.Color,f (x+gillS (tor n) v)=f x:=by
       intro f; refine ⟨?_,⟨fun i j hj=>congrArg ((Phone G).coord _) (hs.jury _ _ hj)⟩,fun i v=>congrArg ((Phone G).coord _) (hy _ _)⟩
       apply Eq.symm (Tall.pint (((Phone G).coord j).toContinuousLinearMap.contDiff.comp (Tall.tag le_rfl h).neat) ?_)
       intro x t; rw [Function.comp_apply,show p _= _ from (show p (t • x)=t^r • p x from (congr_fun h _).trans ((Tensor.homogeneous ..).trans (congr_arg _ (congr_fun h x).symm))),map_smul];rfl
lemma mapQ (u:G.ColorIndex):jet ((Phone G).coord u ∘ (P.Oasis b hp hb p∘ BlurD G (crossV S) n)) r=(Phone G).coord u∘ p:= P.rise b hp hb ((Phone G).coord u ∘ p) (marks_j p h hy hs u).1 (marks_j p h hy hs u).2.1 (marks_j p h hy hs u).2.2
include he
lemma variant (hΞ:∀ g i,p (glint _ g i)=G.adjoint g (p i)):BudY e false r (fun i:↥(crossV S)=>i.val) (P.Oasis b hp hb p):=by
        let u:=P.Oasis b hp hb p; have ht:ContDiff ℝ ω u:= P.schoolC b hp hb p (Tall.tag le_rfl h).neat; refine ⟨ht.contDiffAt,fun j x=>⟨(ht.comp (dip (G:=G) (fun i:↥(crossV S)=>i.val) j x).contDiff).contDiffAt,fun i=>?_⟩,fun j x=>P.boardS b hp hb p j x e he hΞ⟩
        let D:=(Phone G).coord i; let Hr:=dip (fun i:↥(crossV S)=>i.val) j x (G:=G); obtain ⟨hz,hx,hE⟩:= marks_j p h hy hs i; have hv:Hush (D ∘ u) r:=P.roseD b hp hb _ hz hx hE
        intro v k hk; have he:ContDiffAt ℝ ω (D∘u) 0:= (D.toContinuousLinearMap.contDiff.comp ht|>.contDiffAt); exact (congr_arg JetS.s (congr_fun (moldC Hr (D∘u) he k) v)).trans (hv (Hr v) k hk)
end
end Prom
end YM.OPE.Merchant
