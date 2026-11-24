import YM.OPE.Compatible.Parch.Furan
import YM.OPE.Compatible.Kash.Frieze
/-!
# Buoys. Lift of orientation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom
variable {i j d k m r l b:ℕ}{n:Side}
variable (hp:Board n (r+1))
-- glintX
lemma spinK (a:G.El) (x:Chamber G r): sailT G hp (glint _ a x)= glint _ a (sailT G hp x):=by
       funext i; obtain ⟨e,h⟩:=arkSur i; rw[←h]; by_cases ht:e∈fringe r n; swap
       · rw [silly G hp (glint _ a x) e ht]; change 0=G.adjoint a (sailT G hp x (arkE e)); rw [silly G hp x e ht,map_zero]
       obtain ⟨j,h'⟩:=from_port hp e ht; have he:arkE e=terr hp j:= h' ▸ rfl; rw [he,tide]; change G.adjoint a (x j)= G.adjoint a (sailT G hp x (terr hp j)); rw [tide]
variable (G)
lemma sailX (x:Chamber G r): ‖sailT G hp x‖ ≤ ‖x‖:=by refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i=>?_ ; obtain ⟨e,h'⟩:=arkSur i; rw[←h']; exact ebbNorm G hp x e
private lemma antQ {D:Type}(i j:D)(u:G.ColorIndex): An i (Phone G) u i=Phone G u ∧ (j≠i→ An i (Phone G) u j=0):=by unfold An; exact ⟨Pi.single_eq_same ..,fun h=> Pi.single_eq_of_ne h _⟩
lemma ferryT (j:↥(fieldP r))(i:G.ColorIndex) : sailT G hp (PickL G (j,i))=functorE 0 j.val i:=by
       have he:sett n 0 j.val=terr hp j:= ark_sett ..
       funext k; by_cases ht:k=terr hp j; · rw [ht,tide]; change PickL G (j,i) j = An _ (Phone G) i _; rw [he,(antQ G (terr hp j) k i).1]; exact (antQ G j j i).1
       unfold functorE; rw [he,(antQ G (terr hp j) k i).2 ht]; by_cases H: k∈ Set.range (terr hp); · obtain ⟨t,hs⟩:=H; rw[← hs,tide]; exact (antQ G j t i).2 (show t≠j from fun hq=>ht (hs ▸ hq ▸ rfl))
       obtain ⟨e,hq⟩:=arkSur k; rw[← hq]; apply silly G hp _ e; intro hz; obtain ⟨t,hB⟩:=from_port hp e hz; exact H ⟨t,(congr_arg arkE hB).trans hq⟩
variable {G}
lemma boomF {f g:Bid.Dir G n→ℝ} (L:Law (Chamber G r))(he:SiteL (sailT G hp) (chrom f) L)(hg:insured (tor n) f)(h:Once f g): OrientX (tor n) (chrom f) (sailT G hp) L :=by
       let H:=Culm (tor n) f 2 h.sm h.zero hg; exact ⟨he,fun v=> LinearMap.ext fun y=> jitter (tor n) f h.sm H v y,spinK hp, surgeon _ f h.sm H⟩
lemma AntiB {F:Finset (Edge Cover)}(hb: F⊆bark b)(hx:Board n b)(e:Edge Cover)(he:e∈bark b): Anti n e (fun i:↥F=>i.val):=by
       intro i x hh; apply berth_dir hx he (hb i.property); let k:= whiz (n:=n); have hv:k=(driftB n):=rfl
       have ht:(x+wrap n e.1,e.2)=(x+wrap n i.val.1,i.val.2):=(driftB n).injective hh; have ht':e.2=i.val.2:=(Prod.mk.inj ht).2; exact Prod.ext (add_left_cancel (Prod.mk.inj ht).1) ht'
lemma splay (f:Bid.Dir G n→ℝ)(x:Bid.Dir G n)(e:↥(fieldP r))(i:G.ColorIndex)(ht:ContDiffAt ℝ ω f 0): bat (functorE 0 e.val i) (jet f 2) x=chrom f (sailT G hp (PickL G (e,i))) x:=by
       let y:=functorE (0:Site n) e.val i; rw [ferryT, Merchant.podium]; change fderiv ℝ (Tensor.diagonal (Tensor.coeff f 2 0)) x y=_; rw[Tensor.differential_diagonal _ (Tensor.coeff_symm (ht.of_le le_top)), Tensor.coeff]; simp only[ContinuousMultilinearMap.curryLeft_apply,_root_.smul_apply]; rw[show Fin.cons y (fun _:Fin 1=>x)=![y,x] from funext fun i=>by fin_cases i <;> rfl,← Nat.cast_smul_eq_nsmul ℝ,smul_smul]; norm_num [Nat.factorial]; ring -- maybe norm_num
lemma lightQ (f g:Bid.Dir G n→ℝ)(x:Bid.Dir G n)(p: Body 1 n)(Y:Bid.Dir G n→ G.Color) (r:ℕ)(hp:ContDiffAt ℝ ω f 0)(ht:ContDiffAt ℝ ω Y 0): Claw.rank (fun y=>(Cake p false f g Y r y).s) (r+1) x= topψ p r f Y x:=by
       let V:= fun y=>(Cake p false f g Y r y).s; have hv:Bond V:= (CakeB p false f g Y r) 0; have hh(x:ℝ):ContDiff ℝ ω (fun i:ℝ=>i^r • x):= by fun_prop
       unfold Claw.rank; rw [← WardBin.leading_tensor _ _ (hv.smooth.contDiffAt.of_le le_top)]
       let z(t:ℝ):= t^(r+1) • topψ p r f Y x; let u(t:ℝ):= t^(r-1) • botψ p r Y x; have he:(fun t:ℝ=> V (t • x))=z+u:=funext fun i=> speedCake p f g x Y r i hp ht
       change WardBin.leading (r+1) (fun t:ℝ=> V (t • x))=_; rw [he,show WardBin.leading (r+1) (z+u)=WardBin.leading (r+1) z+WardBin.leading (r+1) u from ?_,show WardBin.leading (r+1) z= _ from (WardBin.lead_monomial (r+1) (r+1) (topψ p r f Y x)).trans (if_pos rfl),show WardBin.leading (r+1) u=0 from (WardBin.lead_monomial (r+1) (r-1) (botψ _ _ _ _)).trans (if_neg (by omega)),add_zero]; unfold WardBin.leading; rw [iteratedDeriv_add,smul_add]; all_goals first| (unfold z; fun_prop) | (unfold u;fun_prop) -- tweak
end YM.OPE.Merchant
