import YM.OPE.Compatible.Anchor.Shift
/-! # Leading for any sponsored Lore.Fi -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Work.F08
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver FreeResolvent WithLp
open Drift Char Silt Silt.Float Module Page Planned.PrimaryIntegral295.Carrier
variable {i j d k m r l:ℕ}{Z I J M:Type}{n:Side}{K:Sponsor G}{T:Seasons K}{u:ℝ}{τ:Char.Phase→ℕ}
variable {e:RootEdge}
local notation "Y!" => Bid.Dir G n
local notation "B"=> Phone G
local notation "µ" => Tested.germ
variable (A:Alps K T i u)(x:Axis){a:RootEdge}
noncomputable def rootζ (A:Alps K T i u)(z:fieldX (Shade G))(x:RootEdge):G.Color:= toLp 2 fun i=> meetsX (barrage (pink K.K.penalty A.gear)) (shadew i z) (x.1,coord x.2)
lemma ζ_price (G:Gauge){I:Type}[Fintype I] (x:Libra.Keys G I)(t:I)(i:G.ColorIndex): ‖x t i‖≤‖x‖ := (PiLp.norm_apply_le (x t) i).trans (norm_le_pi_norm x t)
variable [Fintype I]
noncomputable abbrev fronds (f:I→RootEdge)(y:fieldX (Shade G)): Libra.Keys G I:=fun i=> toLp 2 fun j=> y ((f i).1,(f i).2,j)
noncomputable abbrev InkS (A:Alps K T i u)(a:RootEdge)(r:ℕ)(z:I→ RootEdge)(Y:Libra.Keys G I→ G.Color)(y:fieldX (Shade G)):ℝ:= ∑ i:G.ColorIndex, rootζ A y a i * jet ((Phone G).coord i ∘ Y) r (fronds z y)
-- uniform Φ.X.E s
omit [Fintype I] in lemma Side_top (Z:ℕ): ∀ᶠ i in (atTop:Filter Side), Z≤ i.val:= (viewUp Z).mono fun _ hx=>hx.le
omit [Fintype I] in lemma Val_t:Tendsto (fun n:Side=>n.val) atTop atTop:= tendsto_atTop.mpr Side_top
omit [Fintype I] in lemma Coy {w:fieldX (Shade G)}(_h:Quiet w m)(z:I→RootEdge) :
    Tendsto (fun n:Side=> dip z n 0 ((spool G n).symm (closeX w n))) atTop (𝓝 (fronds z w)):=by
       let g(n:Side):=(spool G n).symm (closeX w n); apply tendsto_pi_nhds.mpr; intro j
       have he:∀ᶠ n:Side in atTop, dip z n 0 (g n) j= fronds z w j:=by
            filter_upwards [eventually_unfold id Val_t (z j).1] with n hn; ext i; simp only [dip,ContinuousLinearMap.pi_apply,ContinuousLinearMap.proj_apply,sett,placed,zero_add]; let h:= z j; let x:Cover:=h.1; let a:=h.2; change spool G n (g n) (wrap n x,a,i)=w ((z j).1,a,i); rw [show spool _ _ _=closeX w n from (spool G n).apply_symm_apply (closeX w n)]; change w (lift _,_,i)= _; rw [show Lattice.lift (wrap n x)=x from hn]
       exact tendsto_const_nhds.congr' (he.mono fun i h=> h.symm)
lemma paints_lit {w:fieldX (Shade G)} (z:I→RootEdge)(Y:Libra.Keys G I→ G.Color)(h:Quiet w m)(hY:BudY e false r z Y)(hi:4 ≤ i):
    Tendsto (fun n:Side=> topψ (sett n 0 e) r (Dune A) (Y ∘ dip z n 0) ((spool G n).symm (closeX w n))) atTop (𝓝 (InkS A e r z Y w)):=by
       unfold topψ InkS; let Q(n:Side):Libra.Keys G (Body 1 n) := (spool G n).symm (closeX w n); have he:Realized id atTop w (fun i:Side=> spool G i (Q i)) m:=by unfold Q;simp only[ContinuousLinearEquiv.apply_symm_apply]; exact received Val_t h
       apply tendsto_finsetSum univ;intro i' _; let C: Libra.Keys G I→ℝ:= (Phone G).coord i' ∘ Y; let b:= jet C r; refine Tendsto.mul (f:=fun i=> bat _ _ (Q i)) (rootRead (e:=e) A hi w m h i' id Q he) ?_; refine Tendsto.congr ?_ ((Radial.Smooth.continuousJet C r|>.continuousAt|>.tendsto).comp (Coy h z)); intro n
       have hh: ContDiffAt ℝ ω C 0:= (((Phone G).coord i').toContinuousLinearMap.contDiff.contDiffAt.comp _ hY.sm); apply Eq.symm; exact congr_arg JetS.s (congr_fun (moldC (dip z n 0) C hh r) (Q n))
-- stencil rank.Aut independent
noncomputable abbrev SongY (A:Alps K T i u)(e:RootEdge)(r:ℕ)(z:I→RootEdge)(Y:Libra.Keys G I→G.Color): foliage G:= fun n v=> Cake (sett n v e) false (Dune A) (Rh A) (Y∘ dip z n v) r
variable (h:G.Simple) {z:I→RootEdge} {Y:Libra.Keys G I→ G.Color} (hp:BudY e false r z Y) {P:solar G d τ} (hv:Holds P (SongY A e r z Y))(hs:r+1≤d)
include hv hp h hs
lemma PegS : CapE (r+1) P:=by
     intro j hj; let q:= topX P j; refine Flume.Script.home (p:=q) (sootS ((resin (m:=0) P.val (fun _=>Nat.zero_le _) 0).2 j)) summable_zero (P.property.1 0 j) (fun _=>rfl) id Val_t ?_; filter_upwards [hv] with n hQ v; let x:= (spool G n).symm v; have he: Flume.Script.value 0 q (spool G n x)=0:= (Chip (V:=P) (e:=e) (n:=n) (p:=Y ∘ dip z n 0) (f:=Dune A) (g:=Rh A) (A:=SongY A e r z Y) rfl (congr_fun hQ _) (DuneAt A h).sm (hp.tilt_i n 0).smooth hs x).2 j hj; rw[show spool G n x=v from (spool G n).apply_symm_apply v] at he; exact he.trans (by simp [Flume.Script.value,scribe]) -- notation etc
lemma Fler (hi:4 ≤ i) {w:fieldX (Shade G)}(hW:Quiet w m)(ht:(r+1)*m ≤ τ 0): wholeX (topX P (r+1)) (fun _=>w)= InkS A e r z Y w:=by
     have hx:soot (τ 0) (topX P (r+1)) _:= (sproutV _ _ (P.val 0)).2 (r+1); have he:= paints_lit A z Y hW hp hi; refine tendsto_nhds_unique_of_eventuallyEq (keepX (r:=r+1) hx (x:=fun (n:Side) (_:Fin (r+1))=>closeX w n) (V:=id) (k:=fun _=>m) (fun _=>received Val_t hW) (by simpa using ht)) he ?_
     filter_upwards [hv] with n hn; let x:= (spool G n).symm (closeX w n); let q:=topX P (r+1); change Flume.Script.value 0 q (closeX w n)=topψ (sett n 0 e) _ _ _ x; rw [← show spool G n x=closeX w n from (spool G n).apply_symm_apply _]; exact (Chip (V:=P) (e:=e) (n:=n) (p:=Y ∘ dip z n 0) (f:=Dune A) (g:=Rh A) (A:=SongY A e r z Y) rfl (congr_fun hn _) (DuneAt A h).sm (hp.tilt_i n 0).smooth hs x).1
end YM.OPE.Variance
