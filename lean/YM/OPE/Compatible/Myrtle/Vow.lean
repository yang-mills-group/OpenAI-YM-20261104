import YM.OPE.Compatible.Myrtle.Table
/-! # Mark runtime ages.Halo under ticket. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Raucous.Host
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge Tree Push Push.AbsoluteSums Precision Matrix Exterior
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra GaussianScore Metric Limn Cinders
variable {G:Gauge}{c f:Side}{I:Type*}
attribute [local instance] Gauge.frobInner
open Radial Flume.Virgin
open PhysicalNext.Repeat.Aroma
open YM.AnalyticNext.QuarticMatch Radius Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom Estimate Sheets Radius.Model
open Woody Next.Free Finset Work.F03 Progress.StationaryScenes AnalyticNext.QuarticMatch.Local Cascade Rill Glass Coin Votive Stationary
variable {i m j:ℕ} {s t r R e d b b' v u z x a C:ℝ}
open Zeph Dew
variable {K:Sponsor G}{T:Seasons K}
variable {N:ChartRatio G} (hN: LocalRatio N) (H:StackP N r R t)
namespace Studio
variable {L:Host K T}(Y:Studio L)
noncomputable abbrev omS (ε B r:ℝ):= Prism L.Z L.H L.A L.U L.k L.F Y.X Y.w Y.ext ε B r
noncomputable abbrev will(N:ChartRatio G)(ε:ℝ):= Dress L.Z L.H L.A L.U L.k L.F L.P Y.X Y.w Y.ext N ε
noncomputable abbrev join (p:ℝ):= ‖Y.w‖+(‖Y.ext‖+p)
include H
lemma valley (hr:0<e)(hx:0<x)(hd:x/2 ≤ r)(p:Y.St)(hk:p∈omS Y e x r):
         0 ≤ Y.join (2*x/e) ∧ ‖Y.boat p‖≤ Y.join (2*x/e)∧ ‖Y.V (Y.boat p)‖≤ Y.join (2*x/e):=by
           have hp:= (era (F:=(Y.X:Type)) H.sweep hr hx hd).2 (show (Y.boat p) ∈ CapeQ G (Y.X:Type) x e r from hk); rw[mem_closedBall,dist_zero_right] at hp; have hy:Y.Vx (Y.boat p)≤ Y.join (2*x/e):= add_le_add le_rfl (add_le_add le_rfl hp); have hq:=Y.plume (Y.boat p); exact ⟨(norm_nonneg _).trans (hq.1.trans hy),hq.1.trans hy,hq.2.trans hy⟩
lemma keptV (v:ℝ)(hv:0<e)(hx:0<x)(hd:x/2 ≤ r)(hp: v+‖Y.centerA‖<x/(2*e)): closedBall (0:Y.St) v ⊆ omS Y e x r:=by
         intro i hi; have he: Y.boat i∈ ball (0:Y.St) (x/(2*e)):=by rw[mem_ball,dist_zero_right]; rw[mem_closedBall,dist_zero_right] at hi; exact ((norm_add_le i Y.centerA).trans (add_le_add_left hi _)).trans_lt hp
         change Y.boat i ∈ CapeQ G (Y.X:Type) x e r; exact (era H.sweep hv hx hd).1 he
end Studio
variable {L:I→ Host K T}{Y:∀ i, Studio (L i)}{l:Filter I}{V ε B A T' :I→ℝ}
structure Bevel (Y:∀ i,Studio (L i))(l:Filter I)(V ε B :I→ℝ)(r a:ℝ):Prop where
       presents : ∀ᶠ i in l,0<ε i ∧ 0 < B i ∧ B i/2 ≤ r
       beats : a<0
       pays : RateLE l V ε a
       skies : RateLE l V (fun i=> B i/ε i) 0
       cream : ∀ q:ℝ,0 ≤ q→ ∀ᶠ i in l, crestPrice G (q*V i)+‖(Y i).centerA‖ < B i/(2*ε i)
       reads : ∀ᶠ i in l,(L i).P.beta=(ε i)⁻¹^ (2:ℕ)
variable (h:Craft Y l V A s b e u C)
namespace Craft
variable (hx:Bevel Y l V ε B r a)
set_option quotPrecheck false
local notation "O!"=> fun i=>(Y i).omS (ε i) (B i) r
local notation "μ"=> fun i=>(Y i).μφ
include h H hx
lemma failed (t':ℝ): RateLE l V (fun i=>(Y i).μφ.real ((Y i).omS (ε i) (B i) r)ᶜ) t':=by
           let v:= ‖t'‖; let t:= fun i=> Real.exp (-(v*V i)); have ht: RateLE l V t t':=by
                 intro x he; filter_upwards [h.light.eventually_ge_atTop 0] with i hi; rw [Real.norm_of_nonneg (Real.exp_nonneg _)]; rw[← neg_mul]; exact Real.exp_monotone (mul_le_mul_of_nonneg_right ((neg_le.mp ((le_abs_self (-t')).trans_eq (abs_neg _))).trans he.le) hi)
           apply RateLE.of_norm_le (((h.IP.mul (RateLE.const (Fintype.card G.ColorIndex:ℝ) h.light)).mul ((RateLE.const (2*Real.exp (C/2)) h.light).mul ht)).mono (by simp))
           filter_upwards [hx.cream v (norm_nonneg _), hx.presents,h.enters,h.light.eventually_ge_atTop 0] with i hi hp hk hv; obtain ⟨hr,hv',hb⟩:= hp; rw [Real.norm_of_nonneg measureReal_nonneg]; refine (measureReal_mono (Set.compl_subset_compl.mpr ((Y i).keptV H _ hr hv' hb hi))).trans ?_ -- notation?
           have hg : (closedBall (0:(Y i).St) (crestPrice G (v * V i)))ᶜ={x:(Y i).St| crestPrice G (v*V i)< ‖x‖}:=by ext x; rw [mem_compl_iff,mem_closedBall,dist_zero_right,not_le]; rfl
           rw [hg]; exact hk.1.DustK h.served.1 h.served.2.1 h.served.2.2 (Y i).X _ (mul_nonneg (norm_nonneg _) hv)
omit H
include h hx
abbrev ν (Y:∀ i,Studio (L i))(ε B:I→ℝ)(i:I):= (Y i).join (2*B i/ε i)
lemma costsν: RateLE l V (ν Y ε B) 0:=by
        refine RateLE.congr (h.Wax.add (h.axe.add (((RateLE.const (2:ℝ) h.light).mul hx.skies).mono (by norm_num)) h.light) h.light) ?_; filter_upwards with i; unfold ν Studio.join; ring
end Craft
end YM.OPE.Raucous.Host
