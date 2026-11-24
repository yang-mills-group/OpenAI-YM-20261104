import YM.OPE.Compatible.Myrtle.Vow
/-! # enact income quantum -/
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
variable {L:Host K T} {Y:Studio L} {y:Y.St}
noncomputable abbrev PayT(Y:Studio L)(s b b' t B:ℝ):= ‖Y.heel s b b' t B‖ + ‖labor L.Z L.ForestQ Y.X s b b' t Y.Y B‖
variable {w:ℝ}
variable (hr:L.Rich s b e b' u C)(h':0< s)(hb:0 ≤ b)(he:0<e)(hb':0 ≤ b') (hz:0<x) (hw:0<w)(hd:x/2 ≤r) (hx:y∈ Y.omS w x r) (hc:ShadeQ L.Z L.ForestQ (Y.V (Y.boat y)) Y.Y)
include hr
-- using eventual predicates
private lemma DSpin: (∃ p, Pile L.Z L.ForestQ e b s 5 (pane L.ForestQ L.k L.P.clip L.P.path) p) ∧ (∃ p,Pile L.Z L.ForestQ e b' s 3 (fun x:L.DirA=>springF L.ForestQ L.P.path x.2) p):=by rw [hr.home.clip,hr.home.path]; exact ⟨hr.stem,hr.aged⟩ -- unused omit
include H hN hr h' hb he hb' hz hw hd hx hc
lemma axleP : ‖Y.Hx y‖+‖Y.Ux N y‖≤ PayT Y s b b' t (Y.join (2*x/w)):=by
        obtain ⟨hh,hZ,hM⟩:=Y.valley H hw hz hd y hx
        obtain ⟨⟨p,hp⟩,⟨a,ha⟩⟩:= DSpin hr
        exact (salaryP _ _ _ _ _ _ _ hN hp ha H h' hb hb' _ _ hM hc hZ he).trans ((Real.le_norm_self _).trans (le_add_of_nonneg_right (norm_nonneg _)))
lemma tunesP (hp:G.Simple) (hB:L.P.beta=w⁻¹^ (2:ℕ)) (hg:w*Y.join (2*x/w)<e)(hJ:w≤1) (hv:2* PayT Y s b b' t (Y.join (2*x/w))*w ≤1): ‖Y.will N w y-(Y.glow N y).atK w‖ ≤ duesR (PayT Y s b b' t (Y.join (2*x/w)))*w^3:=by
          let W:=L; have hi:fderiv ℝ (pane W.ForestQ W.k W.P.clip W.P.path) 0=0:=by rw [show W.P.clip=_ from hr.home.clip, show W.P.path=_ from hr.home.path]; exact pegZ W.Z W.H W.U W.k hr.signed hp
          have hΨ : fderiv ℝ (fun x:L.DirA=>springF L.ForestQ L.P.path x.2) 0=0:=by
                let T:=springF L.ForestQ L.P.path; let p:= ContinuousLinearMap.snd ℝ (Bid.Dir G L.c) (AxisChart G L.ForestQ); obtain ⟨he,hv'⟩:=sophok L.ForestQ (L.A.pays); change fderiv ℝ (T ∘ p) 0=0; unfold T; rw [hr.home.path,fderiv_comp _ (show DifferentiableAt ℝ (springF L.ForestQ L.A.live) (p 0) from he.differentiableAt (by simp)) p.differentiableAt,p.map_zero,hv',ContinuousLinearMap.zero_comp]
          obtain ⟨_,hZ,hA⟩:= Y.valley H hw hz hd y hx; obtain ⟨⟨f',hf⟩,⟨g,hg'⟩⟩:=DSpin hr; have hx': w • Y.boat y∈ ball (0:Y.St) r:= hx.2 -- trans reduce
          have hV:= stipeT L.Z L.ForestQ L.k L.P Y.X Y.w Y.ext hN hf hg' H h' hb hb' hw hg hB hi hΨ _ Y.Y hA hc hZ hx'; exact grit_exp hw hJ (axleP hN H hr h' hb he hb' hz hw hd hx hc) (hV.trans (mul_le_mul_of_nonneg_right ((Real.le_norm_self _).trans (le_add_of_nonneg_left (norm_nonneg _))) (pow_nonneg hw.le _))) hv
end Studio
end YM.OPE.Raucous.Host
