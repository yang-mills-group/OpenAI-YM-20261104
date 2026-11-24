import YM.OPE.Compatible.Myrtle.Vapor
/-! # predicted price. all horizons stochastic -/
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
lemma jetSun {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X](p:X→ℝ) (i:ℕ): Continuous (jet p i):= continuous_const.mul ((map_continuous (iteratedFDeriv ℝ i p 0)).comp (continuous_pi fun _=>continuous_id))
namespace Studio
variable {L:Host K T} (Y:Studio L)
noncomputable abbrev Hx (x:Y.St):= haze L.Z L.ForestQ L.k L.P Y.X Y.w Y.ext (Y.boat x)
noncomputable abbrev Ux (N:ChartRatio G)(x:Y.St):= litter L.Z L.ForestQ L.k L.P Y.X Y.w Y.ext N (Y.boat x)
noncomputable abbrev glow (N:ChartRatio G)(x:Y.St):Token:= ⟨1,Y.Hx x,Y.Ux N x + (Y.Hx x)^2/2⟩
noncomputable abbrev heel(s b b' t B:ℝ):= salary L.Z L.ForestQ Y.X s b b' t Y.Y B
lemma slotH (N:ChartRatio G): Continuous Y.Hx ∧ Continuous (Y.Ux N):=by
       let Q(x:Y.St):= Y.V (Y.boat x); have ht:Continuous Y.boat:= continuous_id.add continuous_const; let u:= stake Y.X (G:=G); have hx: Continuous Q:= continuous_const.prodMk (continuous_const.add (u.continuous.comp ht)); let a:=L.Z; let b:=L.ForestQ; refine ⟨((jetSun (pane b L.k L.P.clip L.P.path) 3).comp hx).neg,?_⟩; exact (((jetSun _ _).comp ht).sub ((jetSun _ _).comp hx)).sub ((jetSun _ _).comp hx)
variable {Y}
include H hN
lemma crestP {p:Y.St}(hr:L.Rich s b e b' u C)(hz:0<s)(hb:0≤b)(hb':0≤b')(hε:0<e)(ht:ShadeQ L.Z L.ForestQ (Y.V (Y.boat p)) Y.Y): ‖Y.Hx p‖+‖Y.Ux N p‖ ≤ Y.heel s b b' t (Y.Vx (Y.boat p)):=by
        obtain ⟨a,ha⟩:=hr.stem; obtain ⟨c,hc⟩:=hr.aged; have hP:Pile L.Z L.ForestQ e b s 5 (pane L.ForestQ L.k L.P.clip L.P.path) a:=by rw [hr.home.clip,hr.home.path]; exact ha
        have hX:Pile L.Z L.ForestQ e b' s 3 (fun x:L.DirA=>springF L.ForestQ L.P.path x.2) c:=by rw [hr.home.path]; exact hc
        have hy:= Y.plume (Y.boat p); exact salaryP L.Z L.ForestQ L.k L.P Y.X Y.w Y.ext hN hP hX H hz hb hb' (Y.boat p) Y.Y hy.2 ht hy.1 hε
end Studio
namespace Craft
variable {L:I→ Host K T}{Y:∀ i, Studio (L i)}{l:Filter I}{V ε B A T' :I→ℝ}
variable (h:Craft Y l V A s b e u C)
set_option quotPrecheck false
local notation "μ"=> (fun i=>(Y i).μφ)
local notation "f"=> fun i x => (Y i).Hx x
local notation "Y'"=> fun i x=> (Y i).Ux N x
include h hN H
lemma estimated : Grain μ l V (fun i x=>(Y i).Hx x) 0 ∧ Grain μ l V (fun i x=>(Y i).Ux N x) 0 :=by
        let p:= fun i (x:(Y i).St)=> (Y i).Vx ((Y i).boat x); let P i (x:(Y i).St):=paying (Y i).Y (p i x) s; let Q(i)(x:(Y i).St):= (Y i).heel s b (A i) t (p i x); have hk(x:ℝ):Grain μ l V (fun _ _=>x) 0:= Grain.const (RateLE.const x h.light); have hP:Grain μ l V P 0:= ((Grain.const h.XP).mul (h.Vap.mul (hk (Premium.overall s)))).mint (by norm_num)
        have hQ: Grain μ l V Q 0:= (((((hk b).mul (hP.pow h.light 3)|>.mint (le_of_eq (zero_add _))).add ((Grain.const h.IP |>.mul ((hk t).mul (h.Vap.pow h.light 2))).mint (by norm_num)) h.light).add (((hk b).mul (hP.pow h.light 4)).mint (by norm_num)) h.light).add (((Grain.const h.wage).mul (hP.pow h.light 2)).mint (by norm_num)) h.light)
        have hv:∀ᶠ i in l,∀ x:(Y i).St,‖(Y i).Hx x‖+‖(Y i).Ux N x‖≤‖Q i x‖ :=by
             filter_upwards [h.enters,h.covers] with i hi hM x; let g:= Y i; exact (Studio.crestP hN H hi.1 h.served.1 h.served.2.1 hi.2 h.served.2.2 (hM ((Y i).boat x)) (p:=x)).trans (Real.le_norm_self _)
        refine ⟨hQ.of_le (Eventually.of_forall (fun i=> ((Y i).slotH N).1.aestronglyMeasurable)) (hv.mono (fun i hv=> Eventually.of_forall (fun x=> (le_add_of_nonneg_right (norm_nonneg _)).trans (hv x)))), hQ.of_le (Eventually.of_forall (fun i=> ((Y i).slotH N).2.aestronglyMeasurable)) (hv.mono (fun i hv=> Eventually.of_forall (fun x=> (le_add_of_nonneg_left (norm_nonneg _)).trans (hv x))))⟩
lemma writeP : Butte μ l V (fun i=>(Y i).glow N):=by
        obtain ⟨p,hp⟩:=estimated hN H h; intro i; fin_cases i
        · exact Grain.const (RateLE.const 1 h.light)
        · exact p
        have hz:=hp.add (((p.pow h.light 2).mul (Grain.const (RateLE.const ((2:ℝ)⁻¹) h.light))).mint (le_of_eq (zero_add _))) h.light; refine hz.shift (Eventually.of_forall fun i=> funext fun x=>?_); change (Y i).Ux N x+(Y i).Hx x^2*2⁻¹=_+(Y i).Hx x^2/2; rw [div_eq_mul_inv]
end Craft
end YM.OPE.Raucous.Host
