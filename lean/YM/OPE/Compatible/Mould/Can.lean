import YM.OPE.Compatible.Mould.Crest
/-!
# Finite rank slope registration. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}{U:Boxes G P K.K}
variable {H:LocalRatio R}{hs:G.Simple}{X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m){Z:Topic H hs X B D₀}{a:Axis}
open Flume.Script Maxwell Balsam Nestle Pert.Full Variance
namespace Topic
variable {p₁:Clip}{u ν:M→ℝ}{hp:4≤ i}{V:(j:M)→Alps K T i (u j)}{hq:1 ≤ u}{U: Z.Ω M u}
variable (T': Z.Floss V U hp (le_trans zero_le_one hq) k Hp a)
local notation "F!"=> Tracts G d τ
noncomputable abbrev soupA (V:Alps K T i v) (hp:4≤ i)(h:0 ≤v) (D:Stern K P τ l d w):= OmegaPhi (H:=H) (hs:=hs) (D₀:=D) a V hp h
noncomputable def Sapling (t:M) : Submodule ℝ (Tracts G d τ):= by
      exact OmegaPhi (H:=H) (hs:=hs) (D₀:=D₀) a (V t) hp (zero_le_one.trans (hq t))
include T'
lemma Bliss (hx:∀ t,(V t).clip=p₁) : Forum (d:=d) (τ:=τ) V (fun i=>Variance.SailSap (V i) H hp hs (zero_le_one.trans (hq i)) P a l):=by
       refine ⟨fun i r' hr e A' y h p ht=>Variance.Hero _ H hp hs (zero_le_one.trans (hq i)) P e y _ p hr T'.ward T'.dimD h ht a,hp,zero_le_one.trans hq,_,hx⟩
local notation "S!"=> Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀)
lemma Cune (r: Fin (e+1))(he:e <l+1)(hx:∀ t,(V t).clip=p₁)(hp':r.val*l≤τ 0)(x:Bead G l e)(hm:x∈ Ghost G l e):∃ p:M→Tracts G d τ, Wealth p u 1∧∀ i,p i∈ Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀) i ∧ SprigT D₀ (p i) r x:=by
       let Y(t:M):=Variance.SailSap (τ:=τ) (d:=d) (V t) H hp hs (zero_le_one.trans (hq t)) P a l; have ht:= D₀.mark; have hA:=BrightStock Y V (impress x r) hp' (by omega) hs (Bliss (hq:=hq) Hp T' hx) ((ghost_iff _|>.1 hm) r); obtain ⟨c,hc,Ht⟩:= hA.stock; choose q hq' hz hV using Ht; let g(i:M):=Fallix G D₀.aware K (V i).gear hp; let p(i:M):= (g i).symm (q i); have hy: Wealth p u 1:= segmentWe (FallWeather (K:=K) D₀.aware (fun i=>(V i).gear) hp _ hq).2 (Zcost q c hc hq hq'); have hQ(i:M): g i (p i)=q i := (g i).apply_symm_apply _; refine ⟨p,hy,fun i=>⟨?_,Pollen D₀ r he hp' (p i) (V i).gear hp _ ((hQ i).symm ▸ hV i)⟩⟩; exact (show g i (p i)∈ Y i from (hQ i).symm ▸ hz i)
end Topic
end YM.OPE.Stroke
