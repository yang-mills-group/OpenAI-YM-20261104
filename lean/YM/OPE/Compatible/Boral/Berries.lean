import YM.OPE.Compatible.Boral.Yul
/-! # Shift-independent LP signal book on platter. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type*} {i k m:ℕ}{t C s u z ℓ v a c e r R:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown
variable {K:Sponsor G}{T:Seasons K}
section
variable {N:ChartRatio G}(hN:LocalRatio N)
variable (L:Host K T) (p:Sender L)
local notation "Fθ"=> L.ForestQ
open AnalyticNext.QuarticMatch Radius Radius.Articles Radius.Fetch Radius.Showroom Estimate
local notation "Yκ"=>AxisChart G Fθ
noncomputable abbrev Rate3 : L.DirA →ℝ:=fun x=> -(jet L.PA 3 x)
noncomputable abbrev Rate4 (N:ChartRatio G):L.DirA→ℝ:=fun x=> -(jet L.PA 4 x)- jet L.PL 2 x+ jet (taxY L.ForestQ N) 2 x.2
noncomputable abbrev CoatB (N:ChartRatio G) (x:L.DirA) :Token:= ⟨1,Rate3 L x,Rate4 L N x+(2:ℝ)⁻¹*(Rate3 L x)^2⟩
noncomputable abbrev MuseY (N:ChartRatio G)(Y:Studio L):Token:= Speak Y.μφ (fun x=> CoatB L N (Y.V (Y.boat x))) (fun x=> p (Y.V (Y.boat x)).2)
noncomputable def GPY (N:ChartRatio G)(x:Bid.Dir G L.c): Token:= L.F.L.predicts N (fun y=>p y.2) x
noncomputable abbrev majr:= quart L.F.L.Q (Chart.tangent G (forest L.Z.ratio L.H).Free)
noncomputable abbrev stareD (x:Bid.Dir G L.c)(z:Yκ):L.DirA:= (x,L.F.L.M x+z)
include hN
lemma RFrame (Y:L.DirA)(h: L.Rich s c e v u C)(he:L.b=0)(hs:G.Simple):Libra.Adhesion.Curling L.F.L.f (L.F.L.wSign N) Y=CoatB L N Y:=by
             rw [gumbar L.Z L.H L.U L.k h.signed hN L.F Y hs]; let p:=HaloC L.Z L.H L.k L.b L.A N; let U:L.DirA→ℝ:=fun x=>taxY _ N x.2; let V':L.DirA→L[ℝ] Yκ:=ContinuousLinearMap.snd ..; have hv:p=(4:ℝ)⁻¹ • (U+((-1:ℝ) • L.PL)):=by funext x; unfold p HaloC U; simp only [he,neg_zero,zero_mul,zero_sub,Pi.add_apply,Pi.smul_apply,smul_eq_mul]; change (_+_)/4=4⁻¹*(_+ -(1:ℝ)*L.PL _); unfold Host.PL;ring -- arg
             obtain ⟨hp,-⟩:= accountV L.ForestQ hN; have hz: ContDiffAt ℝ (↑(2:ℕ)) U 0:=(hp.comp (f:=V') 0 V'.contDiff.contDiffAt).of_le le_top; have hh:= (sophok L.ForestQ L.A.pays).1; have hh' : ContDiffAt ℝ (↑(2:ℕ)) L.PL 0:=(hh.comp (f:=V') 0 V'.contDiff.contDiffAt).of_le le_top; have hX: jet U 2 Y=jet (taxY L.ForestQ N) 2 Y.2:=by unfold jet; rw [show iteratedFDeriv ℝ 2 U 0 _= _ from (show _= _ from lin_rate_at (taxY L.ForestQ N) V' 0 hp 2 (fun _=>Y))]; rfl
             have he':jet p 2 Y=(4:ℝ)⁻¹ * (jet U 2 Y- jet L.PL 2 Y):=by have hg:ContDiffAt ℝ (↑(2:ℕ)) ((-1:ℝ) • L.PL) 0:=hh'.const_smul (-1:ℝ); rw [hv,arcConst _ (show ContDiffAt ℝ (↑(2:ℕ)) (U+(-1:ℝ) • L.PL) 0 from (hz.add hg)),arcAdd hz hg,arcConst _ hh'];ring
             rw [he',hX]; apply JetS.eta; · rfl;
             · rfl
             change -jet L.PA 4 _ +4*_+ _=Rate4 L N Y+(2:ℝ)⁻¹* _; unfold Rate4 Rate3; change _ + (-jet L.PA 3 Y)^2/2= _;ring -- path
lemma βRead (h:L.Rich s c e v u C)(he:L.b=0)(hs:G.Simple)(x:Bid.Dir G L.c): GPY L p N x= Speak (majr L) (fun y=>CoatB L N (stareD L x y)) (fun y=>p (stareD L x y).2):=by
            let B:=L.F.L; let Y(y):=stareD L x y
            let A:= Chart.tangent G (forest L.Z.ratio L.H).Free; have hx(g:Yκ→Token): ηAvg (majr L) g= Libra.draw g L.F.L.Q A:= by apply JetS.eta <;> exact has_p _ _ _
            rw [Speak,hx,hx]; let W(y):= B.cloth N (x,y);
            have ht: W=fun y=>CoatB L N (Y y):=funext fun y=> RFrame hN _ _ h he hs
            rw [show (fun y=> p (stareD L x y).2)*(fun y=>CoatB L N (stareD L x y))=(fun y=>p (Y y).2)* W from ?_, ← show W= _ from ht]; rfl
            rw [ht]
end
end YM.OPE.Borealis
