import YM.OPE.Compatible.Camo.Hilt
import YM.OPE.Compatible.Ice.Rose
/-! # caps on all horizontal costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cameo
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type}{i j k m n M:ℕ}{ε v t c r z u s e a β C R A D:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Push Push.AbsoluteSums.Animals
variable {K:Sponsor G}{T:Seasons K}
section
open Ibis Stroke Borealis Borealis.Galea
variable {L:Host K T} {V:ℝ}
variable (T':BudgetPoint) (p:Config G L.c→ℂ)(a:ℂ→L[ℝ]ℝ)(x:Site L.c){b:ℕ}(P:Spells.Pad G)(hv:2*(b+1)<L.c.val)(h:Acceptance x T' (k+6) p b v)
-- seam at anchor. Eye width Rβ. tilt.Q
private lemma Opt (w:Bid.Dir G L.c)(i:TilesB m): InLine m (charW x w) i = w (x+wrap L.c i.val.1,coord i.val.2):= rfl
private lemma Knorm (w:Bid.Dir G L.c)(m:ℕ): ‖InLine m (charW x w)‖≤‖w‖:= (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun _=> (congr_arg norm (Opt ..)).trans_le (norm_le_pi_norm w _)
-- shorthand crossing
abbrev Covered (L:Host K T)(x: Site L.c)(b:ℕ)(j:Site L.f)(n:ℕ):Prop:= ∀ i:TilesB (4*b),(x+wrap L.c i.val.1,coord i.val.2)∈rangeG L j n
private lemma Znorm (w:Bid.Dir G L.c){y:Site L.f}(hd:Covered L x b y M): InLine (4*b) (charW x w)= InLine _ (charW x (Qspot L y M w)):=by funext i; rw [Opt,Opt,Q_on y _ (hd i)] -- Q unbound
lemma Tess (W c:ℝ){y:Site L.f}(hd:Covered L x b y M)(w:Bid.Dir G L.c): Mell x P T' p a W hv (charW x w) c=Mell x P T' p a W hv (charW x (Qspot L y M w)) c:=by unfold Mell WSign;rw [vents _ _ (Znorm x w hd)]
noncomputable abbrev hY (b:ℕ)(t:ℝ)(G:Gauge):= TagN (BFilm b (0:fieldX (Shade G))) + (1+t)^3*(3*LargeK G b) -- maybe simpler
lemma μnorm(w:Bid.Dir G L.c){r:ℝ}(h:‖w‖ ≤ r)(b:ℕ): TagN (BFilm b (charW x w))≤ RedG G b r ∧ AuroraK b (charW x w)≤ Mā G 4 b r:=by
       let u:= ‖InLine (4*b) (charW x w)‖; have hh:u≤r:= (Knorm x w (4*b)).trans h; let v:=charW x w; have hp(i:ℕ): Mā G i b u≤ Mā G i b r:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (add_nonneg zero_le_one (norm_nonneg _)) (add_le_add le_rfl hh) _) (show 0≤ magnol G i*RoadK b^i from by simpa only [Mā,add_zero,one_pow,mul_one] using Māhi G i b le_rfl); have he (i:Phase): ‖PlateB (i.val+1) b v‖≤ Mā G (i.val+1) b r:=(PriceFl ..).trans (hp _); refine ⟨?_,hp _⟩; unfold TagN RedG; change 1+ ‖PlateB 1 b v‖+‖PlateB 2 b v‖+‖PlateB 3 b v‖ ≤ 1+ _; rw [CxT,← _root_.add_assoc,←_root_.add_assoc]; exact add_le_add (add_le_add (add_le_add le_rfl (he 0)) (he 1)) (he 2)
variable (W c:ℝ)(q:Phase)
local notation "μ!"=> (1+‖c/2‖)
local notation "R!"=> TourF P T' a (k:=k+6) (b:=b) (t:=v) W
noncomputable abbrev Elev(w:Bid.Dir G L.c):= Mell x P T' p a W hv (charW x w) c
include h
lemma TessPay (w:Bid.Dir G L.c)(hw:‖w‖≤r): ‖(Elev T' p a x P hv W c w).seq q.val‖ ≤ Jfare ((1+‖c/2‖)* RedG G b r) (TourF P T' a (k:=k+6) (b:=b) (t:=v) W):=by
       let A:=Artifact x P hv T' p a W; have he : Velvet A R! 0:= GrowE x T' P p a W b 0 h (by omega) _; let V:= Ebox (BFilm b (charW x w)) c; have hz: TagN V ≤ μ! * RedG G b r:= Cert _ _ (μnorm x w hw b).1; apply thickP (W:=V) (f:=A) _ he.roll (fun i hi x _=>by simpa only [pow_zero,mul_one] using he.seats i hi x) he.pos q
       have hx: scope V (TagN V):=by
             have he : ‖V.s‖ ≤ TagN V ∧ ‖V.l‖≤ TagN V ∧ ‖V.h‖≤ TagN V:=by unfold TagN; have hh:=norm_nonneg V.h; have hy:=norm_nonneg V.s; have h:=norm_nonneg V.l; exact ⟨by linarith,by linarith,by linarith⟩
             intro i; fin_cases i
             · exact he.1
             · exact he.2.1
             exact he.2.2
       exact fun i=>(hx i).trans hz
end
end YM.OPE.Cameo
