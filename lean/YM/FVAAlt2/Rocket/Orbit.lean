import YM.FVAAlt2.Rocket.Reading
import YM.RegulatorIR.Atlas.Outfit
/-! # Softening on cover directly from uncalibrated top fields
 This uses the RegulatorIR SatisfiesQ with OUR top stencil REPORT, fixed rank, native
 units. Kick is proved, not inherited estimates after dressing. Particularly, no task-bounds from
 pivot history; includes large top-age costs in explicit Meters. Holds for all histories admitted by
 this geometry (including still at finite N), with prices that do not involve size of growing orbit
 except by spacing & control. Projection of cover Z.main participating here is its
 **full identity-output numerator/vac conditional** before testing against a coarse measure;
 as in `
 Ledger` infinite cover (not evaluating this output on a fundamental domain).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Rocket
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Profiles Sources Labels Source Momentum Clocks
open Oracle Atlas Epoch Calibration Calibration.Notebook
open Kick
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {X I:Type}{u a b p e r:ℕ}{M:X→ℕ}{n:Page M→Side}{G:Gauge}
variable (S:Oracle.Circuit M n){K:KernelChoices}(Y:Oracle.Program K)(Z:∀ P: Patch,P.Branches K G) {B:Epoch.Marked M}
variable {g:G.ColorIndex}{γ:ℝ}{F: Calibration.Tent M}{x:X→Room}{L:Meter X}
local notation "LΘ"=> S.lane Y G Z (sheet F)
local notation "AΘ"=> S.payroll Y G Z (sheet F)
local notation "Σ'"=> S.dialect Y G Z (sheet F)
-- truncation.P hotCharge implicit.
def native (M:X→ℕ): Ledger.Choice M:= ⟨0,fun _=>Nat.zero_le _⟩
local notation "η"=> native M
local notation:max "P_" w:max => Page.opening M w
variable (A: X→Orders (Foot G)) {V: X→ Portrait G}(H:Kick L x a V A)
set_option quotPrecheck false
local notation "Ωf"=> Profiles.declaring AΘ A H.census
-- cost build
lemma shade_top (W:X)(h : S.l (P_ W)=1)(Q:Packet (Foot G) r) : markQ ((Σ').coverQ x u (P_ W)) Q= markQ (monetary u (x W)) Q:=by
    let w:=P_ W; let t:=Σ'; let l:=t.l w
    let T₀ (l:ℝ) (h:0<l) (y:Room)(Q:Packet (Foot G) r) := markQ ((Premium.rooted (Tariff.native (max 1 l) (lt_max_of_lt_right h) u) y).uses (fun i:Foot G=> Geometry.seat l i.1)) Q
    change T₀ (S.l (P_ W)) (S.l_p _) (x W) Q=_
    refine Eq.trans (b:=T₀ 1 zero_lt_one (x W) Q) ?_ ?_
    · congr 1; exact S.l_p _
    unfold T₀
    let V(r:ℝ)(hr:0<r):= markQ ((Premium.rooted (Tariff.native r hr u) (x W)).uses posH) Q
    change V _ _= V _ _; congr 1; all_goals try norm_num
lemma carries (hk:∀ w,S.l (P_ w)=1)(m:ℕ) : (Σ').Preserved AΘ Ωf 1 m p η x u L:=by
   intro i hi j; let E:= (η).before
   let k(w:Page E.spans):= markQ (monetary u (x w.bindW)) (A w.bindW i j)
   refine ⟨_, (H.paid p u i hi j).us Page.bindW,?_⟩; intro w;rcases w with ⟨w,d,hd⟩; change d≤0 at hd; obtain rfl:d=0:= by omega  -- dependent? likely fail
   change markQ ((Σ').coverQ x u (P_ w)) (A w i j) ≤ markQ (monetary u (x w)) (A w i j) * (ENNReal.ofReal ((S.l (P_ w)^m)⁻¹) * 1); rw [shade_top _ _ _ w (hk w),hk w];simp
lemma still : Feeds.scale Calibration.dawn= Clocks.flat:=by unfold Calibration.dawn Clocks.flat Feeds.scale creator; congr; ext1 i; simp
variable (hq:Atlas.SatisfiesQ G Y S Z B p u γ) (hver:Notebook S Y G Z g (native M) F p) (hc:∀ w,B.peak (Page.opening M w)=0) (hP:∀ w,S.l (Page.opening M w)=1)
variable (hL:OfAge B L)(hN: ∃ v:ℕ,∀ w,(n (Page.finallyW M w)).val≤v)
include hq hP hc hver hL hN
open YM.FVAAlt2
lemma start_table (hg:G.Simple){c₀:ℝ}(J:Choice M)(hb:quantum 1 0 ≤u)(hp:0<c₀)(ht:(Σ').cushion c₀ x)(he:e≤ p) : Carry L (fun w=> ENNReal.ofReal ((Σ').modifyErr 0 1 γ J w)) fun w=> ‖plotPT Clocks.flat (vital (n (Page.opening M w)) (V w)) a e-note ((Ωf).main (J.choose w) e 0)‖ₑ :=by
    have hm:∀ w,(LΘ).clock (P_ w)= Clocks.flat:=by intro w; change (F (Page.opening M w)).scale= _; rw [ show F (P_ w)=Calibration.dawn from hver.reference w ]; exact still
    -- simp_rw [fun w=> show plotPT Clocks.flat (vital (n (Page.opening M w)) (V w)) = _ from congrArg (fun t=> plotPT t (vital (n (Page.opening M w)) (V w))) (hm w).symm] -- implicit
    obtain ⟨k,h⟩:=hN
    obtain ⟨JH,Q⟩:= Atlas.reservations S G Y Z (D:= native M) hc hL hq g hver hg hP
    have HH:=H.authority; change ∀ w,Halo.BasisT _ _ (V w) ((Ωf).main (P_ w)) at HH
    have h₀:= (JH.emits (b:=1) (by norm_num) hb).transmission (J:=J) Ωf V HH Q (carries S Y Z _ H hP 0) hp ht he (fun _=>Nat.zero_le _) (Atlas.closures S G Y Z hL hq k h F)
    simp_rw [hm] at h₀; exact h₀
local notation "nbig"=> ∃ v:ℕ,∀ w,(n (Page.finallyW M w)).val≤v
end YM.RegulatorIR.FVAAlt2.Rocket
