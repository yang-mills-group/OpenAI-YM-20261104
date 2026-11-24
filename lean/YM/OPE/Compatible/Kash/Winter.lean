import YM.OPE.Compatible.Kash.Rule
import YM.OPE.Compatible.Kash.Pond
import YM.OPE.Compatible.Kash.Snow
import YM.OPE.Compatible.Ice.Room
import YM.OPE.Compatible.Chest.Booth
/-!
# A uniform period threshold from sequential field estimates

`PassportIce` supplies `CropFill` along sequences with `β` tending to infinity
and periods above `Ramp`. Under this hypothesis, `phrase` gives the `ClockVal`
bound for every sufficiently large scale and every period above that cutoff.
`ThresholdIce` and `PoleC` package the estimate with `epsilonR = 1/100`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic StageLight
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{p p':Clip}
variable {v v' b u:ℝ}
variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full
variable {X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
variable {Y:M→ℝ}
local notation "J!"=> Fin (l+1)
local notation "F!"=> Tracts G d τ
local notation "JΛ"=> Fin (l+1) 
open Pipes
local notation "μ"=>lapPrice (Patch.L P)
section
open GlowPack Silt.Phere Ibis Owl Lass.Zest Spells Yolk Pill Dial
variable {L:PriceBook H T}{a:Axis}(V:Foyer L hs a l (l+6+6))(i':ℕ)(he:highStage L hs a V ≤ i')
variable (S:Stage)(X:BankW L hs a V he S.clip) (P:Pad G)
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
local notation "F*"=> solar G (l+6+6) V.pay.st.τ
-- The period bound applies to each member of the indexed family.
variable {n:I→Side}{φ:Filter I}{β:I→ℝ} (ξ:ℝ)(r l':ℕ)
variable (A:∀ i, HillZ (T:=T) S i' r l ξ (β i) (n i))
open CardinalQ Next.Scheduling
local notation "L'"=>l+6+6
local notation "M!"=> localSection G l
noncomputable abbrev Ramp (x:ℝ):ℕ:= Nat.ceil (Real.exp x)+SiteEra V i' he ℕ (Real.log x)
noncomputable abbrev epsilonR :ℝ:=1/100
lemma q'φ : q2 < -1-epsilonR:=by unfold q2 epsilonR; norm_num
structure PassportIce (a:Axis)(g:G.Simple):Prop where
       vest :∀ (K:Sponsor G)(T:Seasons K)(H:LocalRatio (chart G))(L:PriceBook H T)(l:ℕ)(V:Foyer L g a l (l+6+6))(i:ℕ)(he:highStage L g a V ≤ i)(S:Stage)(_X:BankW L g a V he S.clip)(P:Pad G) (r:ℕ)(t:ℝ)(β:ℕ→ℝ)(n:ℕ→Side), Tendsto β atTop atTop → (∀ j, Ramp V i he (β j) ≤ (n j).val) →∀ A:(j:ℕ)→ HillZ (T:=T) S i r l t (β j) (n j),∀ g:ℂ→L[ℝ]ℝ,CropFill V i he S P A g (φ:=atTop)
section
variable (he':PassportIce a hs)
include he'
noncomputable abbrev Φfee (A: HillZ (T:=T) S i' r l ξ b c) := Swing V X A.living A.lens P (Clock.gap A.path.beta) A.art
private def SlowGoal (t β:ℝ)(n:Side)(Y:HillZ (T:=T) S i' r l t β n):Prop:=‖ClockVal V X Y.lens (localSection G l) P Y.living (Clock.gap Y.path.beta) Y.art‖ ≤ heats epsilonR β

end
section
variable {H:LocalRatio (chart G)}{L:PriceBook H T}{a:Axis}(V:Foyer L hs a l (l+6+6))(i':ℕ)(he:highStage L hs a V ≤ i') (F:Stage)(X:BankW L hs a V he F.clip) (P:Pad G)(he': PassportIce a hs)(u:ℝ)
include he'
set_option maxHeartbeats 200000
lemma phrase (r:ℕ):∀ᶠ x:ℝ in atTop,∀ (n:Side),Ramp V i' he x ≤ n.val→∀ Y:HillZ (T:=T) F i' r l u x n, ‖ClockVal V X Y.lens (localSection G l) P Y.living (Clock.gap Y.path.beta) Y.art‖ ≤ heats epsilonR x:=by
        let Fail (x:ℝ):Prop:=∃ n:Side,Ramp V i' he x ≤ n.val∧∃ Y:HillZ (T:=T) F i' r l u x n, ¬ SlowGoal V i' he F X P r u x n Y
        have hw:∀ᶠ x in atTop,¬Fail x:=by
               by_contra h; rw[not_eventually] at h; simp only [not_not] at h; choose f H hF using fun i:ℕ=> frequently_atTop.mp h (i:ℝ); choose n hn Y hY using hF; have he':= he'; have hp:Tendsto f atTop atTop:=tendsto_atTop_mono H tendsto_natCast_atTop_atTop; have hB:∀ g:ℂ→L[ℝ]ℝ,CropFill V i' he F P Y g (φ:=atTop):= he'.vest _ _ _ L l V i' he F X P _ u f n hp hn Y; have he := EraQ V i' he F X P Y hp (Eventually.of_forall fun i=> le_trans (Nat.le_add_left _ _) (hn i)) hB; obtain ⟨j,hj⟩:= (he _ q'φ).exists; exact hY j hj
        refine hw.mono fun i hi n h Q=> not_not.mp (fun hh=> hi ⟨n,h,Q,hh⟩)
lemma ThresholdIce (r:ℕ) : ∀ᶠ x:ℝ in atTop, Freeze hs P V he F X u epsilonR x r:=by
        filter_upwards [phrase V i' he F X P he' u r,eventually_gt_atTop 0] with x hx hy; constructor; refine (eventually_ge_atTop (Ramp V i' he x)).mono fun n hn i he' => ?_; obtain ⟨b,hb,hB⟩:= freeze_it (G:=G) F hy u i
        refine ⟨b,hb,fun p Z W X1 hf h hz hV p' hq hp hU=>?_⟩; have hm:Cyan F u x p:=⟨hV,hf.clip.trans X1.clip,h.1.TagQ⟩; exact hx i (le_trans hn he') ⟨p',hq,p,hm,Z,W,X1,hf,h,hz,hp,hB _ hm _ r hU⟩
lemma PoleC : Glacier (a:=a) hs epsilonR:= ⟨by unfold epsilonR; norm_num,by unfold epsilonR; norm_num,fun K T Z L l X i he F W P a n=> ThresholdIce X i he F W P he' _ n⟩
end
end
end YM.OPE.Stroke
