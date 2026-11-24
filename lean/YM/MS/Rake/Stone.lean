import YM.MS.Rake.Regalia
/-!
# Birth handling all configurations. Northern piece.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rake.Geo
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook
open scoped Topology ContDiff Interval
variable {G: Gauge}{I E:Type} [ NormedAddCommGroup E ][ NormedSpace ℝ E] {b c d:Bool}{k n:ℕ}{h:ℤ}
  (P:Geo I) {A:ℝ} {F H: Glade G I } {K:Belt I}
local notation "Ω"=>east P b
abbrev lamp (b:Bool) {X:Belt I} (p:X.time):= if b then exp (tstart p) else 1
lemma unitE (p:(east P true).time): (east P true).price.length p=1:= by change exp ( if true=true then 0 else (tstart p) )=1; simp
lemma coldE (p:(east P false).time): (east P false).price.length p=exp (tstart p):= by simp [ east,solar,market ]
lemma seasonE (p:(east P b).time): exp ( tstart p ) ≤1:= Real.exp_le_one_iff.mpr p.2.property
lemma b_le (p:(east P b).time): (east P b).price.length p≤1:= by cases b; rw [ coldE ]; exact seasonE P p; exact le_of_eq ( unitE P p )
lemma lampC (p:(east P b).time): lamp b p≤1:= by cases b; simp [lamp]; simpa [lamp] using seasonE P p
lemma airLamp (X:Belt I)(b:Bool): nn (lamp (X:=X) b):=by intro i; unfold lamp; split; positivity; exact zero_le_one
lemma tollB (k:ℕ)(b:Bool): nn (birthTar (K:=east P b) P k):= by intro x; unfold birthTar; positivity
lemma rateC (k:ℤ) (K:Belt I): nn (rateS K k):= fun i=> zpow_nonneg ( K.price.pos i|>.le) _
lemma lowerB (p:(east P b).time)(k:ℕ) : birthTar (K:=Ω) P k p ≤ 1:= by unfold birthTar; refine mul_le_one₀ ( seasonE P p ) (by positivity) ( pow_le_one₀ (by positivity) (Real.exp_le_one_iff.mpr ?_) ); exact neg_nonpos.mpr (P.room _)
lemma rank_e (p:(east P b).time)(r:ℕ): 1≤ rateS Ω (r:ℤ) p:= by unfold rateS; rw [zpow_neg]; exact one_le_inv₀ (zpow_pos ((Ω).price.pos p ) _ ) |>.mpr (by rw [zpow_natCast]; exact pow_le_one₀ ( (Ω).price.pos p|>.le) ( b_le P p))
lemma rightB (p:(east P b).time): (east P b).price.length p ≤ roots P p.1 := le_trans (b_le P _) ( Real.one_le_exp (P.room p.1))
lemma light_η (P:Geo I)(J:I→ Set ℝ)(h:∀ i, MeasurableSet ( J i ))(c:Moments I ℝ)(q:(solar P J h c).time) : ‖P.η q.1‖ ≤ (solar P J h c).price.basic q := by
   change |P.η q.1| ≤ (1+|P.η q.1|)*(1+|tstart q|); exact le_trans (by linarith : |P.η q.1|≤1+|P.η q.1| ) (le_mul_of_one_le_right (by positivity) ( by simp ))
lemma LightY (P:Geo I)(J:I→ Set ℝ)(h:∀ i,MeasurableSet ( J i ))(c: Moments I ℝ)(q:( solar P J h c).time): ‖P.η q.1+tstart q‖≤ (solar P J h c).price.basic q := by
   apply (norm_add_le ..).trans; change |P.η q.1|+|tstart q| ≤ (1+|P.η q.1|)*(1+|tstart q|); nlinarith [ abs_nonneg (P.η q.1),abs_nonneg (tstart q)]
lemma sunX (p:Pack G)(hp: Fees c h p) : Here c d (east P true) (fun i t=> p (η P i) (exp t)) 1:= maximumT (a:=fun i=>exp (tstart i)) ( fun i=> ( norm_of_nonneg (exp_pos _|>.le) ).le.trans (seasonE (b:=true) P i )) (unitE P) p hp (η:=fun i=>η P i.1) ⟨1,zero_lt_one,1,fun i=>(by simp only [one_mul,mul_one,pow_one, Pi.one_apply]; exact light_η P _ _ _ (i:(east P true).time))⟩ -- syntax
set_option maxHeartbeats 500000 in
lemma sund (F:Pearl.Flats G)(hp:Emit.Host F n): Here c d (east P false) ( nameR (four n F) P.η ) (rateS (east P false) n):= by apply nameD ( S:=(east P false).price) (a:=tstart)  hp (fun i=>(coldE P i).symm) ( η:=fun i=>P.η i.1 ) (fun z=> LightY P _ _ _ z)
-- actual Λ local classes
structure Stage (K L: Planet G I) (P: Geo I) (b:Bool): Prop where
   well: Sheet (east P b).price (lamp (X:=east P b) b) (plug L)
   market: CourseK (east P b).price 1 (plug K)
   pinC: S0 K
   pool: BackF L
variable (G I)
abbrev constantP (G:Gauge)(I:Type)(P:ℝ→ Edge G): Planet G I:= fun _=> P
lemma masterD (P: Geo I): Stage (constantP G I (PlanetD G)) (constantP G I (PlanetD G)) P false:= by
    have he : Sheet ( east P false ).price 1 (plug (constantP G I (PlanetD G))) := cost_D ( fun i=>( coldE P i).symm ); exact ⟨he, fun i j=> polar ( he i j ), sugar _ _ (Upcoming I G), Upcoming I G ⟩ -- leg p against false defeq?
lemma masterL (P:Geo I): Stage (constantP G I (LowP G)) (constantP G I (PlanetL G)) P true:= by
   have hu:= seasonE P (b:=true); have he: Sheet ( east P true ).price (fun x=>exp (tstart x)) (plug ( constantP G I (PlanetL G))) := crown hu ( unitE P );
   refine ⟨he,fun i j=> ( ( cost_L0 (G:=G) hu (unitE P) ) i j ).raise ( Cost.of_le (fun s p _=>?_ )), MainL I G, HereL I G⟩; exact mul_le_mul_of_nonneg_left (hu s) (length_p ..) -- unification
end YM.MS.Rake.Geo
