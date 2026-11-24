import YM.FVAAlt2.Convert.Fort
/-! Post-Peal limit for each admissible constant q. stronger than `Drivers.Harvest`. 
Eventual support conditions inside implicit branch proved via h positivity.
No perseverance claims for numerical running coupling in variable q or growth rates.
Uses Matrix rates already achieved with exact frame elimination, not multiplied by diverging
field-Frame P. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Convert
open Function Filter Set MeasureTheory Metric Finset Topology Lattice Extraction
open PertExtension PertExtension.Position Labels
open FormalOPE FormalOPE.RG10 RG10.Position RG10.Position.Peal RG10.Carryon RG10.Gazebo
open MS MS.Land Home Home.Report Precision
open PowerSeries (C coeff constantCoeff subst)
open scoped Topology BigOperators PowerSeries ContDiff Classical
variable {G:Gauge}{F:Frames G}{I:Type*}{l:Filter I}{d:ℕ}
local notation:max "V_" n:max=> RG10.Position.Deck F n
local notation "Υ"=> Mark (V_ d) PertExtension.Physical.Profile.n
section tune
variable {b: I→Datum ( RG10.Position.Deck F 6 ) →PowerSeries ℝ} {a:Datum ( RG10.Position.Deck F 6 )→ PowerSeries ℝ}(hk:∀ v,AlignSeries l (fun i=> b i v) (a v))
include hk
lemma tolls (x:Fin d↪ Fin 3) : AlignSeries l (fun i=> touch F (b i) x) (touch F a x):= by unfold touch; exact AlignSeries.sum _ _ fun i=> (AlignSeries.const _).mul (hk _)
lemma beatCost : AlignSeries l (fun i=> ( charged ( b i ) ).x) (charged a).x:=by
 unfold charged mint; apply AlignSeries.mul (AlignSeries.const _) (p:=fun _=>_) (q:=fun i=>Triangle.deviation _ ) -- h type placeholder
 have ht: AlignSeries l (fun i=> together F ( b i )) ( together F a ):= by unfold Peal.together; exact AlignSeries.add (p:=fun i=> _) (q:=fun i=>_) ( (tolls hk _).sub (AlignSeries.sum _ _ fun i=> (tolls hk _).mul (tolls hk _) )) ( (AlignSeries.const (2:PowerSeries ℝ)).mul (AlignSeries.prod _ _ _ fun i _=> tolls hk _) ) -- sum
 apply ht.sub (q:=fun i=> C ( constantCoeff (together F ( b i ) ))) (AlignSeries.scalar_C _ _ (by simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using! ht 0)) -- unfolding
end tune
variable (P:Plan F) (hP:P.liftOff=LoftPP F) {W: Drivers} (Y: Patience P W) (Q:ChartRatio G) (hQ:LocalRatio Q)(hg:G.Simple)
variable (μ:ℝ) {U:Booked (seats P.liftOff P.certified)} (S:MS_Data G U) (X:Prescription ( seats P.liftOff P.certified )) (hx:Launch (F:=F) (Lobby.Table (Home.Profiles.nativeR P) (Home.seats P.liftOff P.certified)) S X)
local notation "R"=> river P μ S
local notation:max "Z"=> χ P S μ
local notation "V"=> Deck F 6
variable (q:Side)(hq:1<q.val)
local notation "TZ"=> rates (X:=X) μ q P
set_option quotPrecheck false
local notation:max "γ"=> Convention ∘ (rates (X:=X) μ q P)
include hP hQ hx hq hg μ Y
lemma sea : AlignSeries atTop (fun i:ℕ=>(γ i).x) ( Z ).x:= beatCost (F:=F) (hk:=fun v=> reporting μ P Q hg hQ hx q hq Y.certified v)
lemma hot : ∀ᶠ i:ℕ in atTop,(γ i).Hot := (sea P hP Y Q hQ hg μ S X hx q hq 1).eventually ( isOpen_ne.mem_nhds ( (peal_hot P hP hQ μ S hg Y.certified hx.money).trans_ne one_ne_zero ) )
-- funded coupling detector on all late real column diagnostics
local notation "Qχ"=> Convention ∘ P.dressed q
lemma bill (n:ℕ): γ n =(depart P X μ q n).step ( Qχ n ):= Warp.trade ..
lemma rightful : Tendsto (fun i:ℕ=> coeff 1 ( Qχ i ).x ) atTop (𝓝 1):=by
 obtain he:= sea P hP Y Q hQ hg μ S X hx q hq 1; change Tendsto (fun i:ℕ=> coeff 1 ( γ i ).x) _ _ at he; have hz(i:ℕ): coeff 1 ( γ i ).x=coeff 1 ( Qχ i ).x:= by rw [ bill P hP Y Q hQ hg μ S X hx q hq, Warp.step, Warp.heats, leaving,mul_one ]
 simp_rw [hz] at he; rwa [ show coeff 1 ( Z ).x=1 from peal_hot P hP hQ μ S hg Y.certified hx.money] at he
lemma determined : ∀ᶠ i:ℕ in atTop, ( Qχ i ).Hot := (rightful P hP Y Q hQ hg μ S X hx q hq).eventually (isOpen_ne.mem_nhds (one_ne_zero : (1:ℝ)≠0)) -- typo
lemma steps_go (p:Υ) : AlignSeries atTop (fun i=> Plan.collect F P q i d p) ( Y.Yield p ):=by
 obtain hR:= reporting μ P Q hg hQ hx q hq Y.certified p; obtain hU:= (sea P hP Y Q hQ hg μ S X hx q hq).inverse_est ( isUnit_iff_ne_zero.mpr ((peal_hot P hP hQ μ S hg Y.certified hx.money).trans_ne one_ne_zero )); obtain ht:= hU.compose hR ( PertExtension.Position.Triangle.inverse_zero _ ) (Eventually.of_forall fun _=> PertExtension.Position.Triangle.inverse_zero _) -- namespace clash
 intro n; rw [ show Y.Yield p=( ( Z ).refund.charge ( (Init (science μ S F) P.stock) d p ) ) from congr_fun (congr_fun (Y_eq P S X W Q μ hg Y.certified hQ hx.high ( tired μ P Q hg hQ hx ) ( peal_hot P hP hQ μ S hg Y.certified hx.money ) Y) d) p ]; rw [ Warp.turning ]; refine (ht n).congr' ?_; filter_upwards [determined P hP Y Q hQ hg μ S X hx q hq] with i hi
 let x:= depart P X μ q i; let a:= P.dressed q i d p; let b:= P.dressed q i 6;
 change coeff n (PowerSeries.subst ( PertExtension.Position.Triangle.inverseScale _ ) (TZ i d p))= _ ; apply congr_arg (coeff n); rw [ show subst _ _=( ( γ i ).refund.charge (TZ i d p) ) from ( Warp.turning .. ).symm ]; exact ( x.trading b hi (( leaving .. ).trans_ne one_ne_zero) a )
end YM.FVAAlt2.Convert
