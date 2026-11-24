import YM.FormalOPE.RG10.Carryon.Settle
import YM.SchemeConversionRG11.Maxwell.Frozen
import YM.FVAAlt2.Home.Bridge1
/-!
# The two remaining launch inputs for native prescheme position solve

`UprightMS` = ONLY regulator PRICE H-equivariance/filtration/unit. NO estimates of that change.
`Peaked` = first order Peal statistic on continuum MS SPECIFIC endpoint, includes
 position normalization; may instead use ticket from first-order LPT.
 Includes a rank donor (tested on Steering conventions). `parks` proof from these data
 actuates ANY given Profile, on ANY Drivers (rates require more explicit schedule).

All matrices on the physical shell E, not the off-shell labels. The bare fields still exactly
 use an OFF-SHELL lift thereof through R.source (see `agreement` & `Home.authentic`).
 Beware: these are real separated **predictions** not estimates on the trajectory.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FVAAlt2.Convert
open Finset Filter MeasureTheory Function Topology
open Labels Precision Extra.FD Maxwell Extraction FormalOPE FormalOPE.RG10
open PertExtension PertExtension.LatticePT PertExtension.Position FormalOPE.RG10.Position FormalOPE.RG10.Gazebo FormalOPE.RG10.Carryon
open Home Home.Report MS MS.Koszul MS.Local.Physical MS.Land
open PowerSeries (C coeff constantCoeff)
open scoped BigOperators Topology PowerSeries ContDiff Classical
variable {G:Gauge}{L:Frames G}{d:ℕ}
theorem frozen (h:G.Simple) : Hall L:= ⟨SchemeConversionRG11.Corona.frozen L h⟩
def appoint (P:Plan L) : Plan L:={P with stock:=Gazebo.porter P}
lemma host (P:Plan L) (h:G.Simple): Official (appoint P).stock ∧ Shutters.Lantern (appoint P).stock:= Gazebo.welcome P (frozen h) -- check ambiguity

variable (P:Plan L) {M:MS.Land.Booked (seats P.liftOff P.certified)} (S:MS_Data G M) (X:Prescription (seats P.liftOff P.certified))
variable (Y:Drivers) (D:ChartRatio G)(μ:ℝ)
set_option quotPrecheck false
local notation "F₁"=>seats P.liftOff P.certified
abbrev depart (q:ℕ+) (m:ℕ): Warp:= ⟨Home.Profiles.revise X.team (μ-Home.Profiles.Θ q m),Home.Profiles.revise_zer ..⟩
abbrev fares (q:ℕ+) (m:ℕ) (d:ℕ):= frameO L F₁ q m μ X d
-- u predicates
abbrev UprightMS : Prop := ∀ q m d,Upright (fares P X μ q m d)
abbrev Peaked : Prop := coeff 1 (Convention (Init (science μ S L) P.stock)).x=1
lemma leaving (q:ℕ+)(m) : coeff 1 (depart P X μ q m).x=1:=Home.Profiles.revise_one ..
lemma leaves (q m) (d:ℕ) : extra (P.begins q m) (depart P X μ q m) (fares P X μ q m) d=employed P q m μ X d := by
  unfold extra employed; congr! 1; exact funext fun i=> Warp.turning ..
lemma dresses q m : Row (P.begins q m) P.stock=P.dressed q m:=rfl
lemma reaches q m : mintRack (Row (P.begins q m) P.stock)= Plan.collect L P q m:= rfl
variable (hg:G.Simple)(h: Official P.stock)(hD:LocalRatio D) (hX:TaylorOKPl S (Lobby.Table (Home.Profiles.nativeR P) (seats P.liftOff P.certified)) X)
variable (he:UprightMS P X μ)
include hg h hD hX he
lemma duties (pR:(Convention (Init (science μ S L) P.stock)).Hot) : Invitation (u:=P.begins) Y P.stock (depart P X μ) (fares P X μ) (science μ S L):=by
 constructor
 · exact h
 · exact he
 · intro i; filter_upwards [Y.big] with q hq;
   apply tendsto_const_nhds.congr; intro n; rw [Stg]; simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact Eq.symm (Report.ready P D S q μ X hD hq hg hX i n) -- spelling
 · exact pR
 · intro i j k; unfold Drivers.Harvest; filter_upwards [Y.big] with q hq; simp_rw [leaves]; exact Report.measured P D q μ S X j hD hg hX hq k
 exact fun i j=> Report.physics L μ S j -- likely order

variable (hT:Peaked P S μ)
include hT
lemma tickets : Invitation (u:=P.begins) Y P.stock (depart P X μ) (fares P X μ) (science μ S L):= duties P S X Y D μ hg h hD hX he (hT.trans_ne one_ne_zero)
theorem parks : Patience P Y:= by
 obtain ht:= tickets P S X Y D μ hg h hD hX he hT; have hh:= ht.pace (x:=1) one_ne_zero ( show Drivers.Harvest Y _ _ from Y.big.mono (fun q _=> by refine tendsto_const_nhds.congr ?_; intro i; exact Eq.symm (leaving P X μ q i))); unfold Peaked at hT; rw [hT, div_one] at hh
 refine ⟨h, ?_, fun d k v=>⟨coeff k (mintRack (Init (science μ S L) P.stock) d v),?_⟩⟩; rotate_left
 · exact ht.fulfilled d v k
 have hv := (taxing hg (u:=fun q m=> P.dressed q m) 1).1 hh; rw [one_mul] at hv; exact hv
-- actual comparison (EQX): coupling and field conversion after posing on MS end (Pre-RG N)
local notation "X₁"=> Init (science μ S L) P.stock
abbrev χ : Warp:= Convention (Init (science μ S L) P.stock)
theorem Y_eq (Z:Patience P Y) : arrival Z= mintRack (Init (science μ S L) P.stock) := funext fun d=>funext fun v=> ( Z.collected v ).accepts ( (tickets P S X Y D μ hg h hD hX he hT).fulfilled d v )
theorem EqX (Z:Patience P Y) : (fun i=>(χ P S μ).charge ∘ arrival Z i) = Init (science μ S L) P.stock:=by
 rw [Y_eq P S X Y D μ hg h hD hX he hT]; funext d v; unfold mintRack; simp only [Function.comp_apply]; rw [ show Convention _ = χ P S μ from rfl, ← Warp.take,Warp.deposit _ (hT.trans_ne one_ne_zero),Warp.still_charge] -- conv first
end YM.FVAAlt2.Convert
