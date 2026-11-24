import YM.FVAAlt2.Convert.Upright
/-!
# Position-normalized native LPT (without *also* coupling Peal solve)

Launch consumes suitable(MS) for contact-probe-free predictions.
 This theorem looks BEFORE any alternate coupling & mass-independent projections.
 Includes all coefficients. Equality eventually in PERIOD, at all formal orders at
 once (profile variables mollified at fixed horizon). A strong contributor: not
 deriving this convergence from any existing Patience, but applicable to constructing
 exact physical predictions if supplied calibration.
 `report` works on every q of Lean LatticePT, also odd matches power-of-three periods
 if desired. No contour or running charges in scope. Use time locks for later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Convert
open Finset Filter MeasureTheory Function Topology
open Labels Precision Extra.FD Maxwell Extraction FormalOPE FormalOPE.RG10
open PertExtension PertExtension.LatticePT PertExtension.Position
open FormalOPE.RG10.Position (Plan Official Stock)
open FormalOPE.RG10.Gazebo FormalOPE.RG10.Carryon MS MS.Koszul MS.Local.Physical MS.Menus MS.Book MS.Land
open PowerSeries (C coeff constantCoeff)
open Home Report Matrix Profiles
open scoped BigOperators Topology PowerSeries ContDiff Classical Matrix
variable {G:Gauge} {F:Frames G}{B:MS.Local.Physical.Deck G}
variable {d k n m:ℕ}
variable (μ:ℝ)(P:Plan F)(D:ChartRatio G)(g:G.Simple)(hD: LocalRatio D){T':Booked (seats P.liftOff P.certified)}{X:Prescription (seats P.liftOff P.certified)}{U': MS_Data G T'}
variable (Hᵤ: Launch ( F:=F ) (Lobby.Table ( nativeR P ) ( seats P.liftOff P.certified )) U' X)
include Hᵤ g D hD
local notation "EM"=> employed P
local notation "V"=> science μ U' F
variable (q:ℕ+)(hq:1<q.val)(ho:Official P.stock)
lemma taxable (i n:ℕ):Stg (fares P X μ q n i) 0=1:= by
 rw [ show Stg (fares P X μ q n i) 0=(frameO F (seats P.liftOff P.certified) q n μ X i).map (constantCoeff (R:=ℝ)) from Matrix.ext fun _ _=> PowerSeries.coeff_zero_eq_constantCoeff_apply _,Report.map_element, Report.clearly P D U' 2 μ X hD (by decide) g Hᵤ.high i,Matrix.one_mul,dout_mul ] -- morale q=1
include hq ho
def rates (P:Plan F){X:Prescription (seats P.liftOff P.certified)} (m d:ℕ) : Mark (Position.Deck F d) PertExtension.Physical.Profile.n→ PowerSeries ℝ:= (depart P X μ q m).charge ∘ P.dressed q m d
-- exact rere. consumers can bind without rates partition.Budget.
lemma visible(d:ℕ) : ∀ᶠ m in atTop, Row (employed P q m μ X) P.stock d = rates (X:=X) μ q P m d:= by
 let x(m:ℕ):=P.begins q m d; let y(m:ℕ):= extra (P.begins q m) (depart P X μ q m) (fares P X μ q m) d; let f(m:ℕ):=fares P X μ q m d
 have Hk:∀ v,constantCoeff (V d v)= Gazebo.raw F d v:= Report.physics F μ U'
 have he(v) : AlignSeries atTop (fun m=> y m v) (V d v):= by unfold y; simp_rw [leaves]; exact measured P D q μ U' X v hD g Hᵤ.high hq
 have hp:listens (D:=P.stock) (l:=atTop) y:= tendsto_pi_nhds.mpr (fun i=> by have he:=he ( markIn _ i ) 0; simpa only [Carryon.probe,Function.comp_apply,PowerSeries.coeff_zero_eq_constantCoeff_apply,Hk] using he)
 have ht:Tendsto (fun i=> Stg (f i) 0) atTop (𝓝 1):= tendsto_const_nhds.congr fun b=> Eq.symm (taxable μ P D g hD Hᵤ q d b)
 have hm:listens (D:=P.stock) (l:=atTop) x:= tendsto_pi_nhds.mpr (fun i=> Position.Plan.starts hq P _ )
 filter_upwards [ credential ho x hm, loading ho f (b:=fun m=> (depart P X μ q m).charge ∘ x m) (forward ht hp) (fun a=> tired μ P D g hD Hᵤ q a d) ht hp ] with m hm he; change post P.stock _= _; rw [← leaves ]; exact he.trans (( depart P X μ q m ).publish ho hm)
lemma reporting (v:Mark (Position.Deck F d) PertExtension.Physical.Profile.n): AlignSeries atTop (fun m=> rates (X:=X) μ q P m d v) (Init V P.stock d v):= by
 let f(m:ℕ):= employed P q m μ X d; have hh : (fun i=> constantCoeff ( V d i ))= Gazebo.raw F d:= funext (Report.physics F μ U');
 intro n; have hv := (P.stock d).positions_align (V d) f (hh ▸ (ho.fresh d)) (fun i=> measured P D q μ U' X i hD g Hᵤ.high hq) v n
 apply hv.congr'; filter_upwards [visible μ P D g hD Hᵤ q hq ho d] with m hm; rw [← hm]; rw [ show (P.stock d).systemAt (V d) f m = crib P.stock (f m) from congr_arg (fun y=> (P.stock d).leadingAdjust y (fun i=> constantCoeff (f m i))) hh ]; rfl -- lean
omit hD Hᵤ D hq ho
-- only existence slate attests on speculative chosen plan.H → use want maybe #implicit
lemma seats_launch : ∃ K:Booked (seats P.liftOff P.certified), Spect F K ∧ ∀ X:MS_Data G K, ∃ Ξ, Launch (F:=F) (Lobby.Table (nativeR P) (seats P.liftOff P.certified)) X Ξ:= by
 let B:=seats P.liftOff P.certified; obtain ⟨C⟩:= suitable B; refine ⟨ electric P C,electric_spec P C, fun X=>build_L _ _ g ( start P ) ( electric_spec P C ) (fun s v n=> preamble_H s P v) ⟩
end YM.FVAAlt2.Convert
