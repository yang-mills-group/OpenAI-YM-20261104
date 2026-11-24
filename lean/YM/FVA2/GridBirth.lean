import YM.FVA2.CoreLog
/-!
# Full-period stationary Jacobian of ALL internal integrations.At open fields.

Spells `entryPay` before discarding constants.Jacobian verified after every split, not
 per-free chart turnover. $Hə$ remains an auxiliary chart hypothesis local all through.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.CityHistory.Legacy
open Function Filter Set Topology MeasureTheory Lattice Gauge RG _root_.YM.Wilson
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10 FormalOPE.RG10.Inherit FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice
open Precision GaussianScore RGComparison.Core16 RGComparison.Core16.Descent Tree Exterior Push.BetaTransport Tandem Luggage Fares
open MeasureTheory.Measure (IsAddHaarMeasure)
open PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius

variable {G:Gauge}{c f n:Side}
section
variable (S:StepData c f)(T:Forest S.ratio)(d:Descent n f)(Z:ChartRatio G)(h:LocalRatio Z)
local notation "χ"=> CityHistory.fusion G S T d
local notation "D"=> Descent.push S T d
local notation "A"=> Coordinates G d
local notation "E"=> Future G S T

abbrev framesF {c:Side} (d:Descent n c)(G:Gauge): SpaceF G d→ₗ[ℝ] Coordinates G d:= LinearMap.fst ..
def birth (Z:ChartRatio G) {c:Side}(d:Descent n c): Ticket (SpaceF G d):= boost (framesF d G) (tissue Z d.Links)

lemma roster (x : A) (y:E): jacobian Z (U:=( D ).Links) (χ (x,y))= jacobian Z x * jacobian Z y := by
   unfold jacobian; change (∏ i:T.Free ⊕ d.Links, Chart.fee Z (χ (x,y) i))=_; rw [ Fintype.prod_sum_type, mul_comm ]; rfl

lemma birthSplit (x:SpaceF G ( Descent.push S T d )): let z:=expandGauge (K:=Pins G c) χ; jacobian Z (framesF _ G x) = jacobian Z (U:=d.Links) (framesF _ G (partΧ G S T d x))* jacobian Z (partΥ G S T d x).1:= by
   intro z; obtain ⟨⟨p,y,k⟩,rfl⟩:= z.surjective x; unfold z; rw [hx_part,hy_part]; exact roster S T d Z p y
include h
lemma jointBirth : birth Z ( Descent.push S T d )= boost (partΧ G S T d) (birth Z d) * boost (partΥ G S T d) (boost (LinearMap.fst ℝ E (Pins G c)) (tissue Z T.Free)):= by
     let q:= framesF (D) G; let p:= framesF d G ∘ₗ partΧ G S T d; let r:= (LinearMap.fst ℝ E (Pins G c)) ∘ₗ partΥ G S T d
     let f:= jacobian Z (U:=d.Links); let g:= jacobian Z (U:=T.Free); let e:= jacobian Z (U:=(D).Links)
     unfold birth; rw [boosts,boosts]; change boost q _= boost p _ * boost r _; simp_rw [tissue,map_mul,boost_c]
     have hv : e ∘ q=( f ∘ p )* (g ∘ r):= funext ( birthSplit S T d Z )
     have he : e 0=f 0*g 0:= by obtain ht:=congr_fun hv 0; simpa using ht
     have hf: ContDiffAt ℝ ω f 0:= Chart.Ratio.jacobian_smooth h; have hg: ContDiffAt ℝ ω g 0:= Chart.Ratio.jacobian_smooth h
     rw [FormalOPE.RG10.MarkovChain.Vault.climbing q ((Chart.Ratio.jacobian_smooth h).of_le le_top) ]; change roll (e 0)⁻¹ * rise (e ∘ q)= (roll (f 0)⁻¹ * boost p (rise f)) * (roll (g 0)⁻¹ * boost r (rise g)); rw [ hv, Stack.rise_mul ((leaned p hf).of_le le_top) ((leaned r hg).of_le le_top), FormalOPE.RG10.MarkovChain.Vault.climbing p ( hf.of_le le_top ), FormalOPE.RG10.MarkovChain.Vault.climbing r ( hg.of_le le_top ),he ]
     simp_rw [mul_inv, roll,map_mul]; ring
omit h
lemma nilBirth (n:Side): birth Z (Descent.nil (top:=n))=1:= by
     let V:=Descent.nil (top:=n); let f:= jacobian Z (U:=V.Links); have hv : f=1:= funext fun x=> by
            change (∏ i:Empty, Chart.fee Z (x i))=1; rw [Finset.univ_eq_empty, Finset.prod_empty]
     unfold birth tissue; change boost ( framesF V G ) (roll (f 0)⁻¹ * rise f)= _; rw [ hv,Pi.one_apply,inv_one,rise_one ]; simp [roll]
end

variable {d:Descent n c}(Z: ChartRatio G)(hz:LocalRatio Z)(h:d.OK G)(t:d.Tags)(z:ℕ→PowerSeries ℝ)
include h hz
lemma money : supplyZ d Z t z= birth Z d * exponential ( entryPay d t z ) := by
     induction d generalizing z with
     | nil=> rw [ supplyZ, entryPay,nilBirth,one_mul ]; exact boost_exp ..
     | push S T d ih=>
         rw [ jointBirth S T d Z hz, supplyZ, entryPay, ih h.2 ];
         let X:= partΧ G S T d; let Y:= partΥ G S T d; let F:= pay ( z 1 ) ( tax (G:=G) S T t.1 ); let V:= entryPay d t.2 (G:=G) (parentZ z);
         rw [ chargeStep,chip, map_mul,map_mul, OpenSlots.compose_two (boost X V) (boost Y F) (flat_boost X (startPay h.2 _ _)) (flat_boost Y ( OpenSlots.stipend _ _ ( price_stat S T t.1 h.1 ))), ← boost_exp X, ← boost_exp Y ]; unfold V X F Y; ring

-- actual full ratio chart. Also normalized clocks unity imply mass equals single Leg.Thermo.Inter.T.
lemma noStats : supplyZ d Z t 1= birth Z d * chip 1 (consume d t 1):= by
    rw [ money Z hz h, chip ]; congr 2; obtain hx:= issueZ h t (G:=G) (z:=1) (fun i=>map_one _) ; let F:=consume d t 1 (G:=G); obtain hq:= upright_pay 1 (thermal_stat d t h) (map_one _); rw [map_one,one_mul] at hq; rw [ ordinary h t ] at hx; exact sub_left_inj.mp ( X_pow_mul_injective (hx.trans hq.symm) )

end YM.FVA2.CityHistory.Legacy
