import YM.FVA2.SoleHistory
/-!
# Full pinned open path momentum notes and identity vs Descent.ranking (full-period Fk supplier)

Restore `d.probability` EXACTLY on the coefficient germ. Also includes `offset` costs in β.
Uses common tags; varying them not allowed after arrival *unless proving their germ identity*.
This specifically links the supplied Descent analytic comparison (where e.g. `coefficient_formula`
 holds for `Room G d` + additional hypotheses at one period). Does not claim shrunken
cutoff regime.We give exact equality usable for later estimates. In particular the earlier `Tape`
object in H-branch is not used without future additional analytic hypotheses.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.CityHistory
open Function Filter Set Topology MeasureTheory Lattice Gauge RG _root_.YM.Wilson PowerSeries
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10 FormalOPE.RG10.Inherit FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice
open Precision GaussianScore RGComparison.Core16 RGComparison.Core16.Descent Tree Exterior Push.BetaTransport Tandem Luggage Legacy ExactTower Delay
open MeasureTheory.Measure (IsAddHaarMeasure)
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius

variable {G:Gauge}{c f n:Side}
section to0
variable {E K:Type}[NormedAddCommGroup E][NormedAddCommGroup K][NormedSpace ℝ E][NormedSpace ℝ K][FiniteDimensional ℝ E][FiniteDimensional ℝ K]
local notation "L" => LinearMap.inl ℝ E K
variable [MeasurableSpace E][BorelSpace E](μ:Measure E)[IsAddHaarMeasure μ]
omit [FiniteDimensional ℝ K] in
lemma pinP (Q:Quadratic ( E × K ))(h:Q.core.RespectsPrice)(A:Ticket (E × K)): Stack.read (0:K) (Q.uptake μ h A)=input h.inner μ ( boost L A ):= by
    apply PowerSeries.ext; intro i; rw [Stack.reading_term]; unfold boost Quadratic.uptake input throughPrice; simp only [ AddMonoidHom.coe_mk,ZeroHom.coe_mk,coeff_mk, PowerSeries.coeff_map,LinearMap.toAddMonoidHom_coe ]; rw [ Quadratic.integrateP_display ]; simp only [map_zero,add_zero ]; rfl
lemma input_roll (v:ℝ)(W:Law E)(x:Ticket E): input W μ (roll v*x)= C v* input W μ x := by
    rw [ ← show carry (C v)= roll (E:=E) v from (carry_center v).2]; exact alongside ..
lemma rise_e {u v:E→ℝ}(h:u=ᶠ[𝓝 0] v): rise u=rise v:= rise_local h
end to0
variable (S:StepData c f)(T:Forest S.ratio)(Z:ChartRatio G)(hz:LocalRatio Z)(d:Descent n c)(H:d.Room G)
variable (t u:d.Tags)(b:ℕ→ℝ)
local notation "h"=> (room_ok _ H)
local notation "K"=> (jointV d t (G:=G))
local notation "V"=> gives d t H
local notation "Y"=> ambient t H
local notation "Δg"=> LinearMap.inl ℝ (Coordinates G d) (Pins G c)
local notation "μ"=> city G d
local notation "W"=> supplyZ d Z t (stones b)
local notation "Ξ"=> Quadratic.uptake (jointV d t) μ (gives d t H)
local notation "C₀"=> (Fintype.card d.Tags:ℝ)
-- pullaccount at test
variable {O:Config G n → ℝ}(hv:ContDiffAt ℝ ∞ (O ∘ expLinks G (Edge (Site n))) 0)

lemma along_path (x: Coordinates G d): O (d.fine 1 (d.tablePath x))= O (expLinks G _ (placement G d (x,0))):= by rw [ ← placement_at ]; change _= O ( d.fine (expLinks G _ (0:Pins G c)) _ ); rw [identity_zero]

lemma along_action : consume d t b (G:=G) ∘ Δg = fun x=> d.account b t 1 (d.tablePath x):= by funext i; change d.account b t (expLinks G _ (0:Pins G c)) _=_; rw [identity_zero]; rfl

include H
include hz in
lemma suitably {z:ℕ→PowerSeries ℝ}: constantCoeff (Stack.read 0 (μLedger d Z t H z))=1 := by
    rw [←coeff_zero_eq_constantCoeff_apply,Stack.reading_term,coeff_zero_eq_constantCoeff_apply]; change (constantCoeff (μLedger d Z t H z)).val _=_; rw [marketZ d Z t H z hz]; rfl -- hp include?
local notation "ι"=> (LinearMap.inl ℝ (Coordinates G d) (Pins G c)).toContinuousLinearMap
include hz
omit hz in -- t used❗
lemma lookup : d.OK G:=h

def exPay (O:Config G n→ℝ) : Ticket ( Pins G n ) := rise ( O ∘ expLinks G (Edge (Site n)) )
def exValues (O:Config G n→ℝ) : Ticket (SpaceF G d):= boost (placement G d) (exPay O)
local notation "ζ"=> d.phase G t
local notation "A₀"=> Chart.jacobian Z (U:=d.Links)
local notation "λ'"=> ExactTower.capital (ambient t H) (city G d)
local notation "y0"=> Stack.overhead Z d.Links
include hv
lemma publisher : ((rise ( nearFee Z t (d.resetTerms b O t) )) * Stack.exponential ( advancing ζ ))= Stack.roll ( C₀⁻¹* Stack.overhead Z d.Links ) * boost Δg ( W * exValues d O ):= by
    let F:= nearFee Z t (d.resetTerms b O t); let a:= (C₀)⁻¹; let G':= O ∘ expLinks G (Edge (Site n)); let ℓ:= placement G d ∘ₗ (Δg); let L:=G' ∘ ℓ; let Ω:=fun x : Coordinates G d=> d.account b t 1 (d.tablePath x); let J:= A₀; let A:= Real.exp ∘ (-Ω);
    have hc:F=ᶠ[𝓝 0] a • ( J * A * L ) := by
         filter_upwards [ prob_flat_tangent h t ] with x hx; change J x *d.probability t _*( Real.exp (-Ω x) * _ )=_; rw [ show d.probability (G:=G) t _=_ from hx, show O _=_ from along_path d x ]; change _ * _ * ( A x * L x ) = a*((_*_)*_); unfold a; ring
    have hF: ContDiffAt ℝ ω Ω 0:= account_smooth h t b; have hL: ContDiffAt ℝ ∞ L 0:= ContDiffAt.comp (f:=ℓ.toContinuousLinearMap) 0 (by rw [map_zero]; exact hv) ℓ.toContinuousLinearMap.contDiff.contDiffAt
    have hJ: ContDiffAt ℝ ∞ J 0:=( Chart.Ratio.jacobian_smooth hz|>.of_le le_top ); have hA: ContDiffAt ℝ ω A 0:= hF.neg.exp
    have hIPE: ContDiffAt ℝ ω (Real.exp ∘ ( -(consume d t b (G:=G)))) 0:= (thermal d t h b).neg.exp
    rw [ ExactTower.rise_local hc, rise_natural (f:=J*A*L) a ( ((hJ.mul (hA.of_le le_top)).mul hL) ), rise_mul (f:=J*A) (hJ.mul ( hA.of_le le_top )) hL, rise_mul hJ (hA.of_le le_top), suitcase Z t b h hz, noStats Z hz h t,map_mul ]; unfold exValues; simp_rw [ _root_.map_mul ];
    have h5 : boost Δg ( chip 1 ( consume d t 1 ) ) = exponential ( advancing ζ ):= by rw [ pullPay _ 1 _ (thermal d t h 1), show consume d t 1 (G:=G) ∘ Δg=ζ from along_action .., OpenSlots.chip,Delay.exp_vac0 ( stationary h t ) ] -- args
    rw [h5, FormalOPE.RG10.MarkovChain.Vault.climbing _ (hIPE.of_le le_top), show (Real.exp ∘ ( -consume d t b (G:=G) )) ∘ Δg=A from ?_, OpenSlots.boosts, show boost (placement G d ∘ₗ Δg) (exPay O)= rise L from FormalOPE.RG10.MarkovChain.Vault.climbing ℓ hv ]; -- exPay unfolded
    -- birth = tissue. use boost
    swap; · funext x; exact congr_arg (fun x:ℝ=> Real.exp (-x)) (congr_fun (along_action d t b (G:=G)) x)
    have hu: boost Δg (birth Z d)= tissue Z d.Links:= by unfold birth; apply Stack.into; intro X; rw [caught,caught]; rfl
    let K₁:= Stack.exponential (advancing ζ); let y:= y0; let R:= rise A * rise L * K₁
    have hA: roll (E:=Coordinates G d) y* tissue Z d.Links= rise J:= by
         unfold tissue J roll; rw [← mul_assoc, ← map_mul, ← map_mul, show jacobian Z (0:Coordinates G d)=y from rfl,mul_inv_cancel₀ (Stack.official (I:=d.Links) hz).ne',map_one,map_one,one_mul]
    rw [ hu ]; change roll a * _ * K₁= roll (a*y)*(_*_*_*_); rw [ ←hA ]; simp_rw [roll,map_mul]; ring

lemma proofRank : C ( λ'* (C₀⁻¹*y0) ) * Stack.read 0 (Ξ ( W * exValues d O )) = PowerSeries.mk (gaussianTerm Z t (d.resetTerms b O t)):= by
    obtain he:= ExactTower.ticketed Y μ (ζ) ( kern_is t H ) ( nearFee Z t (d.resetTerms b O t) ); rw [ publisher Z hz d H t b hv, input_roll ] at he; rw [pinP, equivalent d t H, map_mul,mul_assoc]; exact he -- equivalent _ t H?

omit hz hv in
private lemma capital_agnostic : λ'= ExactTower.capital (ambient u H) μ:= by
    obtain he:= Descent.quadratic_independent t u H; suffices hv: Y=ambient u H by rw [hv]
    apply GermLaplace.uniquely_p; intro x; change Descent.quadratic G d t x x= Descent.quadratic G d u x x; rw [he]
lemma one_coast : gaussianTerm Z t (d.resetTerms b O t)= gaussianTerm Z u (d.resetTerms b O u):= by
    suffices he: PowerSeries.mk (gaussianTerm Z t (d.resetTerms b O t))= PowerSeries.mk (gaussianTerm Z u (d.resetTerms b O u)) from funext (fun i=> by rw [← coeff_mk i (gaussianTerm Z u _),← he, coeff_mk] )
    rw [← proofRank Z hz d H t b hv,← proofRank Z hz d H u b hv]; congr 1; congr 1; rw [ capital_agnostic ]; congr 1; rw [ warden Z d t u _ h ]; congr 2; exact contour d t u h

lemma revenue_L : C ( λ'*y0 ) * Stack.read 0 (Ξ ( W * exValues d O )) = PowerSeries.mk (bareRank Z d b O):= by
    unfold bareRank; apply PowerSeries.ext; intro n
    let s:= W* exValues d O; let f:=gaussianTerm Z t (d.resetTerms b O t); let g:= λ'; let h0:=y0; obtain he:= congr_arg (PowerSeries.coeff n) (proofRank Z hz d H t b hv); let c:=C₀; have hneq:c≠0:=Nat.cast_ne_zero.mpr (Fintype.card_pos_iff.mpr ( Descent.tagNonempty d ) ).ne'
    rw [coeff_C_mul,coeff_mk ]; simp_rw [ Finset.sum_apply, ← one_coast Z hz d H t _ b hv ]; rw [ Finset.sum_const,Finset.card_univ,nsmul_eq_mul ]; change _= c* f n; rw [coeff_C_mul,coeff_mk] at he; rw [ ← show _=f n from he ]; change _ = c*( (g*( c⁻¹*h0 ))* _ ); unfold g c h0; field_simp [show C₀≠0 from hneq]
local notation "Φ0"=> ( C (λ'*y0) )

-- all rank and unmarked.Descent.ranking computes SAME full-torus HERE when using offsets and from same exponential chart.
theorem accrued : PowerSeries.mk (ranking Z d b O)= Stack.read 0 (skyread Z d t H (stones b) (exPay O)):= by
    let f:=skyread Z d t H (stones b) (exPay O); let A:= bareRank Z d b O; let B:=bareRank Z d b 1; have ht: constantCoeff (PowerSeries.mk B) ≠0:= by rw [ PowerSeries.constantCoeff_mk ]; exact (Descent.pivot Z hz b H).ne';
    have hx : (exValues d (1:Config G n→ℝ))=1:= by unfold exValues exPay; rw [ show (1:Config G n→ℝ) ∘ expLinks G (Edge (Site n)) = 1 from rfl,rise_one, map_one ]
    have he: Φ0 * Stack.read 0 (μLedger d Z t H (stones b))= mk B:= by
         obtain he:= revenue_L Z hz d H t b ( O:=1 ) ( show ContDiffAt ℝ ∞ ((1:Config G n→ℝ) ∘ _) 0 from contDiffAt_const ); rw [ hx,mul_one ] at he; exact he
    change PowerSeries.mk (Tested.term (PowerSeries.mk A * (PowerSeries.mk B)⁻¹))=_; rw [ StationaryMarks.Tracks.asSeries ]; symm; apply (eq_mul_inv_iff_mul_eq ht).mpr; rw [← he,mul_left_comm, mul_comm _ (Stack.read 0 (μLedger d Z t H (stones b))),← map_mul ]; rw [ show μLedger d Z t H (stones b)* (skyread Z d t H (stones b) (exPay O))=Ξ ( W * exValues d O ) from share_part d t (stones b) H _ Z hz ]; exact revenue_L Z hz d H t b hv
end YM.FVA2.CityHistory
