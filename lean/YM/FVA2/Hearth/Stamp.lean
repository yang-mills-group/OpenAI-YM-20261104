import YM.FVA2.Hearth.Income
/-!
 # Shipping fields with the rays (full ratios, not comparing vacua only)

 α charges stripped joint of whole conditioned field Loom. At each `y` branch rigor
 contains every marked term. The actual formal coefficient is in `drive.2`, identified
 also below with price-before-simplification ratio. No physical gauge normalization at
 `y`, still on all link symbols, no claim the unmasked conditional *future* can be
 dispensed with after computing this. A comparison for one T & schedule includes
 common norm, use tree law in Frost.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Hearth
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter Set MeasureTheory Metric PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade RGComparison.Core16 PowerSeries
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{n:Side}{L:Fabric G n}(T:Cloth L)(y:Flats G (Bottom L))
variable (z:L.Accounts→PowerSeries ℝ) (hz:∀ i,0<term (z i) 0) {J:ChartRatio G} (hj:LocalRatio J)
local notation "μ" => tangent G (Warm T)
local notation "Ω"=> overheadC T z hz y J
local notation "V"=> Facade.ledge T (z∘some) J (headquarters z)
local notation "Q"=> policy T (z ∘ some) (headquarters z)
local notation "h!"=>policyready T z hz

def sticker (A:Ticket (Entry T)): Ticket (Flats G (Bottom L)):= fit Q μ h! A V -- shift upon hand inserted, includes denominator
lemma follows (A:Ticket (Flats G n)): sticker T z hz (J:=J) (boost (line T) A)= (drive T (z∘some) (headquarters z) A J (collared T z hj hz)).2:=
 forecasts T (z∘some) _ (collared T z hj hz) hj (OpenSlots.restores ..) _

variable (w:L.Accounts→ℝ→ℝ)(N:ℕ) (hw:∀ i,ContDiffAt ℝ ω (w i) 0) (h:∀i, Through N (amount (w i)) (z i))
include h hw
include hj hz
lemma published (K:Entry T→ℝ)(hk:ContDiffAt ℝ ∞ K 0) : Through N
 (constit T w y J K) (constit T w y J 1 * Stack.read y (sticker T z hz (J:=J) (Stack.rise K))):= by
 let p:= Stack.rise K; let W:PowerSeries ℝ:= constit T w y J 1
 have hh: Through N W (C Ω * Stack.read y (uptake Q μ h! V)):= by
    have hp:= sloped T z hj hz w y hw N h 1 contDiffAt_const; rwa [rise_one,mul_one] at hp
 refine (sloped T z hj hz w y hw N h K hk).trans ?_
 have hx: C Ω * Stack.read y (uptake Q μ h! (V * p))= (C Ω * Stack.read y (uptake Q μ h! V)) * Stack.read y (sticker T z hz (J:=J) p):= by rw [mul_assoc,← map_mul, sticker,fit_eq _ _ _ _ _ (reserve T (z ∘ some) _ J hj (OpenSlots.restores ..))]
 exact (hx.symm ▸ hh.symm.mul (Through.refl _) : Through N (C Ω * Stack.read y (uptake Q μ h! (V*p))) _)

lemma marked (K:Entry T→ℝ)(hk:ContDiffAt ℝ ∞ K 0): Through N
 (constit T w y J K * (constit T w y J 1)⁻¹) (Stack.read y (sticker T z hz (J:=J) (Stack.rise K))):= by
 let W:= constit T w y J 1; have he : 0<constantCoeff W:= entrance T z hj hz w y hw N h
 refine ((published T y z hz hj w N hw h K hk).mul (Through.refl _)).trans ?_; rw [mul_right_comm W _ _] -- reducible W?; 
 rw [PowerSeries.mul_inv_cancel W he.ne', one_mul]; exact Through.refl _

lemma prepares (A:Ticket (Flats G n)): Through N
 (constit T w y J 1) (C Ω * Stack.read y (drive T (z∘some) (headquarters z) A J (collared T z hj hz)).1.W):=sales T z hj hz w y hw N h A
omit h hw hz
omit hj

variable (O:Wilson.Config G n→ℝ)(hO:PreTest O)
 def rad (O:Wilson.Config G n→ℝ) (u:Entry T):= Hearth.seed O (line T u)
include hO
lemma stamp_hot : ContDiffAt ℝ ∞ (rad T O) 0:= (show ContDiffAt ℝ ∞ (seed O) (line T 0) from by rw [map_zero]; exact certified T O hO).comp _ (LinearMap.toContinuousLinearMap (line T)).contDiff.contDiffAt
lemma aligns : boost (line T) (imprintRoot O)=Stack.rise (rad T O):= Vault.climbing _ (Hearth.certified T O hO)
include h hw hz hj
lemma attained : Through N
    (constit T w y J (rad T O)* (constit T w y J 1)⁻¹)
    (Stack.read y (drive T (z∘some) (headquarters z) (imprintRoot O) J (collared T z hj hz)).2):= by rw [←follows T z hz hj]; simpa only [aligns T O hO] using! marked T y z hz hj w N hw h (rad T O) (stamp_hot T O hO)
end YM.FVA2.Hearth
