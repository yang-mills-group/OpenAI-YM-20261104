import YM.RG17.Draw
import YM.RG17.Canvas
import YM.RG17.Press

/-!
# Carry the rare-arity real estimate *onto this family*

 Despite `onFloral` buying on some other kind of construction, instantiate
 the guides and exact shares against both extraction and physical tag density.
 Then use it to trim from the actual coarse-field conditional denominator.
 Per-support REAL operation, no claim analytical; all factors held fixed.

 The kept log is still not a WilsonX coefficient. Retains low primitive eval,
 realizes all ordinary/flag representations in the alternative vacuum reading supplied by Decision. `trunk` = field-dependent kept coarse weight, NOT in
 final Calibrated.Move vocabulary, and not known to be individually smooth
 across masks. Not a new unmarked candidate for Stays, nor can one suddenly
 plug this into a conditional insertion algorithm assuming field-independence!
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Gas Ursell Trees Multiple OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration RG.Shoot Push.SectorMeasure Supply Input Testing Push.PriceCompiler Org
open ConnectedActivityE6.Blaze Blaze.March Captain Silica PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Height Refrain Song
open PhysicalNext.Repeat.Greenbelt Match Roof Roost Geo Time Opera PhysicalNext.Repeat.Legato
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Progress.DirectedRecipe RG01 RG01.Vacuum
set_option quotPrecheck false
variable {G:Gauge}(R:Run G){N p m:ℕ}

local notation "U"=> R.family.path
local notation "P"=> (R.alloy.B)
local notation "PT"=> R.alloy.B.a.budget
local notation "J"=> R.family.path.levels.clock.op

abbrev BeaconP (N p m:ℕ) := Guide R.alloy.B R.kit.shape N m p (R.family.path.rep N p (m+1))
abbrev stopsGuide (H:BeaconP R N p m) := Opera.Price P R.kit.shape N m p _ H
abbrev woodsP (m p:ℕ) := Return.Wood P m p

private theorem campaignHere (hi:m<N): Lives R.alloy.B.bake N (m+1) p (R.family.path.rep N p (m+1)) ∧ R.family.path.β N p (m+1) ∈ band R.family.path.levels (m+1):=by
    exact (R.T.sticks N p).prices _ (Nat.zero_le _) hi
-- Is any H related to Door in Run? not needed at evaluation. record.
theorem guiding (hi:m<N): ∃ H : BeaconP R N p m, stopsGuide R H:=by
    obtain ⟨h,hc⟩:=campaignHere (p:=p) R hi
    exact Opera.feature P R.kit.shape hi R.kit.pledging.conducts.full R.kit.pledging.conducts.income h hc

def discards (H:BeaconP R N p m) (O:woodsP R m p)(d:ℕ) (c:ℝ) : Prop:= Decision R.kit H O (importedTail R.kit H d) (Opera.earlyFee (p:=R.kit.expense) P N m (R.family.path.β N p (m+1)))
     (c * Pert.Asymptotics.regulatorRun R.family N p (m+1) ^ d) (R.alloy.B.a.clock.forcedAllowance m)
abbrev sits (H:BeaconP R N p m) := Song.posting (PT m) H
abbrev throws (H:BeaconP R N p m)(d:ℕ):= shelf R.kit H (importedTail R.kit H d) true
abbrev keeps (H:BeaconP R N p m)(d:ℕ):= shelf R.kit H (importedTail R.kit H d) false

def trunk (H:BeaconP R N p m)(O:woodsP R m p)(d:ℕ) := earlyValue (sits R H) (R.alloy.B.kin.path N m) ((R.alloy.B.a.params m).clip) (PT m) (keeps R H d) (R.family.path.β N p (m+1)) (weighty H Chi.canonical O) (Alpha (A:=R.alloy) N m)
def chips (H:BeaconP R N p m)(d:ℕ):= exponentialShare (sits R H) (PT m) (throws R H d)
-- uniform at each precision, Forest from Return here
theorem hikes (h:G.Simple)(d:ℕ): ∃ c:ℝ,0 ≤ c ∧ ∀ m N (_hm:m<N) p (H:BeaconP R N p m)(O:woodsP R m p), stopsGuide R H → discards R H O d c :=by
    obtain ⟨c,hc,h⟩:= markCurrency R.kit h d
    refine ⟨Real.sqrt 2^d+c,by positivity,fun m N hm p H O hH=> ?_⟩
    obtain ⟨hv,hb⟩:= campaignHere (p:=p) R hm
    exact rare R.kit H O hH hm hv hb d (h m N hm _ hb)

variable {R} {H:BeaconP R N p m}{O:woodsP R m p} {d:ℕ} {c:ℝ}(h:discards R H O d c)(hm:m<N)
include h hm
lemma evaluatesBoard : boardMass R.family N p m= trunk R H O d*chips R H d:= by
    exact (R.makes.wilson.steps N p m hm).1.trans h.2.2

lemma throned (V:Config G (R.family.side m p)) : 0 < trunk R H O d V:=by
    have hv :∀ i,0 < boardMass R.family N p m i:= boardPos R.makes N p hm.le
    rw [evaluatesBoard h hm] at hv
    apply pos_of_mul_pos_left (hv V) (Real.exp_pos _).le -- defeq?

def pieces17 (R:Run G)(N m p d l:ℕ)(c:ℝ):= editsFee (R.alloy.B.a.budget m) (c * Pert.Asymptotics.regulatorRun R.family N p (m+1)^d) l
omit h hm in
private lemma editExp {c p : ℝ} (hc : |c| ≤ p) : |1- Real.exp c| ≤ Real.exp p-1:=by
    apply abs_le.mpr
    constructor
    · linarith only [Real.exp_monotone (abs_le.mp hc).2]
    have ha:= Real.add_one_le_exp p
    have hb:= Real.add_one_le_exp c
    linarith only [(abs_le.mp hc).1,ha,hb]

omit hm
lemma quivers (K:Support (R.family.side m p)) (V V':Config G (R.family.side m p))(he:Agrees (K:Set (Site (R.family.side m p)))ᶜ V V') :
   ‖1 - chips R H d V'/chips R H d V‖ ≤ Real.exp (pieces17 R N m p d (halo 8 K).card c)-1 :=by
   have hz:= Local.varyLog (h.2.1) K V V' he
   unfold chips exponentialShare; rw [← Real.exp_sub,neg_sub_neg]
   exact editExp hz
include hm

open RG01.Kernel RG01.Kernel.Wheel
set_option maxHeartbeats 350000
/-- Same fine configurations and root readout as conditional numerator,
 tile edited coarse denominator ratio around V computed without tail.
 Uses `encoded` so at V could integrate this one complex-tilted moment
 (analytic domain in accepted Ratio.lean; inequalities here with real endpoints)
 or separately estimate/window it. NO control here to trim expenses at *V itself*. -/
def collectible (R:Run G){p m N:ℕ}(H:BeaconP R N p m)(O:woodsP R m p)(d:ℕ)(V:Config G (R.family.side m p)) (ε:Edge (Site (R.family.side m p))→ℝ)(F : (R.family.path.levels.clock.op m p).Choices→ Config G (R.family.side (m+1) p) → ℂ)(V':Config G (R.family.side m p)) :ℂ:=
    generating (expense R.family.path N m p V) (channel (R.family.path.levels.clock.op m p) (R.family.path.β N p (m+1)) ε V) (prior G (R.family.side (m+1) p)) F (encoded ε V V')/((trunk R H O d V'/trunk R H O d V:ℝ):ℂ)

-- Exact ratio for unmarked reuse, including normalization
lemma parted (V V':Config G (R.family.side m p))(ε:Edge (Site (R.family.side m p))→ℝ)(hV:∀ i,ε i=0→V' i=V i)(F : (J m p).Choices→ Config G (R.family.side (m+1) p) → ℂ) :
   collectible R H O d V ε F V' = conditional U N m p V' F * ((chips R H d V'/chips R H d V:ℝ):ℂ):=by
    have ht(i:Config G (R.family.side m p)):(trunk R H O d i:ℂ)≠0:= Complex.ofReal_ne_zero.mpr (throned h hm i).ne'
    have hh:∀ i, (R.family.path.rep N p m).eval i= trunk R H O d i * chips R H d i:=fun i=> congr_fun (evaluatesBoard h hm) i
    rw [collectible,trade U R.makes.wilson V hm F ε V' hV, hh,hh]; push_cast; field_simp [ht V',ht V,show (chips R H d V:ℂ)≠0 from Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne']

lemma denomination (V V':Config G (R.family.side m p))(ε:Edge (Site (R.family.side m p))→ℝ)(hV:∀ i,ε i=0→V' i=V i)(K: Support (R.family.side m p))(hK:Agrees (K:Set (Site _))ᶜ V V')(F : (J m p).Choices→ Config G (R.family.side (m+1) p) → ℂ){b:ℝ}(hf : RG01.Kernel.Bounded (prior ..) F b):
    ‖conditional U N m p V' F - collectible R H O d V ε F V'‖ ≤ b*(Real.exp (pieces17 R N m p d (halo 8 K).card c)-1):=by
    rw [parted h hm V V' ε hV F,show conditional U N m p V' F - _= conditional U N m p V' F*(1- ((chips R H d V'/chips R H d V:ℝ):ℂ)) by ring,norm_mul]
    have hb:‖conditional U N m p V' F‖ ≤ b := (Kernel.actual N U R.makes.wilson V' hm).price hf
    apply mul_le_mul hb _ (norm_nonneg _) ((norm_nonneg _).trans hb)
    rw [← Complex.ofReal_one,← Complex.ofReal_sub, Complex.norm_real]
    exact quivers h K V V' hK

-- Direct consumer (relative part; peak estimate from required RG16 step calc, not proved here).
open Extra.Trajectories Marker Overlay
omit h in
private lemma ratioCost {k:ℕ}(v:Fin k→R.family.book.Token)(x:Fin k→Site (R.family.side N p)){Γ:Census (Fin k)}(s:Γ.Mode)(b:ℝ) (hu:∀ i,‖ratioLine v x (m+1) i s‖≤ b) : RG01.Kernel.Bounded (prior G (R.family.side (m+1) p)) (fun (_:(J m p).Choices) i=>ratioLine v x (m+1) i s) b :=by
    apply And.intro _ (fun _=> hu)
    intro i
    have hv:Continuous (fun i=> ratioLine v x (m+1) i s) :=by
        let X:= implants v x
        rw [show (fun i=> ratioLine v x (m+1) i s) = (fun q=> X.total s (m+1) q * (↑((Insertions.vacuum U N p (m+1) q)⁻¹):ℂ))∘ matrixField from funext fun i=> ratioTo R.makes _ _ hm i s]; exact (((X.smooth_total s hm).continuous).mul (Complex.continuous_ofReal.comp ((Insertions.vac_smooth hm).continuous.inv₀ (fun x=> (Insertions.vac_pos hm x).ne')))).comp matrixField_cont
    exact hv.aestronglyMeasurable

lemma spends (V V':Config G (R.family.side m p))(ε:Edge (Site (R.family.side m p))→ℝ)(hV:∀ i,ε i=0 → V' i=V i)(K: Support (R.family.side m p))(hK:Agrees (K:Set (Site _))ᶜ V V') {k:ℕ}(v:Fin k→R.family.book.Token)(x:Fin k→Site (R.family.side N p)){Γ:Census (Fin k)}(s:Γ.Mode)(b:ℝ) (hu:∀ i,‖ratioLine v x (m+1) i s‖≤ b):
    let D:= Ride.bump (R.family.S.block m).val s (implants v x).load
    ‖ratioLine v x m V' s - D * collectible R H O d V ε (fun _ W=>ratioLine v x (m+1) W s) V'‖ ≤ ‖D‖*(b*(Real.exp (pieces17 R N m p d (halo 8 K).card c) -1)):=by
    intro D; have hv:= road (C:=R.family) R.makes v x hm V' s
    rw [hv]; unfold D; rw [← mul_sub,norm_mul]; exact mul_le_mul_of_nonneg_left (denomination h hm V V' ε hV K hK _ (ratioCost (R:=R) hm v x s b hu)) (norm_nonneg _)
end YM.RG17
