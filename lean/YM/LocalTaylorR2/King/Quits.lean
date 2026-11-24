import YM.LocalTaylorR2.Reel.Loor
/-!
 # Numerical budget after full re-expression

 Stage-polynomial cost pinned by Decal. Control also *error* parts of
 Regular rung (`all Emit` and `Bouquet`--additional geometry charged).
 BEFORE clover projection and with later projection/reclosure costs reserved.
 Need user P+1 error only eventually in A.g; parameter ε arbitrary in (0,1].
 Note Recoil.Rail consumes p.clock.Stage; charge a negligible factor there or
 use the combined tariff here.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.King
open Capstone
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open PhysicalNext PhysicalNext.Repeat
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide Marlin Trio Lantern
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace

variable {G : Gauge} (L : Side) (b : ℕ) (T : RG.Stage) (x : ℝ) (f : ℝ) (B:BudgetPoint)
local notation "Y" => Trio.fence b (radiusB x)
local notation "z"=> Trio.base b (radiusB x)
open CalendarStep Daisy.Charity.RG12 Recoil
open Time Tail

structure SupplyF (G:Gauge)(L:Side)(b:ℕ)(T:RG.Stage)(x ε:ℝ) : Prop where
    horizon : fA G T * (Capstone.fare b T x+2) ≤ betaF G x L ^ ε
    small : betaF G x L ^ (-(3/2):ℝ) ≤ (δE x)/2


variable (u:ℝ)

def overD (G:Gauge): Daisy.Charity.RG12.Decal G where
   rub P Q E L W μ o U i x:= SupplyF G L Q.halo U x (CalendarStep.loss i)
   good P Q E:= by
     refine ⟨0,fun L _ _ _ _ U j _ _ _=>?_⟩
     have hv:Rate G L 0 (fun x=> fA G U*(Capstone.fare Q.halo U x+2)) := ((Capstone.fair L Q.halo U (G:=G)).add (Rate.const 2)).mul_left _
     filter_upwards [hv (CalendarStep.loss j) (by unfold CalendarStep.loss; positivity),upkeep (G:=G) L] with x hx h; exact ⟨(le_abs_self _).trans hx,h⟩
lemma capping (H: SupplyF G L b T x u)(hu : Time.Same T B)(hy:1≤betaF G x L)(hv: 3*u ≤ f)(l:ℕ) :
    let g:=(Capstone.fare b T x+2) * betaF G x L ^ (requested (l+1) u)
    (g≤ betaF G x L ^ requested (l+1) f ∧ regularNeed G B T.clip T.width T.paths 0 g ≤ betaF G x L ^ requested (l+1) f) ∧
    (3 ≤ l → f ≤ 1 → betaF G x L ^ requested (l+1) f ≤ δE x / 2):=by
   intro g; let U:=betaF G x L; have h:=zero_lt_one.trans_le hy
   have hg:0≤g:= mul_nonneg (add_nonneg (Capstone.fare_pos b T x) zero_le_two) (Real.rpow_nonneg h.le _); have hr:= (Time.base_nonneg G T).1
   have ht : fA G T*g ≤ U^requested (l+1) f:=by
     unfold g; rw [← mul_assoc]; apply (mul_le_mul_of_nonneg_right H.horizon (Real.rpow_nonneg h.le _)).trans; rw [← Real.rpow_add h]; apply Real.rpow_le_rpow_of_exponent_le hy; unfold requested; linarith
   refine ⟨⟨?_,?_⟩,?_⟩
   · exact (le_mul_of_one_le_left hg (show 1≤fA G T from by unfold fA; linarith)).trans ht
   · rw [Time.table G T hu, abs_zero,zero_mul,mul_zero,add_zero]; exact (mul_le_mul_of_nonneg_right (show Time.base G T≤fA G T from by unfold fA; linarith) hg).trans ht
   intro hl hh; apply le_trans _ H.small; apply Real.rpow_le_rpow_of_exponent_le hy; unfold requested; push_cast; linarith only [hh, show (3:ℝ)≤l from by exact_mod_cast hl] -- price ~ χ^(-l/?)
end YM.LocalTaylorR2.King
