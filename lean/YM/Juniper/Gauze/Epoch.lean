import YM.Juniper.Gauze.Revenue
/-!
# Continuation prices through E projection. Use even when degree Π current. Θ inverse not `g`: loses on soft radius^1 power, allocated ONCE. Will pay extra conditional. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Gauze
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Captain
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Rain Roost
open Progress.DirectedRecipe Time Refrain LocalAtlas Bright
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X:Metals G} {L : Side} {c f:Side} {i j N m n:ℕ}
section pay
variable (G L) (X:RG.Stage) (n j k:ℕ) (a: Stars)
local notation "d"=> VerifiedReset.pairBill G (Time.probe X)
local notation "W"=> X.paths
local notation "D"=> X.clip
local notation "σ"=> X.width
local notation "b'"=> (fun x=>radiusB x)
local notation "L'"=> lowHard (Time.probe X) D σ W
local notation "T"=> Height.away X
local notation "U"=> raiseK G L X n j k
local notation "Y"=> betaF
local notation "m'"=> (climbed j n)
local notation "K"=> (rampK j n)
def curtain (x:ℝ):= softReset G (Time.probe X) 1*(1+(b' x:ℝ))^4 + ( 2*Blaze.Frond.boil G L x+2⁻¹*d)*(L'*(1+(b' x:ℝ))^4)
lemma motivated (x:ℝ) (hf:Blaze.Frond.mist G L x ≤ Pressure.temp x)(hh:0< Y G x L)
    (P:BudgetPoint) (he:P.threshold=Pressure.temp x)(hk:P.B=radiusB x)(hr: Time.Same X P) (v:ℝ)(hv:0≤v) : softNeed G P D σ W 0 v≤ curtain G L X x*v:= by
    have hf:(Blaze.Frond.boil G L x)⁻¹≤P.threshold:= he.symm ▸ hf
    obtain ⟨-, -, hL⟩:= Collection.budget_pos (Time.probe X) G X.clip X.width_pos X.paths_pos.le
    have ht:= P.threshold_pos; let b:= Blaze.Frond.boil G L x; have hp:0<b:=Real.rpow_pos_of_pos hh _
    have hB: P.threshold⁻¹≤ b:= (inv_anti₀ (inv_pos.mpr hp) hf).trans_eq (inv_inv ..)
    have hY : hitNeed P G 0 v ≤ (2*b+2⁻¹*d)*v:= by
       rw [hitNeed,abs_zero,zero_add, show VerifiedReset.pairBill G P=d from (by unfold VerifiedReset.pairBill Time.probe; dsimp; rw [hr.1,hr.2.1])]
       have hU: v/P.threshold^2*(2*P.threshold) + v*2⁻¹*(d)=(2*P.threshold⁻¹+2⁻¹*d)*v:= by field_simp
       rw [hU]; apply mul_le_mul_of_nonneg_right _ hv; apply add_le_add _ le_rfl; gcongr
    have he' :0≤ hitNeed P G 0 v:= by unfold hitNeed; have hv:=VerifiedReset.pair_nonneg G P; positivity
    unfold softNeed
    apply le_trans (add_le_add (softReset_exp G X hr hv) (mul_le_mul hY (lowSoft_exp X hr) (budget_pos P G D X.width_pos X.paths_pos.le).2.2 (he'.trans hY))) (le_of_eq ?_); unfold curtain; rw [hk]; unfold b; ring
-- event minimum exponent `m' = ramp + leew`
local notation "v"=> (betaK G L n j)
def plusK (x:ℝ):= (Y G x L)^(m' +1/2)
def pulseK (x:ℝ):= (Y G x L)^(m' +1)
def alarmed (x:ℝ): Prop:= ∀ P:BudgetPoint,Time.Same X P→P.threshold=Pressure.temp x→P.B=radiusB x→ regularNeed G P D σ W 0 (U x)≤ v x∧ softNeed G P D σ W 0 (U x)≤ plusK G L n j x∧ ∀ a:ℝ,P.threshold^2*a≤ U x→ a ≤ pulseK G L n j x
lemma chimes (hn:n≤j): ∀ᶠ x in atTop, alarmed G L X n j k x:= by
   obtain ⟨h₀,h₁,h⟩:= feathers G L X n j k hn
   have he : K < m':= lt_add_of_pos_right _ (by unfold leew; positivity)
   let f x:= (1+ (b' x:ℝ))^(4:ℕ); have hh: Rate G L 0 f := (((Bolt.still 1).joins (Bolt.size (G:=G) (L:=L))).nod 4).uses
   have hx:Rate G L (1/2) (curtain G L X):= by
      apply Rate.add ((hh.mul_left _).weaken (by norm_num)); simpa only [add_zero] using! ((((Rate.power (G:=G) (L:=L) (a:=1/2)).mul_left 2).add ((Rate.const (G:=G) (L:=L) ((2:ℝ)⁻¹*d)).weaken (by norm_num : (0:ℝ) ≤ 1/2))).mul (hh.mul_left (L')))
   filter_upwards [Delay.shift_pos G L,softly G L,(h.mul_left (Time.base G X)) m' he,(hx.mul h) (m' +1/2) (by linarith only [he]), sail G L X n j k hn] with x hx hζ hw hv hf
   intro P h hv' hb; let Z:=Y G x L; have hZ:0<Z:=hx; have ht:0≤ (U x):= raise_nn hx.le
   refine ⟨?_, (motivated G L X x hζ.2 hx P hv' hb h _ ht).trans ((le_abs_self _).trans hv), ?_⟩
   · rw [Time.table G X h, abs_zero,zero_mul,mul_zero,add_zero]; exact (le_abs_self _).trans hw
   intro a hh'; by_cases he':0<a; swap; · exact (le_of_not_gt he').trans (Real.rpow_nonneg hx.le _)
   apply le_of_mul_le_mul_left (a:=Z⁻¹) _ (inv_pos.mpr hx); let t:=Blaze.Frond.mist G L x; have hg:Z⁻¹=t^2:= by
     unfold Z t Blaze.Frond.mist Blaze.Frond.boil; rw [inv_pow,← Real.sqrt_eq_rpow, Real.sq_sqrt hx.le]
   have hQ: Z⁻¹ * pulseK G L n j x = v x:= by unfold pulseK betaK; rw [Real.rpow_add hx, Real.rpow_one]; unfold Z; field_simp
   rw [hQ]; exact ((mul_le_mul_of_nonneg_right (show Z⁻¹ ≤ P.threshold^2 from hg ▸ pow_le_pow_left₀ hζ.1.le (hv'.symm ▸ hζ.2) _) he'.le).trans hh').trans hf.1
end pay
end YM.Juniper.Gauze
