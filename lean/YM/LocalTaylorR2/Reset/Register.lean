import YM.LocalTaylorR2.Reset.Recoating
/-!
# Price powers for the physical reset on R2

 Reserve powers used after the pre-reset Taylor projection. Logs `loses` in
 softHit may use ALL (1+B)^4, together with one inverse field-threshold.
 They are not the same money as the hard addresses. The full estimate here
 does not for example bound H01's fusion of unaffordable *other* `loses`
 (computed from a `Local` with only the pre-reset Taylor estimate on the
 error), does not authorize changing the density representation via Equality.
 Actual local step buys reclosure on regrouped rather than each independent
 such H. Later consumers must use bill with both modes. Inputs
 from Votes / Legato, all notches held on the same budget. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Recoil
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Gas Ursell Trees Multiple OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection UVNext Next.Scheduling Ovens Quotes
open Extra.Iteration RG.Shoot Push.SectorMeasure Supply Input Testing Push.PriceCompiler Org
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Time Daisy.Charity.RG12
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Progress.DirectedRecipe
variable {G:Gauge} {n:Side} {J: Listing G n} {p:BudgetPoint} {v w y: Collection.Source G n}
    {E Y H κ μ :ℝ} {W:PathData G} {c:Clip} {σ C Λ:ℝ}

abbrev factorL (G:Gauge)(L:Side)(drift:ℝ) := drift + |G.slopeConstant*Real.log L.val|+1
open Time Tail
-- need two facts on soft output: no threshold inverse hidden in regular.
-- thresholds used exactly; K and soot separate.
def soot (G:Gauge)(T:RG.Stage):ℝ := softReset G (Time.probe T) 1 + (2+2⁻¹*pairBill G (Time.probe T))*lowHard (Time.probe T) T.clip T.width T.paths
lemma soot_nn (G:Gauge)(T:RG.Stage):0≤ soot G T:=by unfold soot; have := Time.soft_pos G T; have := pair_nonneg G (Time.probe T); have:= (budget_pos (Time.probe T) G T.clip T.width_pos T.paths_pos.le).2.2; positivity
lemma soot_rate (T:RG.Stage) (hp:Time.Same T p)(he:0≤E): p.threshold * softNeed G p T.clip T.width T.paths 0 E ≤ soot G T * (1+p.B)^4 * E :=by
  have hs:=softReset_exp G T hp he
  have hl:=lowSoft_exp T hp
  have ht:=p.threshold_le; have hy:=p.threshold_pos
  have hr:=pair_nonneg G (Time.probe T); have hh:=Time.soft_pos G T; have hx:= (budget_pos (Time.probe T) G T.clip T.width_pos T.paths_pos.le).2.2
  have hv : pairBill G p=pairBill G (Time.probe T):=by unfold pairBill Time.probe; dsimp only []; rw [hp.1,hp.2.1]
  have hK : hitNeed p G 0 E= p.threshold⁻¹*(2*E)+E*2⁻¹*pairBill G (Time.probe T) := by unfold hitNeed; rw [hv]; simp only [abs_zero,zero_add]; field_simp
  unfold softNeed; rw [hK]
  set k:= p.threshold⁻¹*(2*E)+E*2⁻¹*pairBill G (Time.probe T)
  set K:= lowHard (Time.probe T) T.clip T.width T.paths*(1+p.B)^4 with hU
  have hw:p.threshold*k≤(2+2⁻¹*pairBill G (Time.probe T))*E:=by rw [show p.threshold*k=2*E+p.threshold*(E*2⁻¹*pairBill G (Time.probe T)) by unfold k; field_simp]; have hb:=mul_le_of_le_one_left (show 0 ≤ E*2⁻¹*pairBill G (Time.probe T) by positivity) ht; linarith only [hb]
  calc
    _ ≤ p.threshold * ((softReset G (Time.probe T) 1 * _^4 * E)+ k*K):= mul_le_mul_of_nonneg_left (add_le_add hs (mul_le_mul_of_nonneg_left hl (by unfold k; positivity))) hy.le
    _ ≤ (softReset G (Time.probe T) 1 * (1+p.B)^4 * E)+ ((2+2⁻¹*pairBill G (Time.probe T))*E)*K:=by rw [mul_add,← mul_assoc p.threshold k K]; exact add_le_add (mul_le_of_le_one_left (by positivity) ht) (mul_le_mul_of_nonneg_right hw (show 0 ≤ K by rw [hU]; positivity))
    _ = _ := by unfold soot; rw [hU]; ring

structure Rail (G:Gauge)(L:Side)(x d drift ε:ℝ)(T:RG.Stage):Prop where
    health : d≤ -(7/16:ℝ)
    rush : (radiusB x:ℝ)≤2*x
    gap : betaF G x L≤2*x
    track : T.supportExponent⁻¹≤2*x
    leg : T.width⁻¹≤2*x
    haul : T.paths≤2*x
    step : Time.base G T*(2*turnFee (Time.probe T))+Time.top G T*factorL G L drift ≤ 2*x
    core : Time.base G T ≤ betaF G x L ^ (ε/2)
    soft : soot G T*(1+(radiusB x:ℝ))^4 ≤ betaF G x L ^ (ε/2)

def railD (G:Gauge):Decal G where
  rub P _ E L _ _ _ U i x:= Rail G L x E.wanting P.top.drift (CalendarStep.loss i) U
  good P Q E:= by
    refine ⟨0,fun L _ W U o T j hw _ _=>?_⟩
    let e:ℝ:= CalendarStep.loss j/2; have he:0<e:=by unfold e CalendarStep.loss; positivity
    have hx: ∀ᶠ x in atTop, betaF G x L≤2*x:= (eventually_ge_atTop (G.slopeConstant*Real.log L.val)).mono fun x h=>by unfold betaF; linarith
    have hr:=Rate.radius_price (L:=L) (G:=G)
    have hk : Rate G L 0 (fun x=> soot G T*(1+(radiusB x:ℝ))^4):= by simpa only [zero_mul] using! ((((Rate.const 1).add hr).pow 4).mul_left (soot G T))
    have hh:=Rate.const (L:=L) (G:=G) (Time.base G T) e he
    let s:=Time.base G T*(2*turnFee (Time.probe T))+Time.top G T*factorL G L P.top.drift
    filter_upwards [hr 1 zero_lt_one,hx,hk e he, hh,eventually_ge_atTop s,eventually_ge_atTop T.supportExponent⁻¹,eventually_ge_atTop T.width⁻¹,eventually_ge_atTop T.paths] with x hR hX hK hH hS ha hb hd
    rw [Real.rpow_one] at hR; have h₀':0≤x:=le_trans T.paths_pos.le hd; have ht : x ≤2*x:=by linarith
    exact ⟨hw,(le_abs_self _).trans (hR.trans hX),hX,ha.trans ht,hb.trans ht,hd.trans ht,hS.trans ht,(le_abs_self _).trans hH,(le_abs_self _).trans hK⟩

lemma prices {T:RG.Stage} {x drift α ε d:ℝ} {L:Side} (H:Rail G L x d drift ε T) (hp:Time.Same T p)(hα:|α|≤factorL G L drift) (he:E≤2*turnFee p) (hy:p.B=radiusB x) :
    regularNeed G p T.clip T.width T.paths α E ≤2*x ∧ ∀ f≥ (0:ℝ), regularNeed G p T.clip T.width T.paths 0 f ≤ betaF G x L^(ε/2)*f ∧
      p.threshold * softNeed G p T.clip T.width T.paths 0 f ≤ betaF G x L^(ε/2)*f:= by
    have hx:=Time.base_nonneg G T; have hF:turnFee p=turnFee (Time.probe T):=by unfold turnFee Time.probe; simp only [hp.1,hp.2.1]
    have hV : p.threshold^3≤1:=pow_le_one₀ p.threshold_pos.le p.threshold_le
    constructor
    · rw [table G T hp]; rw [hF] at he
      exact (add_le_add (mul_le_mul_of_nonneg_left he hx.1) (mul_le_mul_of_nonneg_left ((mul_le_of_le_one_right (abs_nonneg _) hV).trans hα) hx.2)).trans H.step
    intro f hf; rw [table G T hp,abs_zero]; simp only [zero_mul,mul_zero,add_zero]
    have h : soot G T*(1+(p.B:ℝ))^4 ≤ _:= hy.symm ▸ H.soft 
    exact ⟨mul_le_mul_of_nonneg_right H.core hf,(soot_rate T hp hf).trans (mul_le_mul_of_nonneg_right h hf)⟩

open Roost PhysicalNext.Repeat.Legato
variable {M: Metals G} {D:Rolls M.p} {A : Alloy M D} {m j:ℕ} (R:Factor A) (hp:Mallow.RG12.Earned (railD G) R.shape A.delay)
local notation "P" => A.B.a.clock
local notation "T" => A.B.a.params m
local notation "b" => A.B.a.budget m
local notation "x" => A.B.a.clock.hatBeta m
local notation "Jp" => A.B.a.clock.J (m+1)
local notation "Ip" => A.B.a.clock.J m
include hp
lemma gatesHere : Rail G (D.L Jp) x (R.expense Jp Ip).wanting (M.p.profile Jp).drift (CalendarStep.loss Jp) T:= by
  rw [params_eq A.B.valid m]
  exact hp _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)
omit hp in
lemma inv_bound (a: Levels G)(j:ℕ) : (a.budget j).threshold⁻¹ ≤ Real.sqrt (a.clock.hatBeta j) := by
    -- omit R
    have h0 : 1≤ a.clock.monitor j:= Real.one_le_exp (sq_nonneg _); have hs := zero_lt_one.trans (a.fits.delayed j)
    change (a.clock.hatCoupling j*a.clock.monitor j)⁻¹ ≤ _
    have hp:0<a.clock.hatCoupling j:=by unfold Calendar.hatCoupling; positivity
    exact (inv_anti₀ hp (le_mul_of_one_le_right hp.le h0)).trans_eq (inv_inv _)

lemma base_quote (hx: (P).monitor m ≤ x) {y:ℝ} (he:0≤y)(hh:y≤ 2*x): Pert.Kinetic.Quotes b (T).width (T).paths ((P).loopCap m) y (2*x):=by
    have h:= gatesHere (m:=m) R hp; have hMon : 1 ≤ (P).monitor m:= Real.one_le_exp (sq_nonneg _); have hw:= (T).paths_pos; have hm : 1 ≤ x:= hMon.trans hx
    refine ⟨by linarith,?_,h.leg,?_,?_,hh,he,h.rush,h.track,?_⟩
    · exact (T).width_pos
    · rw [abs_of_pos hw]; exact h.haul
    · refine mul_le_mul_of_nonneg_left ((Real.rpow_le_rpow_of_exponent_le hMon ?_).trans (le_trans (Real.rpow_one ..).le hx)) zero_le_two;refine (A.B.a.fits.thetaRange m).2.trans ?_; exact inv_le_one_of_one_le₀ (by exact_mod_cast (show 1 ≤ (P).J m from (by linarith only [(P).adm m])))
    apply (inv_bound _ _).trans ; nlinarith [Real.sq_sqrt (zero_le_one.trans hm)] -- sqrt estimate; exact Universe

omit hp
lemma monitoring (hG:G.Simple) : ∀ᶠ i in atTop, A.B.a.clock.monitor i ≤ A.B.a.clock.hatBeta i := by
    filter_upwards [(Next.Rank.Station.hat_rate A.B.a hG).eventually (Vac.Numbers.cost 1 1 one_pos)] with i hi; simpa [Vac.Numbers.P, Calendar.monitor] using hi
end YM.LocalTaylorR2.Recoil
