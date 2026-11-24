import YM.LocalLTE.East.Summer
/-! Orbit radius inward. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.East
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Match
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open Height LocalLTE.Fan Pastel -- namespace edit
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L : Side} {T₀ : Patch} {ℓ k j n: ℕ} {K : Teller G} {s a W U V g C' y A M K₀ r β δ q b v σ t w Λ γ: ℝ} {m : ℕ}
variable {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} (H : Cash W s a L X o U T R) {I: Cash W s a L X o U T R'} {χ : Chi}
local notation "B" => radiusB s
lemma highway (S:StepData c f): Census (Fintype.card Signed*S.patch.L.val^4) (fun i:Signed×Site f=> i.1.act (S.ratio.parent i.2)):= Census.prefix_counts (fun (i:Signed)=> (Census.homeland S).permute (i.actEquiv.toEquiv))
-- plate vector per aperture.
lemma billboard (S:StepData c f)(D: Support c) {q:ℝ} (Q:ℕ→Atom G n)(hp:SumBudget (fun i=>(Q i).budget σ) q)(hs:0<σ)(hv:0≤v)(hx:q*v≤1): SumBudget (fun i:Raw.Trans f=> if Mint.soul S i∈D then (Q i.2.2).magnitude*v else 0)
    ((1:ℝ)*(D.card*((Fintype.card Signed*S.patch.L.val^4:ℕ):ℝ))):=by
    refine East.censusNext (ι:=Signed×Site f) (s':=fun p:Raw.Trans f=>(p.1,p.2.1)) (P:=fun i:Raw.Trans f=> (Q i.2.2).magnitude*v) (highway S) ?_ zero_le_one D
    intro y; let p i:= (Q i).magnitude*v
    have he:SumBudget p 1:= budget_loosen (budget_mono (budget_scale hv hp) (fun i=>mul_nonneg (sum_nonneg fun i _=>abs_nonneg _) hv) (fun i=> by unfold p; rw [mul_comm]; exact mul_le_mul_of_nonneg_left ((Q i).lower_budget _ hs) hv)) ((mul_comm _ _).le.trans hx)
    have hz: Set.InjOn (fun p:Raw.Trans f=>p.2.2) {p | (p.1,p.2.1)=y}:= by
       intro i hi j hj hp; change (_,_) = _ at hi hj; have hx:= Prod.mk.inj (hi.trans hj.symm); exact Prod.ext hx.1 (Prod.ext hx.2 hp)
    convert East.indicatorPull (P:=fun p:Raw.Trans f=>(p.1,p.2.1)=y) (v:=fun p:Raw.Trans f=> p.2.2) hz p he using 1 with i; ext i; split <;> simp_all only [p]
lemma at_atom {q:ℝ} (P: ℕ→Atom G n)(hp:SumBudget (fun i=>(P i).budget σ) q)(hs:0<σ)(hv:0≤v)(hx:q*v≤1)(i:ℕ): (P i).magnitude*v≤1:= (mul_le_mul_of_nonneg_right (((P i).lower_budget _ hs).trans (budget_single hp i)) hv).trans hx
-- compile Q based traceO.
def grand (L:Side):ℕ := (L.val^4)+3*(Fintype.card Signed*L.val^4)+(Fintype.card Signed*Census.spots L+(Itinerary.density L+Itinerary.density L)) -- edit
variable {Q:ℕ→ℝ} (hE:∀ u₀, SumBudget (fun i=> if (R.activities.reg i).site = u₀ then Q i else 0) 1)
variable (hy:R.path.Bounds R.clip σ A Λ)(hv:1 ≤ β) (ha: A*β^(-claw) ≤ 1) (hp: Λ*β^(-claw) ≤ 1)
include hE H hv hy ha hp
open ConnectedActivityE6.Pulse
lemma grandWay : let g:= fisc (c:=c) R β Q
    (∀ i, 0≤g i ∧ g i ≤1) ∧ ∀ Y:Support c, SumBudget (fun i=> if traceO S R i ∈Y then g i else 0) (Y.card* East.grand L):=by
   let v₁:=β^(-claw); have he:0 < v₁:= Real.rpow_pos_of_pos (zero_lt_one.trans_le hv) _
   intro g; refine ⟨fun i=> ⟨?_,?_⟩,fun Y=> ?_⟩
   · exact fisc_pos (fun i=> by simpa using (hE ((R.activities.reg i).site)).1 i) (zero_le_one.trans hv) i
   · rcases i with i|i|i|i|i
     · change Q i ≤1; simpa using budget_single (hE (R.activities.reg i|>.site)) i
     · exact at_atom _ hy.three hy.width he.le ha i.2.2
     · exact at_atom _ hy.four hy.width he.le ha i.2.2
     · exact at_atom _ hy.two hy.width he.le hp i.2.2
     exact le_rfl
   have hX:=H.laws.data.funds.length_eq
   refine budget_loosen (Cost.sum (East.censusNext (Census.homeland S) (s':=fun i=> (R.activities.reg i).site) hE zero_le_one Y) (Cost.sum (billboard S Y _ hy.three hy.width he.le ha)
       (Cost.sum (billboard S Y _ hy.four hy.width he.le ha)
       (Cost.sum (billboard S Y _ hy.two hy.width he.le hp) (censusHit (smallCensus S L hX) Y))))) ?_
   unfold East.grand; rw [hX]; push_cast; linarith
omit ha hy hp hv hE H in
lemma recurring (P:Teller G)(L:Side): ∀ᶠ x:ℝ in atTop,∀ (c f:Side)(S:StepData c f)(T:Tube G S)(R:RG.Rep G f),S.patch.L=L→ Intake P T x R → R.path.Bounds R.clip P.top.width P.top.paths (loopBill G L x)∧ P.top.paths* (betaF G x L)^(-claw) ≤1 ∧ (loopBill G L x) * (betaF G x L)^(-claw) ≤1 :=by
    unfold claw
    filter_upwards [((Rate.power (G:=G) (L:=L) (a:=-(1/32:ℝ))).mul_left P.top.paths).below (by norm_num) _ zero_lt_one,
      ((loopBill_rate G L).mul (Rate.power (a:=-(1/32:ℝ)))).below (by norm_num) _ zero_lt_one] with x hx ht c f S T R he hR
    have hv:= hR.cap.paths; rw [he] at hv; exact ⟨hv,(le_abs_self _).trans hx,(le_abs_self _).trans ht⟩
end YM.PhysicalNext.Repeat.East
