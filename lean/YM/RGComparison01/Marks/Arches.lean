import YM.RGComparison01.Marks.Wallet
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Pledge
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas Ursell Trees Height Sail
open PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {H : Cash W s μ L Q o C T R} {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} {χ:Chi} {Ω : Utopia H j v d r C' χ}
    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
local notation "Z" => H.faresP
local notation "bZ" => H.birth
local notation "TZ" => Tree.Forest S.ratio
-- **Anchor ledger**, choice/replica occupancy paid externally when accumulating
-- here. Allows as many subdivisions under a source load as the caller
-- can certify. b marking occupancy total; see Quorum constructor later.
variable (M:ι→Leaf R) (rA:ι→ℝ)
def Bench (M:ι→ Leaf R) (ρ : ι→ℝ)(d:ℝ) := ∃ o:ι→Site f,(∀ i,o i∈(M i).crest) ∧
    (∀ i,0≤ρ i)∧ Anchored o (Palette.wages M ρ) (fun i=> coverNumber R.p.B (M i).crest) R.p.supportExponent d
section
-- generic financial GEO. d explicit
variable {m:ℕ}
abbrev wageIn (Q:ConnectedActivityE6.Target G P) (L:Side)(s:ℝ):= Footprint.payment (L.val^4) (extentCost (Q.halo+5) (radiusB s)) 0 Q.ε 1 1 Q.relative (preCost (Q.halo+5))
lemma wage_in (Q:ConnectedActivityE6.Target G P) (L:Side)(s d:ℝ): Footprint.payment (L.val^4) (extentCost (Q.halo+5) (radiusB s)) 0 Q.ε 1 d Q.relative (preCost (Q.halo+5)) = d*wageIn Q L s:=by unfold wageIn Footprint.payment Footprint.degreeIncome; ring
lemma wager (Q:ConnectedActivityE6.Target G P) (L:Side): Geo G L (wageIn Q L):=by
  have ht:Geo G L (fun x=> (extentCost (Q.halo+5) (radiusB x):ℝ)):= by unfold extentCost; push_cast; exact (Geo.fixed _).times Geo.radii
  have hv:Geo G L (fun x=> (Footprint.spread (L.val^4) (extentCost (Q.halo+5) (radiusB x)):ℝ)):= by unfold Footprint.spread; push_cast; exact (Geo.fixed _).times (Geo.balling ht)
  exact ((((Geo.fixed _).times hv).times (Geo.fixed _)).times (Geo.fixed _))
end

structure Payment (Q:ConnectedActivityE6.Target G P) (R:Rep G f) (x:ℝ) (S : StepData c f):Prop where
  budgeted : R.p.B ≤ 2*radiusB x
  audience : 0 < radiusB x
  tickets : Footprint.reserve (R.p.supportExponent-2*Q.ε) Q.relative (conversion S.ratio (Q.halo+5)) Q.ε

lemma payments (P:Teller G)(Q:ConnectedActivityE6.Target G P) : ∃ n:ℕ,∀ (L:Side), n≤L.val→∀ᶠ x in atTop,∀ c f (S:StepData c f) (T : Tube G S) (R:Rep G f), S.patch.L=L→ Intake P T x R→ Payment Q R x S:= by
  have hX := Q.grants
  have hp:0≤ Q.relative := by unfold Target.relative; nlinarith [Q.bound,Q.usable,Q.pos]
  obtain ⟨n,hn⟩:= Fees.exponent (Q.halo+5) Q.usable hp (show 2*Q.ε < P.top.supportExponent-2*Q.ε by linarith only [hX.1])
  refine ⟨n,fun L hl=>?_⟩
  have hz:= Fees.horizons G L Q.halo Q.usable hp (show 2*Q.ε<P.top.supportExponent by linarith [hX.1,Q.usable]); filter_upwards [hz] with x hx c f S T R hs hK
  refine ⟨?_, hx.1,hK.exponent ▸ hn c f S.ratio (show _ from ?_)⟩
  · rw [hK.sizes,hs]; exact hx.2.1
  rw [show S.ratio.count=L from hs]; exact hl

lemma portion_sale (hP:Payment Q R s S)(he : (Tithe.portion R.activities Ψ).EBound R.p e) (H:Cash W s μ L Q o C T R) (ht : e≤1) : ∃ b:ℕ→ℝ,Casing R b Ψ ∧ Sales (radiusB s) Q.relative Q.ε (Raw.regularFoot S.ratio Q.halo (radiusB s) R) b (Raw.regularExtra R) (e*wageIn Q L s):= by
   rw [←wage_in,← H.laws.data.funds.length_eq]; obtain ⟨d,hd,hD⟩:=he
   let X i := (R.activities.reg i).support; let Y i := (R.activities.reg i).site
   have hx : Anchored Y d (Raw.regularExtra R) R.p.supportExponent e:= by intro i; convert hD i using 1; ext j; unfold BudgetPoint.mass; rw [mul_comm (Real.exp _) (d j)]; rfl
   let P' := Raw.regularFoot S.ratio Q.halo (radiusB s) R
   refine ⟨d,⟨fun i hp U=> ?_,fun i _=> ?_⟩, Sales.anchored_sale (z:=d) (l:=Q.halo+5) (M:=R.p.B) S.ratio _ (Y:=X) (fun i=>(R.activities.reg i).anchor) hx (fun i=>(hd i).1) (X:=P') (fun i=> inspected_price S.ratio Q.halo (radiusB s) _ hP.audience) hP.audience hP.budgeted hP.tickets 0 (C:=1) zero_le_one (fun i=>⟨(hd i).1,by simp⟩)⟩
   · by_cases hc: Healthy R.p.threshold (X i) U
     · rw [Activities.regularOccurrence,masked_eq _ _ _ _ hc]; have hs := (hd i).2 U hc [] (Nat.zero_le _) (by simp); simpa only [Tithe.portion, hp,if_true,leftDerivs,Real.norm_eq_abs] using hs
     rw [Activities.regularOccurrence,masked_ne _ _ _ _ hc,abs_zero]; exact (hd i).1
   exact (R.p.loMass (X i) _ (hd i|>.1)).trans (le_trans (by simpa only [Tithe.portion, ↓reduceIte, X] using (budget_single (hD (R.activities.reg i).site) i)) ht)
section cast
variable (H:Cash W s μ L Q o C T R)
local notation "w0" => Palette.wages M rA
local notation "Xt" => Palette.sign M S
lemma leaf_sale (hP:Payment Q R s S)(he: Bench M rA d) : Sales (radiusB s) Q.relative Q.ε (H.supportP ∘ Xt) w0 (fun i=>coverNumber R.p.B (M i).crest) (d*wageIn Q L s):= by
  rw [← wage_in,← show (S.ratio.count.val^4:ℕ)= L.val^4 from (by rw [show S.ratio.count=L from H.laws.data.funds.length_eq])]
  obtain ⟨o,ht,h,hK⟩:=he
  let A i:=(M i).crest; have hB i:(H.supportP ∘ Xt) i = enlargement S.ratio Q.halo (radiusB s) (RG.inspected (A i)):= (M i).turn.badge_area R T _ _
  let w:ι→ℝ:= w0; have hx (i:ι): 0≤w i :=mul_nonneg (h i) (M i).profit
  exact Sales.anchored_sale (z:=w0) (l:=Q.halo+5) (M:=R.p.B) S.ratio _ (Y:=A) ht hK hx (X:= (H.supportP ∘ Xt)) (fun i=> hB i |>.symm ▸ inspected_price S.ratio Q.halo (radiusB s) _ hP.audience) hP.audience hP.budgeted hP.tickets 0 (C:=1) zero_le_one (fun i=>⟨hx i,by simp⟩) -- footprint proof
variable [Fintype ι]
lemma ticketsExtra (hP:Payment Q R s S)(he:Bench M rA d) : Ac.Hit H.supportP (radiusB s) (tariff (Tickets.extra Xt w0) (stairs H) (tolling H) Q.ε) Q.relative (d*wageIn Q L s):= by
  have hz:= leaf_sale M rA H hP he
  intro i
  let f₁:= tariff (Tickets.extra Xt w0) (stairs H) (tolling H) Q.ε
  let y (t):=if i∈H.supportP t then f₁ t*Real.exp (Q.relative*coverNumber (radiusB s) (H.supportP t)) else 0
  let A j:= coverNumber R.p.B (M j).crest; let v j:= (w0 j)*Real.exp (2*Q.ε*A j+0); let z (t):= if i∈H.supportP (Xt t) then v t*Real.exp (Q.relative*coverNumber (radiusB s) (H.supportP (Xt t))) else 0
  change SumBudget y _
  have hP j:tolling H (Xt j)=0:= by unfold Palette.sign; cases hn:(M j).turn <;> simp [tolling,Mixed.stamp,Wing.badge,Mixed.shares]
  have h j: stairs H (Xt j)=(A j:ℝ):=by unfold Palette.sign A Leaf.crest; cases h:(M j).turn <;> rfl
  have hv(p:Head S): y p=∑ j, if Xt j=p then z j else 0:=by
    by_cases hu:i∈ H.supportP p
    · unfold y f₁ tariff; rw [if_pos hu]; unfold Tickets.extra; rw [sum_mul,sum_mul]; apply Finset.sum_congr rfl; intro j _; by_cases hx:Xt j=p
      · unfold z; subst p; simp only [ite_true,if_pos hu,h,hP,v]
      simp only [hx,↓reduceIte,zero_mul]
    unfold y; rw [if_neg hu]; symm; refine sum_eq_zero (fun j _=>?_); split
    next hx=> exact if_neg (hx.symm ▸ hu)
    rfl
  apply budget_of_sum
  · intro j; rw [hv]; apply sum_nonneg; intro a _; split; exact hz.hit i|>.1 a; exact le_rfl
  intro Z'; simp_rw [hv]; rw [sum_comm]; apply le_trans (b:=∑ j,z j) _ (budget_sum (f:=z) (hz.hit i) univ)
  refine sum_le_sum fun j _=> ?_; by_cases hw:Xt j∈Z'
  · rw [sum_eq_single_of_mem (Xt j) hw, if_pos rfl]; exact fun i _ he=> if_neg (Ne.symm he)
  rw [sum_eq_zero]; exact hz.hit i|>.1 j; exact fun a ha=> if_neg (fun (h:Xt j=a)=> hw (h.symm ▸ ha))
end cast
end YM.RGComparison01.Pledge
