import YM.Comparison.Density.Reset.Emission

/-!
Render a multiple α of this SAME true kinetic. Used only for a calibration
`natural`, *not* asserting that paying this regular bound makes the effect
of propagating an arbitrary uncertain rough E (without contraction) negligible.
All row pairs actually re-rendered even when winding. Reuse VerifiedReset for
kept test clipping & hull. Old and new BudgetPoint equal untouched. Full group
bounds (on E + log spills separately). Direction test budget on truly healthy
(full noncommutative derivative array). Perturbation is still pre-reset on paths,
its fresh E need not be affine-null. This allows changing back to the calibrated
β in Kernel (itself a Density operation). Quantitative polynomial/exponential
cost consequences on Calendar dealt with separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Reset.Rows
open Fusing Markers Testing Registers Marker RG Lattice Function Finset MeasureTheory Filter Wilson
open Pert.Attach Push.AbsoluteSums Assembly Ovens Extra.Iteration
open Progress.DirectedRecipe AnalyticBridge.VerifiedReset AnalyticBridge.VerifiedReset.Collection
open WilsonStartup Averaging Geo UVNext.CouplingReset Next.Scheduling Precision Next.Scheduling.Wages
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {n : Side} {G : Gauge}

variable (P : Rep G n) (a : ℝ)

-- write a*kin = regularLow + regularHigh - corrections
-- hence to change from P.beta to P.beta-a we add both regular
-- and give old exponent= new exponent + corrections

def coupon (i : Low) (U : Config G n) := factor*a*(i.mark P.path P.clip * i.plain P.path 0 U)

def little (i : Faces n) : RegularAddress n:= Quotes.lowEntry G P.path P.p i
def honey (i : Faces n) := coupon P a i.2 ∘ i.1.view

def dewE : Activities G n:=
    ⟨little P ∘ numbering _,P.activities.forced,honey P a ∘ numbering _,P.activities.K⟩

def drizzle : Spikes n→ Pot G n:= fun i=>i.2.fresh P.path (0:Site n) (-(factor*a)) 0 ∘ i.1.view
def dewH : Activities G n :=
    ⟨Quotes.highEntry G P.path ∘ numbering _,P.activities.forced,drizzle P a ∘ numbering _,P.activities.K⟩

def deu := weave (dewE P a) (dewH P a)
def basin := {P with activities := weave P.activities (deu P a), beta:=P.beta-a}

def light (i : Faces n) (U : Config G n) := i.2.loan P.path P.clip (0:Site n) P.p (-(factor*a)) 0 (i.1.view U)

def surge (V : Type) [DecidableEq V] (R : Census V) (X : V→Type) : Leftovers R X G n:=
    ⟨⟨(RegularAddress.support ∘ little P) ∘ numbering _,light P a ∘ numbering _⟩,fun _ _ _=>0⟩

def frost {s b} (h : P.activities.Moves s b): (dewE P a).Moves s b:= by
  let N:= numbering (Faces n); let x:= Equiv.prodCongr (Seat.move s b) (Equiv.refl Low); let u:= (N.trans x).trans N.symm
  have hv i : N (u i)=x (N i):= N.apply_symm_apply _
  refine ⟨u,h.kp,fun i=>?_,fun i=> ?_,h.forced_support,h.forced_inventory,h.forced_tests,fun i U=> ?_,h.valuesK⟩
  · change (little P (N (u i))).site=_; rw [hv]; rfl
  · change (little P (N (u i))).support=_; rw [hv]; exact Seat.spread_move ..
  change honey P a (N (u i)) U=_; rw [hv]; change coupon P a _ (((Seat.move s b) (N i).1).view U)= _; rw [Seat.view_move]; rfl

def freeze {s b} (h : P.activities.Moves s b): (dewH P a).Moves s b:= by
  let N:= numbering (Spikes n); let x:= Equiv.prodCongr (Seat.move s b) (Equiv.refl High); let u:= (N.trans x).trans N.symm
  have hv i : N (u i)=x (N i):= N.apply_symm_apply _
  refine ⟨u,h.kp,fun i=>?_,fun i=> ?_,h.forced_support,h.forced_inventory,h.forced_tests,fun i U=> ?_,h.valuesK⟩
  · change (Quotes.highEntry G P.path (N (u i))).site=_; rw [hv]; rfl
  · change (Quotes.highEntry G P.path (N (u i))).support=_; rw [hv]; exact Seat.spread_move ..
  change drizzle P a (N (u i)) U=_; rw [hv]; change High.fresh P.path (N i).2 0 (-(factor*a)) 0 (((Seat.move s b) (N i).1).view U)= _; rw [Seat.view_move]; rfl

def allowance (p : BudgetPoint) (c : Clip) (σ C : ℝ) := (turnFee p*(|factor*a| * p.threshold^2))*Quotes.lowBase G c p σ C
def credit (p : BudgetPoint) (σ C : ℝ) := (turnFee p*(|factor*a| * p.threshold^3))*Quotes.highBase G p σ C
def dues (p : BudgetPoint) (c : Clip) (σ C : ℝ) := (hitPower p G (-(factor*a)) 0)*Quotes.lowHard p c σ C
abbrev Full (A : Activities G n) (B : BudgetPoint) (e : ℝ) := ∃ u : ℕ→ℝ,
    (∀ i U, |A.E i U| ≤ u i) ∧ Quotes.anchored B A.reg u e

def fieldLow (p : BudgetPoint) (c : Clip) (C : ℝ) := (|factor*a| * 2)*(Quotes.anchoredFee p lowCount * (lowerSize c C))
def fieldHigh (p : BudgetPoint) (C : ℝ) := (|factor*a| * 16)*(Quotes.anchoredFee p highCount * (C+C))
lemma unified {A D : Activities G n} {p : BudgetPoint} {z u : ℝ} (h : Full A p z) (he : Full D p u) : Full (weave A D) p (z+u) := by
  obtain ⟨c,hc,h⟩:=h; obtain ⟨b,hb,he⟩:=he
  let X:= Sum.elim c b
  refine ⟨X ∘ rubric,fun i U=> ?_,fun x=>?_⟩
  · dsimp only [weave,Function.comp_apply]; cases v:rubric i; exact hc _ _; exact hb _ _
  exact budget_pull rubric rubric.injective (split_budget (f:=fun i=> if (Sum.elim A.reg D.reg i).site=x then p.mass (Sum.elim A.reg D.reg i).support (X i) else 0) (h x) (he x))

variable {P} {σ C Λ e c : ℝ} (h : P.path.Bounds P.clip σ C Λ) (ha : 0≤e) (hs : Width (later P.p e ha) P.clip σ)
    (hc : Decent P.clip (later P.p e ha))

lemma shrinkWidth {p : BudgetPoint} {e : ℝ} {c : Clip} {ha : 0≤e} (hs : Width (later p e ha) c σ) : Width p c σ:= by
  refine ⟨hs.1,hs.2.1,(div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)).trans hs.2.2⟩
  change _ ≤ p.supportExponent+e+1; linarith

include h ha hs hc
omit h hs ha hc in
private lemma low_quote (p : BudgetPoint) (hp : Decent P.clip p) (i : Low) :
    Bill p 0 (Healthy p.threshold (i.home P.path p 0)) (|factor*a| * p.threshold^2 * (|i.mark P.path P.clip| * lowCost G p (i.length P.path))) (coupon P a i) := by
  refine Bill.le (Bill.mul_left (factor*a) (Bill.mul_left (i.mark P.path P.clip) (i.plain_bill P.path P.clip 0 hp))) ?_
  unfold lowCost
  have hp : 0 ≤ |factor*a| * p.threshold^2 * (|i.mark P.path P.clip| *(2:ℝ)⁻¹*pairBill G p) := by have := pair_nonneg G p; positivity
  linarith
omit h hs in
lemma soundL : Art (dewE P a) P.p:= by
  have hp : Decent P.clip P.p:=⟨hc.1,hc.2,hc.3⟩
  intro i; let u:=numbering (Faces n) i; let k:=u.2
  change P.p.Regular (u.1.spread (k.home P.path P.p 0)) (coupon P a k ∘ u.1.view)
  apply Seat.regular
  apply reg_bill (low_quote a P.p hp k) (continuous_const.mul (continuous_const.mul (k.plain_cont ..))|>.measurable)
  · exact fun U V hj=> by rw [coupon,coupon, k.plain_local P.path P.p hp.radius 0 U V hj]
  exact fun t U=> by unfold coupon; rw [Low.plain_gauge P.path k 0 t U]

omit hs ha hc in
lemma soundH : Art (dewH P a) P.p:= fun _=>Seat.regular _ (High.fresh_regular P.path _ _ h P.p _ _)

lemma chargedL : (dewE P a).EBound (later P.p e ha) (allowance (G:=G) a (later P.p e ha) P.clip σ C) := by
  let B:=later P.p e ha; let R:=P.path
  have hl:= (Quotes.rows G R P.clip B h hs (n:=n)).1
  let x:=turnFee B*(|factor*a| * B.threshold^2)
  have hp : 0 ≤ x:= by unfold x; have := turnFee_pos B; positivity
  have he:= Quotes.anchored_scale hp hl
  let N:=numbering (Faces n)
  refine ⟨fun i=> _,fun i=> ?_,fun o=> Cost.equiv N (he o)⟩
  let z:= N i; let j:= z.2; let X:= j.home R B (0:Site n)
  have hC := low_quote a B hc j
  have hj : B.Regular X (coupon P a j) := by
    refine reg_bill hC (continuous_const.mul (continuous_const.mul (j.plain_cont ..)) |>.measurable) ?_ ?_
    · exact fun U V hU=> by rw [coupon,coupon, j.plain_local R B hc.radius 0 U V hU]
    exact fun k U=> by unfold coupon; rw [Low.plain_gauge R j 0 k U]
 
  apply sup_le (z.1.sup hj (Bill.sup hC (fun _ hh=>hh)))
  apply le_of_eq
  change turnFee B*(_ * (|j.mark R P.clip| * lowCost G B (j.length R))) = x * (|j.mark R P.clip| * lowCost G B (j.length R)); ring

omit hc in
lemma chargedH : (dewH P a).EBound (later P.p e ha) (credit (G:=G) a (later P.p e ha) σ C) := by
  let B:=later P.p e ha; let R:=P.path
  have hl:= (Quotes.rows G R P.clip B h hs (n:=n)).2.1
  let x:=turnFee B*(|factor*a| * B.threshold^3)
  have hp : 0 ≤ x:= by unfold x; have := turnFee_pos B; have := B.threshold_pos; positivity
  have he:= Quotes.anchored_scale hp hl
  let N:=numbering (Spikes n)
  refine ⟨fun i=> _,fun i=>?_,fun o=> Cost.equiv N (he o)⟩
  let z:= N i; let j:= z.2
  apply sup_le (z.1.sup (j.fresh_regular R _ h B _ _) (Bill.sup (j.fresh_bill R _ B _ _) (fun _ hh=>hh)))
  apply le_of_eq
  change turnFee B*(|-(factor*a)+0| * (j.price R B * B.threshold^3))= x * j.price R B
  rw [add_zero,abs_neg]; unfold x; ring
lemma charged : Art (deu P a) P.p ∧ (deu P a).EBound (later P.p e ha) (allowance (G:=G) a (later P.p e ha) P.clip σ C + credit (G:=G) a (later P.p e ha) σ C) :=
    ⟨weave_art (soundL a ha hc) (soundH a h), weave_bound (chargedL a h ha hs hc) (chargedH a h ha hs)⟩
end YM.Comparison.Density.Reset.Rows
