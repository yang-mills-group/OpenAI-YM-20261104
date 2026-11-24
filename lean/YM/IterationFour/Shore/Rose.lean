import YM.IterationFour.Shore.Patch

/-! Cutoff render alternatives. α-of-top capitalization on W.residual with same masks. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.IterationFour
open Lattice Wilson RG Function MeasureTheory Filter Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
open Quad Work Tensor Next.Fluctuations
attribute [local instance] Gauge.frobInner
variable {G : Gauge}{n : Side}{p : BudgetPoint}{f : G.Mat→ℝ}{q i r :ℕ}
open Start Padded YM.IterationFour YM.IterationFour.Vacuum Render Design
section
/-- P cutoff input through r, retain INDEPENDENT stencil even after normalizing the leading
    part λ. -/
def capital (G:Gauge)(p:BudgetPoint)(S:Stage)(i:ℕ):= eyeG S * (((terms_stamp G (5+i)).cost S) * p.threshold^(5+i))
def top_terms (G:Gauge)(n:Side)(p:BudgetPoint)(S:Stage)(i:ℕ):Piece G n:=
    ⟨3+i,5+i, slate G n (Start.weight S.clip 1) (terms G (5+i)), capital G p S i⟩
lemma eyes (S:Stage): 0 ≤ eyeG S:= by unfold eyeG; positivity
lemma cap_income (p:BudgetPoint)(S:Stage)(G:Gauge)(i:ℕ) : 0 ≤ capital G p S i:= by
    refine mul_nonneg (eyes _) (mul_nonneg ?_ (pow_nonneg p.threshold_pos.le _)); exact (Stamp.history (terms_stamp ..) _).1.le
variable {S:Stage}
lemma upgrade (hS:WilsonStartup.Decent S.clip p) (hs:S.order=p.order) (hp:S.power=p.power) (hh:S.supportExponent=p.supportExponent)(hv:p.threshold ≤ (terms_stamp G (5+i)).near S) :
    let w:=top_terms G n p S i; w.packet.Invoice p w.credit:=by
   intro w
   have ht:= leaf (n:=n) (terms_stamp G (5+i)) (by omega) S hs hp hh (Start.weight S.clip 1) hv
   obtain ⟨g,hg,he⟩:=ht.credit; refine { ht with credit:= ⟨g,hg,fun i=> Extra.Iteration.Cost.enlarge (he i) ?_⟩ }; unfold w top_terms; dsimp only; apply mul_le_mul_of_nonneg_left _ (eyes S)
   apply mul_le_of_le_one_left (mul_nonneg (Stamp.history (terms_stamp ..) _|>.1.le) (pow_nonneg p.threshold_pos.le _)); exact (Start.weight_le _ hS.direct|>.trans (by norm_num)) -- lemma

def album (G:Gauge)(n:Side)(p:BudgetPoint)(S:Stage) (r:ℕ): List (Piece G n) := (List.range (r-2)).map (top_terms G n p S)
lemma turn_in (hS:WilsonStartup.Decent S.clip p)(hs:S.order=p.order) (hp:S.power=p.power)(hh:S.supportExponent=p.supportExponent)(hz:∀ i< r-2,p.threshold ≤ (terms_stamp G (5+i)).near S):
    permits (album G n p S r) p:= by intro w hw; obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hw; exact upgrade hS hs hp hh (hz _ (List.mem_range.mp hi))
lemma grades (G:Gauge)(n:Side)(p:BudgetPoint)(S:Stage)(r:ℕ): gradings (album G n p S r) r:=by
   intro w hw; obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hw; obtain hi:= List.mem_range.mp hi; change 3≤ 3+i ∧ 3+i ≤ r; omega

-- matching stamps at cutoff fromTop (paths & clip installed). Captures P layers exacts.
lemma take_weight (c:Clip)(v:ℝ): v*Start.weight c 1= Start.weight c v:=by unfold Start.weight; ring
lemma pages (q:ℕ)(U:Config G n){v:ℝ}(hv:0<v):
    renders (Render.prefactor (Currency.gain v)) p U ((List.range q).map (top_terms G n p S))=
      (Start.weight S.clip v)*∑ j∈ Finset.range q,∑ i:Key n, masked p.threshold i.skin (element G (terms G (5+j)) i.positive) U:=by
   induction q with
   | zero=> simp [renders]
   | succ q ih =>
      let f:= Render.prefactor (G:=G) (n:=n) (Currency.gain v)
      have hy: ∀ (X Y:List (Piece G n)), renders f p U (X++Y)=renders f p U X+renders f p U Y:=by
         intro X Y; induction X with
         | nil=> simp [renders]
         | cons a l h=> simp only [List.cons_append,renders,h]; ring
      rw [List.range_succ,List.map_append,hy,Finset.sum_range_succ]
      have hx:f (top_terms G n p S q)= v:=by
         have hl: stepOrder (top_terms G n p S q)=-((2:ℕ):ℤ):=by change ((3+q:ℕ):ℤ)-((5+q:ℕ):ℤ)=_; omega
         unfold f Render.prefactor; rw [hl,zpow_neg,zpow_natCast]
         simp only [Currency.gain, inv_pow,inv_inv,Real.sq_sqrt hv.le]
      change renders _ _ U _+(f _* (slate G n (Start.weight S.clip 1) (terms G (5+q))).amount p U+0)=_
      change renders f _ _ _= _ at ih
      rw [ih,show f (top_terms ..)= v from hx,tally]; rw [add_zero,← mul_assoc v, take_weight, mul_add]

private def still (R:Rep G n): Rep G n:=
    { R with activities:= { R.activities with E:=0 } }
private lemma open_still {X:RG.Rep G n}{δ γ : ℝ} (h:X.activities.Valid p δ γ) : (still X).activities.Valid p 0 γ:=by
    let A:=(still X).activities
    have hx i : p.Regular (A.reg i|>.support) (A.E i) := Start.zero_reg
    refine ⟨⟨hx,fun i=>rfl,fun i _ x y _ _=>?_⟩,⟨h.forced.sym,h.forced.symtest,h.forced.meas,h.forced.meas_test,h.forced.reads,h.forced.reads_test,h.forced.permit⟩,?_,?_,h.boundK⟩
    · change logHessian (0:Config G n→ℝ) _ _=0; simp [logHessian]
    · intro s b; obtain ⟨v⟩:= h.moves s b; exact ⟨⟨v.ep,v.kp,v.reg_site,v.reg_support,v.forced_support,v.forced_inventory,v.forced_tests,fun i U=>rfl,v.valuesK⟩⟩
    refine ⟨fun _=>0,fun _=> Start.zero_bound,fun x=>?_⟩; simp [BudgetPoint.mass,SumBudget]

def ruin (G:Gauge)(p:BudgetPoint)(S:Stage)(r:ℕ)(β:ℝ):=eyeG S* (|β| * (if h:2≤r then (chip_stamp G r h).cost S * p.threshold^(r+3) else 0))
def roof (C:Rep G n) (S:Stage) (r:ℕ) := {C with activities:= (slate G n (Start.weight S.clip C.beta) (chip G r)).attach 1 (still C).activities }
variable {A:Levels G} {r :ℕ}{N w:ℕ}{v:ℝ}
local notation "p!"=> A.budget N
local notation "S!"=> A.params N
set_option maxHeartbeats 1200000 in
lemma roof_tag (R:PathData G) (h:2≤r) (hx:0<v)
    (H:WilsonStartup.Decent (S!).clip p!) {δ γ : ℝ} (hm:Progress.DirectedRecipe.Ingredients (dictionary G (A.S.side N w)) (payload (S!).clip p! G (A.S.side N w) v) p! δ γ)
    (hp:(p!).threshold ≤ (chip_stamp G r h).near (S!))
    (hs:Render.permits (album G (A.S.side N w) p! S! r) p!) :
    let t:= payload (S!).clip p! G (A.S.side N w) v
    let W:= Progress.DirectedRecipe.finish R (S!).clip p! (dictionary G (A.S.side N w)) t v 0
    let E:=roof W S! r; let Z:=Render.append (album G (A.S.side N w) p! S! r) E (Render.prefactor (Currency.gain v))
    E.activities.Valid p! (ruin G p! S! r v) γ ∧ Z.eval=W.eval ∧ Z.exponent=W.exponent:=by
   intro t W E Z
   let P:=p!; let S:=S!; let u:=Start.weight S.clip v
   let X:=still W; have hX: X.activities.Valid P 0 γ:= open_still (hm.gates R (S).clip _ 0)
   let d:=A.S.side N w
   let π:=slate G d u (chip G r)
   let y:=eyeG S * (|u| *((chip_stamp G r h|>.cost S) * P.threshold^(r+3)))
   have ht: 0 ≤ eyeG S:= eyes S
   have hc:π.Invoice P y:= leaf (chip_stamp G r h) (by omega) S rfl rfl rfl u hp
   have hv:E.activities.Valid P (ruin G P S r v) γ:= by
      have hv:E.activities.Valid P (0+‖(1:ℝ)‖*y) γ:= Payload.payment 1 hc hX
      refine {hv with boundE:= AnalyticBridge.VerifiedReset.Time.E_rises hv.boundE ?_}
      unfold ruin y; rw [norm_one,zero_add,one_mul,dif_pos h]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Start.weight_le v H.direct) (mul_nonneg (Stamp.history (chip_stamp G r h) _|>.1.le) (pow_nonneg P.threshold_pos.le _))) ht
   have hz : Z.exponent=W.exponent:=by
      funext U; have he1:= Render.additive (R:=E) (Render.prefactor (Currency.gain v)) hs hv U
      have hxX:X.activities.additive P U=0:=by
         simp_rw [Activities.additive]; change (∑' i,masked P.threshold (X.activities.reg i).support (0:Config G d→ℝ) U)=0; simp_rw [Start.masked_zero]; simp
      have hE:E.activities.additive P U= X.activities.additive P U + 1*π.amount P U:=Payload.pays_add (A:=X.activities) 1 hc hX U
      have hK:R=Z.path:=rfl
      let Y:= ∑ i:Key d,masked P.threshold i.skin (element G (chip G r) i.positive) U
      let T:= ∑ j∈Finset.range (r-2),∑ i:Key d,masked P.threshold i.skin (element G (terms G (5+j)) i.positive) U
      have hV : Y + T=∑ i:Key d,masked P.threshold i.skin i.accrual U:=by
         unfold Y T; rw [Finset.sum_comm (s:=Finset.range (r-2)) (t:=Finset.univ),← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _=> ?_
         by_cases hv:Healthy P.threshold i.skin U
         · simp_rw [masked_eq P.threshold i.skin _ U hv, Key.accrual_def]; unfold element; rw [chip_sum G r h, Quad.surplus_actual]; rfl
         simp_rw [masked_ne P.threshold i.skin _ U hv, Finset.sum_const_zero,zero_add]
      rw [hxX,one_mul,show π.amount P U =u*Y from tally ..] at hE
      have hT:Z.activities.additive P U=E.activities.additive P U+ u*T:= by
         rw [show u*T= renders (Render.prefactor (Currency.gain v)) P U (album G d P S r) from (pages _ U hx).symm] -- hx shadow
         exact he1
      -- fold
      change 0* _ - (R.inChannels S.clip P v U) - Z.activities.additive P U = W.exponent U
      rw [hT,hE, show W.exponent U = _ from YM.IterationFour.Shore.equal_stamp (dictionary G d) t R S.clip P v 0 U]
      change _= 0*_ - (R.inChannels S.clip P v U) -(raw G d S.clip P v).additive P U
      rw [Start.written_sum,← hV]; unfold u; ring
   refine ⟨hv,?_,hz⟩; funext U; unfold Rep.eval; rw [hz]
   change _=Real.exp (W.exponent U)* X.activities.gas P U
   change _ * Z.activities.gas P U=_; rw [show Z.activities.gas P=E.activities.gas P from Render.gas _ _ _ _, show E.activities.gas P=X.activities.gas P from rfl]
end
end YM.WilsonStartup.IterationFour
