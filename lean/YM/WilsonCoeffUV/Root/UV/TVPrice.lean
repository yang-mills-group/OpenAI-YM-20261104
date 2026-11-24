import YM.WilsonCoeffUV.Root.UV.LimitRecurrence
import YM.WilsonCoeffUV.Vacuum.UV.Moment
import YM.WilsonCoeffUV.Test.Measure
/-!
# True cover moments. Export signed positive measure codes and explicit presentation costs.
Root radius Lebesgue sup <=1/2; distance can use l1 taxi. -- no density norm adaptor here. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V α β:Type*}{r h D l e j k a N M m b i q:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{s t t' A B C x y δ σ γ S O v:ℝ}
variable {E W U' V':Credit}{T:SectionData F}{p:h<D}{θ:ℕ→ℝ}
-- root radius t
lemma rootV [NormedAddCommGroup U][Fintype α]{P:Ten U (Cloth α) k}(h:Cork Bank.terrain 0 s A P)(hp:0<s)(v:s⁻¹≤ B)(r): SumBudget (fun x:dock Cover α k=> (1+(tread Bank.terrain 0 x:ℝ))^r*Real.exp (s/2*tread Bank.terrain 0 x)* ‖P x‖) (A*offerQ α k r B):=by
    let Z:= (1+4*r*B)^r; have hB:0≤B:= (inv_pos.mpr hp).le.trans v; have hZ:0≤Z:= by unfold Z; positivity
    let u:= s/4; have hu:0<u:= div_pos hp (by norm_num)
    have hr (y:dock Cover α k): Real.exp (-u*tread Bank.terrain 0 y) ≤ sail (u/k) Bank.terrain 0 y:= by
       by_cases he:k=0
       · subst k; simp [sail,tread,league,Bank.terrain]
       have he' j: Bank.terrain.gap 0 (y j).1≤ tread Bank.terrain 0 y:= leg_le Bank.terrain (Fin.cons (0:Cover) (Prod.fst ∘ y)) 0 j.succ
       simpa only [sub_zero,neg_zero,zero_mul,Real.exp_zero,one_mul] using sail_cut (d:=Bank.terrain) (Nat.zero_le (tread Bank.terrain 0 y)) le_rfl hu (by omega) 0 y he'
    have he : SumBudget (fun y:dock Cover α k=> sail (u/k) Bank.terrain 0 y) (tiePay α k u):= by
       by_cases ht:k=0; · subst k; simp [sail,SumBudget,tiePay]; exact summable_of_hasFiniteSupport (Set.toFinite _)
       exact train_pay (div_pos hu (Nat.cast_pos.mpr (by omega))) _ _
    have hA:=h.1
    have hg: A*Z*tiePay α k u ≤ A*offerQ α k r B:= by unfold Z u offerQ; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (tideQ hp v) hZ) hA
    have hf (x:dock Cover α k): let l:=tread Bank.terrain 0 x; (((1+l):ℝ)^r *Real.exp (s/2*l))*‖P x‖≤ A*Z*sail (u/k) Bank.terrain 0 x:=by
       intro l; calc
        _ ≤ (Z*Real.exp (s/4*l)*Real.exp (s/2*l))*(A*Real.exp (-s*l)):=mul_le_mul (mul_le_mul_of_nonneg_right (ember hp v l r) (by positivity)) (h.2 _) (by positivity) (by positivity)
        _ = (A*Z) * Real.exp (-u*l):=by rw [show -u*l=(s/4*l+s/2*l)+ -s*l by unfold u; ring,Real.exp_add,Real.exp_add]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hr _) (by positivity)
    have hh:= budget_minor (cap_scale he (show 0≤ A*Z by positivity)) (f:=fun x:dock Cover α k=> (1+(tread Bank.terrain 0 x:ℝ))^r*Real.exp (s/2*tread Bank.terrain 0 x)* ‖P x‖) (fun _=>by positivity) hf; exact ⟨hh.1,hh.2.1,hh.2.2.trans hg⟩
def ranging (α:Type*) (x:dock Cover α k):ℝ:= 3+∑ i, (Bank.terrain.gap 0 (x i).1:ℝ)
lemma reachR (x:dock Cover α k): ranging α x ≤ (3+k)*(1+(tread Bank.terrain 0 x:ℝ)):=by
   unfold ranging; have hx:(∑ i,(Bank.terrain.gap 0 (x i).1:ℝ)) ≤ ∑ _ :Fin k,(tread Bank.terrain 0 x:ℝ):= Finset.sum_le_sum (fun i _=> Nat.cast_le.mpr (show Bank.terrain.gap 0 (x i).1≤ tread Bank.terrain 0 x from leg_le Bank.terrain (Fin.cons (0:Cover) (Prod.fst ∘ x)) 0 i.succ))
   simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,nsmul_eq_mul] at hx; nlinarith only [hx, show 0≤ (k:ℝ) by positivity,show 0≤ (tread Bank.terrain 0 x:ℝ) by positivity]
open Embroider.Canvas MeasureTheory
def Keys_ {α: Type*} (P:Ten (Vote D) (Cloth α) k)(s:ℝ)(r:ℕ)(C:ℝ): Prop:= ∃ f : (dock Cover α k) → Measure (Spun D),
    (∀ x, (f x).Regular ∧ IsFiniteMeasure (f x)) ∧
    (∀ x (v:Scroll D), P x (page D v)=∫ y, balk v y ∂(f x)) ∧
    SumBudget (fun x:dock Cover α k=> (ranging α x)^r * Real.exp (s*tread Bank.terrain 0 x) * (f x).real Set.univ) C

def capPortC (α:Type*)[Fintype α](k r:ℕ)(W:Credit): Credit:= (Credit.mk 0 ((3+(k:ℝ))^r) (one_le_pow₀ (by linarith only [show (0:ℝ)≤ k by positivity]))).prodC ((billingQ α k r).usingC W)
lemma taxR [Fintype α]{P:Ten (Vote D) (Cloth α) k}(h:Cork Bank.terrain 0 s A P)(hp:0<s)(v:s⁻¹≤ W.buy x)(hx:1≤x)(r): Keys_ P (s/2) r (A*(capPortC α k r W).buy x):=by
    choose f F hf he H using fun u=> issued (P u)
    refine ⟨f,fun i=>⟨F i,hf i⟩,H,?_⟩; simp_rw [he]; let Q:= (3+(k:ℝ))^r; have hq:0≤ Q:=by unfold Q; positivity
    unfold capPortC; rw [Credit.products,Credit.stock_up]; simp only [Credit.buy,pow_zero,mul_one];
    let B:=W.buy x
    let z (x:dock Cover α k) :ℝ:= ranging α x ^r * Real.exp (s/2*tread Bank.terrain 0 x)* ‖P x‖
    have hg: SumBudget z (Q*(A*offerQ α k r B)):=by
        apply budget_minor (cap_scale (rootV h hp v r) hq)
        · intro x; unfold z ranging; positivity
        intro x; unfold z; have hv:=reachR x; conv_rhs => unfold Q; rw [← mul_assoc,← mul_assoc,← mul_pow]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by unfold ranging; positivity) hv _) (by positivity)) (by positivity)
    refine ⟨hg.1,hg.2.1,hg.2.2.trans ?_⟩; change Q*(A*offerQ α k r B)≤ A*(Q*(billingQ α k r).buy B); rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (offer_expands (W.purchase hx)) hq) h.1
lemma encodeS (P Q: Ten (Vote D) (YForest G) k)(h:Shelf Bank.terrain 0 s A δ P Q)(hp:0<s)(v:s⁻¹≤ W.buy y)(hx:1≤y)(r): let u:= capPortC (Hooks G) k r W; let B:= A * u.buy y; Keys_ P (s/2) r B ∧ Keys_ Q (s/2) r B ∧ Keys_ (P-Q) (s/2) r (B*δ):= ⟨taxR h.wax hp v hx r,taxR h.wane hp v hx r,(show A * δ * _= _ from mul_right_comm ..) ▸ taxR h.toll hp v hx r⟩
theorem maestro (P:Sees H T p e E W U' i l k)(r): ∃ T':Credit,∀ L:Theatre H T p e E W,∀ m h b N (_:m≤b)(_:b≤N),∀ j:Alma F,valence F j=l →
    let J:=L.V.draws.S; let s:=(L.angle m h).lamp.exitS; let A:=L.V.cash T' m; let X:=(Peaks L.V.draws L.V.paid T p N m).2; let Y:=glory L.V.draws L.V.paid T p m; Keys_ (X j i k) (s/2) r A∧ Keys_ (Y j i k) (s/2) r A ∧ Keys_ (X j i k-Y j i k) (s/2) r (A*(J.a b/J.a m)^((4:ℝ)⁻¹)):= by
    refine ⟨U'.prodC (capPortC (Hooks G) k r W),fun L m h b N v q j u=>?_ ⟩; dsimp only; rw [← trail_ratio,cash,Credit.products]; exact encodeS _ _ (cheers L P h v q j u) (L.angle m h).lamp.positive (L.spend m h).cap (L.V.depth _ h) r
end YM.WilsonCoeffUV.Cosmos
