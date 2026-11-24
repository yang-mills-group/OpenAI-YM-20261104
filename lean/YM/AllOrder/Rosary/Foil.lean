import YM.AllOrder.Rosary.Patch
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Rosary
open Function Filter Set Lattice Wilson RG Ovens
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration Push.BetaTransport
open Till Burn
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ H w : ℝ}
    {X : Listing G n} {v : Collection.Source G n} {ι κ : Type}
-- saturated path prices. assembly buys +3.
def pearl (p:BudgetPoint):BudgetPoint:= { p with supportExponent:=preExponent p, exponent_pos:=by unfold preExponent; linarith [p.exponent_pos] }
local notation "P"=>pearl p
lemma early_sic {d:ι→RegularAddress n}{u:ι→ℝ} (h: anchored (pearl p) d u C): Quotes.early p d u C:= by
  intro x; let f:=fun i:ι=> if (d i).site=x then (pearl p).mass (d i).support (u i) else 0; have he i:f i=if (d i).site=x then u i*Real.exp (preExponent p*coverNumber p.B (d i).support) else 0:= by
    unfold f; by_cases hi:(d i).site=x <;> simp [BudgetPoint.mass,hi,pearl,mul_comm]
  rw [← funext he]; exact h x
-- strong low/high parity paid from Width. on allGood, folds conceptual proxy; not on masks. Don't mix results.
namespace Guard
abbrev FFace (n:Side):=Seat n×Low
abbrev FPeak (n:Side):=Seat n×AnalyticBridge.VerifiedReset.High
local notation "FA"=> FFace n
local notation "FP"=> FPeak n
variable (u:ℝ)
def blue (u:ℝ)(R:PathData G)(c:Clip)(p:BudgetPoint)(n:Side): Herb G n (FFace n) := ⟨lowEntry G R p,fun i=> (fun V=> factor*i.2.fresh R c 0 u V) ∘ i.1.view⟩
def pink (u:ℝ)(R:PathData G)(p:BudgetPoint)(n:Side): Herb G n (FPeak n) := ⟨highEntry G R,fun i=> (fun V=> factor*i.2.fresh R 0 u 0 V) ∘ i.1.view⟩
def costB (G:Gauge)(p:BudgetPoint)(c:Clip)(σ C u:ℝ):=turnFee p* (factor* (|u| *p.threshold^2))*lowBase G c (pearl p) σ C
def costP (G:Gauge)(p:BudgetPoint)(σ C u:ℝ):=turnFee p* (factor* |u| *p.threshold^3)*highBase G (pearl p) σ C
local notation "Q"=> blue u R c p n
local notation "Z"=> pink u R p n
variable (h:R.Bounds c σ C Λ)(hp:Width (pearl p) c σ)(hn:20<n.val)(hv:Decent c p)(g:G.Simple)
-- lemma with general scale rotation
include g
private lemma singles (x:Seat n)(p:BudgetPoint)(o:Support n)(f:Pot G n)(B:ℝ)(h:Till.Fairness p 0 o f B) (hn:20<n.val): Fairness p x.2 (x.spread o) ((fun V => factor * f V) ∘ x.view) (turnFee p * (factor * B)):= by nth_rw 2 [← abs_of_pos factor_pos]; exact (h.scale factor|>.transport x (by omega) g)
include hp h hn hv
lemma wages : (Q).Proto p (costB G p c σ C u)∧(Q).mu=0:= by
 let H : Low→ℝ:=fun d=> |d.mark R c| * lowCost G p (d.length R); let F :ℝ:= turnFee p*(factor*(|u| *p.threshold^2)); let f (i:Low):=F*H i
 have he(d:Low):Fairness p (0:Site n) (d.home R p 0) (d.fresh R c 0 u) (|u| *p.threshold^2 * H d):= ⟨Low.fresh_regular R c d 0 hv _,Bill.sup (d.fresh_bill R c 0 hv _) (fun _ h=> h), d.fresh_one R c 0 _, fun x i=> d.fresh_vanish R c 0 g hv x hn _ _ _ ((LinearJet.isAffine ..).mpr ⟨_,rfl⟩) ((LinearJet.isAffine ..).mpr ⟨_,rfl⟩)⟩
 have hh(i:FA): Fairness p ((Q).addr i|>.site) ((Q).addr i|>.support) ((Q).values i) (f i.2):= by
    rw [show f i.2= turnFee p*(factor*(|u| *p.threshold^2*H i.2)) from (by unfold f F; ring)]; exact singles g i.1 p _ _ _ (he i.2) hn
 have hf :0 ≤ F:= by unfold F; have h:= factor_pos; have h':= turnFee_pos p; positivity
 refine ⟨⟨fun s b=> ⟨(Seat.move s b).prodCongr (Equiv.refl _),?_⟩,fun i=> f i.2,fun i=> ⟨(hh i).ready,(hh i).cap⟩, early_sic (p:=p) (d:=(Q).addr) (anchored_scale hf (Quotes.rows G R c (pearl p) h hp|>.1))⟩,Herb.still fun i=>(hh i).he ⟩ -- rows wrong ambiguous
 intro i; refine ⟨rfl,i.1.spread_move ..,?_⟩; change ((fun V=> factor*Low.fresh R c i.2 0 u V) ∘ (Seat.move s b i.1).view) = _; rw [i.1.view_move]; rfl
lemma crowns : (Z).Proto p (costP G p σ C u)∧(Z).mu=0:= by
 let P':= AnalyticBridge.VerifiedReset.High; let H : P'→ℝ:=fun d=> AnalyticBridge.VerifiedReset.High.price R d p; let F :ℝ:= turnFee p*(factor * |u| *p.threshold^3); let f(d:P'):= F *H d
 have he(d:AnalyticBridge.VerifiedReset.High):Fairness p (0:Site n) (d.home R 0) (d.fresh R 0 u 0) (|u+0| *(H d*p.threshold^3)):= ⟨d.fresh_regular R 0 h p _ _,Bill.sup (d.fresh_bill R 0 p u 0) (fun _ h=>h), d.fresh_one R 0 ..,fun _ i=> d.fresh_vanish R _ g h p _ _ _ _⟩
 have hh(i:FP): Fairness p ((Z).addr i|>.site) ((Z).addr i|>.support) ((Z).values i) (f i.2):= by
    rw [show f i.2= turnFee p*(factor*(|u+0| * (H i.2*p.threshold^3))) from (by unfold f F; rw [add_zero]; ring)]; exact singles g i.1 p _ _ _ (he i.2) hn
 have hf :0 ≤ F:= by unfold F; have h:= factor_pos; have h':= turnFee_pos p; have hh:= p.threshold_pos; positivity
 refine ⟨⟨fun s b=> ⟨(Seat.move s b).prodCongr (Equiv.refl _),?_⟩,fun i=> f i.2,fun i=> ⟨(hh i).ready,(hh i).cap⟩, early_sic (p:=p) (d:=(Z).addr) (anchored_scale hf (Quotes.rows G R c (pearl p) h hp|>.2.1))⟩, Herb.still fun i=>(hh i).he⟩
 intro i; refine ⟨rfl,i.1.spread_move ..,?_⟩; change ((fun V=> factor* AnalyticBridge.VerifiedReset.High.fresh R i.2 0 u 0 V) ∘ (Seat.move s b i.1).view) = _; rw [i.1.view_move]; rfl
variable (U:Config G n)
lemma salary : (Q).teller p U= layer (fade R c p u) U ∧ (Z).teller p U=-(u)* Weaving.highH R p U := by
 have he (b:ℝ):layer (upperFade R p b 0) U=-(b) * Weaving.highH R p U:= by rw [show upperFade (n:=n) R p b 0=_ from funext (fun i=>funext fun V=> Collection.high_fade_eq b 0 V i), layer_scale,add_zero]; -- same
 constructor
 · rw [layer_total ..]; unfold Herb.teller; refine tsum_congr fun i=>?_ ; change masked p.threshold (i.1.spread (i.2.home R p 0)) ((fun V=> factor * i.2.fresh R c 0 u V) ∘ i.1.view) U= _; rw [i.1.distribute,Function.comp_apply, mask_mul]; rfl; exact fade_sum h p u -- strange
 rw [← he,layer_total ..]; unfold Herb.teller; refine tsum_congr fun i=>?_ ; change masked p.threshold (i.1.spread (i.2.home R 0)) ((fun V=> factor * i.2.fresh R 0 u 0 V) ∘ i.1.view) U= _; rw [i.1.distribute, Function.comp_apply,mask_mul]; rfl; exact high_fade_sum h p u 0
variable (R c p) in
lemma flavor (hf:flags p.threshold U=∅) : layer (fun i:Low => i.loan R c 0 p w u) U=0 ∧ layer (fun i:Low=> i.live R c p 0) U= receipt R c p U:=by -- allGood
 have hh(q:Support n)(x:Seat n):Healthy p.threshold q (x.view U):=(Seat.healthy ..).mp (by unfold Healthy; rw [hf]; simp); constructor
 · unfold layer; simp_rw [Low.loan, if_pos (hh _ _), tsum_zero, Finset.sum_const_zero, mul_zero]
 unfold Collection.receipt layer; refine congrArg _ (Finset.sum_congr rfl fun x _=> tsum_congr fun i=> ?_ ); dsimp only; rw [Low.live_plain R c i hv 0 (hh ..)]; symm; exact masked_eq _ _ _ _ (hh ..) -- progress
lemma flareB (h0:flags p.threshold U=∅): layer (fade R c p u) U=u*((∑ i, heads p i U)-receipt R c p U):=by
 have hW:Width p c σ:= ⟨hp.1,hp.2.1, (div_le_div_of_nonneg_right (b:= (pearl p).supportExponent+1) (by unfold pearl preExponent; dsimp; linarith) (Nat.cast_nonneg p.B)).trans hp.2.2⟩
 have ⟨he,he'⟩:= flavor (w:=0) R c p u h hp hn hv g U h0; have ht:= salary u h hp hn hv g U; have hm:layer (upperFade R p 0 u) U=-(u)*Weaving.highH R p U:= by rw [show upperFade (n:=n) R p 0 u=_ from funext (fun i=>funext fun V=> Collection.high_fade_eq 0 u V i), layer_scale,zero_add]
 have hK:= path_split h hW hv 0 u U; rw [hm, ← true_base h hW U, he, he'] at hK; linarith only [hK] -- aliases
end Guard
end YM.AllOrder.Rosary
