import YM.LocalLTE.Slide.Frost
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
namespace YM.PhysicalNext.Repeat.Scarf
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Poll Pond MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Metric Progress.DirectedRecipe Payments Ovens Ovens.Pipes
open Refrain Trio Marlin Push.BetaTransport Shingle
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c L:Side} {X : Listing G c} {m r j k p:ℕ} {e d a Z K q b v Y : ℝ} {x:ℝ} {S:Set ℝ} {ι:Type}
-- primary ornament site widened, still full K mass allocation ONLY eligibility. Frame output may use m beyond (2*z) with flag tests.F.work
variable (B:BudgetPoint)(X : Listing G c) (s : Finset ℕ) (m : ℕ)

def diamond : Listing G c:= {X with reg:=enlarged X.reg s m}
def hesitates (z:ℕ)(d:Collection.Source G c)(t g: Trio.Offer G c)(i:Site c) (U:Config G c):= t i U+ delay X.reg s m B d.logRead i U+(masked B.threshold (neighbors z i) (g i) U -masked B.threshold (neighbors m i) (g i) U)
local notation "Y"=> diamond X s m

variable (z w:ℕ){f T:Collection.Source G c}(g t: Trio.Offer G c)
variable (hA: ∀ i:(Site c), Trio.Tidy B (neighbors w i) (t i)∧ (∀ V,t i V ≠0→¬ Healthy B.threshold (neighbors w i) V)∧ ∀ V, ‖t i V‖ ≤ e) (hk: Meadow.Budget B X.reg T.logRead a) (he: Meadow.Budget B (Marlin.leap z) g b) (hR: Rooms X.reg s m B p) (hh:z≤ m)(hx:m≤w)
local notation "U"=> hesitates B X s m z T t g
include hA hk he hR hh hx
lemma spires (i: Site c): Trio.Tidy B (neighbors w i) (U i) ∧ (∀ V:Config G c,(U i) V ≠0→ ¬Healthy B.threshold (neighbors w i) V)∧ ∀ V, ‖U i V‖ ≤ e+2*a+2*b:=by
    obtain ⟨hs,hg,hl⟩:= hA i; obtain ⟨u,he',ht'⟩:= hk; obtain ⟨g₀,h,h'⟩:=he
    let v i:= delay X.reg s m B T.logRead i; have hv i := sap X.reg s m B T.logRead hR (fun i _=> (ht' i).1) i
    let f₀ N:= masked B.threshold (neighbors N i) (g i)
    have ht (k l:ℕ)(hx:k≤l):neighbors k i ⊆ neighbors l i:= fun j hj => (neighbors_mem ..).mpr (((neighbors_mem ..).mp hj).trans hx)
    have hp:B.Regular (neighbors m i) (g i):= reg_larger (h' i|>.1) (ht z m hh)
    have hR' (f g:Config G c→ℝ) (hf:Trio.Tidy B (neighbors w i) f)(hg:Trio.Tidy B (neighbors w i) g): Trio.Tidy B (neighbors w i) (f+g):= by
       have he:=Trio.tidy_sub B hf (show Trio.Tidy B _ ((0:Config G c→ℝ) - g) from Trio.tidy_sub B (Trio.tidy_const ..) hg); rw [zero_sub, sub_neg_eq_add] at he; exact he
    have hVg:= (hv i).1
    have hu': Trio.Tidy B (neighbors w i) (v i):= ⟨Work.H03.reads_larger (ht m w hx) hVg.uses,hVg.borel,hVg.invariant⟩
    refine ⟨hR' _ _ (hR' _ _ hs hu') (Trio.tidy_sub B (Trio.tidy_mask _ (h' i).1 (ht z w (hh.trans hx))) (Trio.tidy_mask _ hp (ht m w hx))),fun V h₁ h₂=> h₁ (?_),fun V=>?_⟩
    · unfold Scarf.hesitates; have he := healthy_mono (ht m w hx) h₂
      rw [masked_eq _ _ _ _ (healthy_mono (ht z m hh) he),masked_eq _ _ _ _ he,sub_self,(hv i).2 _ he,show t i V=0 from not_not.mp fun h=>hg V h h₂,add_zero,add_zero]
    have ht':‖delay X.reg s m B T.logRead i V‖≤ 2*a:= Scarf.sap_cost X.reg s m B T.logRead hR i (fun i _=> (ht' i).2) (fun x=> Scarf.stanza X.reg he' (fun i=> (ht' i|>.2.1)) x) V
    have hQ : g₀ i ≤ b:= by
       have hp':=budget_single (Scarf.stanza (leap z) h (fun i=> (h' i).2.1) i) i; rwa [if_pos rfl] at hp'
    have hh': B.supBounds i (neighbors z i) (g i) b:= VerifiedReset.sup_le (h' _|>.2) hQ; have hF': B.supBounds i (neighbors m i) (g i) b:= VerifiedReset.sup_larger hh' (ht _ _ hh)
    unfold hesitates; refine (norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add (hl V) ht')) ?_); rw [two_mul]; exact (norm_sub_le ..).trans (add_le_add (CouplingShape.mask_cost hh' V) (CouplingShape.mask_cost hF' V))
-- exactly additive.change
omit hA hx
omit he hh in
lemma stratus (V:Config G c): (X.read T).additive B V=((diamond X s m).read T).additive B V + ∑ i, delay X.reg s m B T.logRead i V:= by
    have h:=(Scarf.acreage X.reg s m B hR T.logRead hk); exact delayed X.reg s m B T.logRead V (Marlin.stashes B X _ V hk) (Marlin.stashes B (diamond X s m) _ V h)
variable {L: Listing G c}{c₁ a' :ℝ}
    (hn:∀ i,L.hard i=X.hard i ∧ f.hardRead i=T.hardRead i)
    (ht: ∀ s b, Nonempty ((L.read f).Moves s b))
    (hv: ∀ s' b,Nonempty (((diamond X s m).read T).Moves s' b))
    (h:∀ V:Config G c,(L.read f).additive B V= (X.read T).additive B V+Fintype.card (Site c)*d+(∑ i, masked B.threshold (neighbors z i) (g i) V)+ ∑ i,t i V)
local notation "j₀"=> Marlin.lodge (diamond X s m) m w
local notation "t₀"=> Marlin.bison T g U
include hn ht h hv hk w
omit he hh in
lemma carve (hP: Ingredients (j₀) (Marlin.dummy (t₀)) (raiser B) 0 a') (R:PathData G)(c':Clip)(β x τ:ℝ) (V:Config G c) :
    earlyValue L R c' B f β x τ V= earlyValue (Marlin.pluck B (j₀)) R c' B (Marlin.poursP B (j₀) (t₀)) β (x-d) τ V:=by
    refine Marlin.carries B (diamond X s m) m w T g U V (R:=L) f hn R c' _ _ _ _ hP (Scarf.acreage X.reg s m B hR _ hk) ?_ ht hv
    intro W; rw [h W, Scarf.stratus B X s m hk hR W]; unfold hesitates; rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,Finset.sum_add_distrib]; abel
end YM.PhysicalNext.Repeat.Scarf
