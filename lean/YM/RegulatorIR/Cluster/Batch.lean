import YM.RegulatorIR.Cluster.Force

/-! Cost for image of the product of two marks in one asynchronous
normalization. Uses actual cover transfers F.lineL. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Cluster
open Set Function Budget Budget.Packet Budget.Layer Budget.Tuple Budget.Tariff Uniform Gradient Step Diagram Collapsed
open scoped ENNReal NNReal Topology BigOperators Classical
variable {W : Type}{X Y V U: W→ Type}{L:Meter W}{v w:W→ℝ≥0∞}{d l:W→ℝ}{hl:∀ i,0<l i}{S T:W→Set Room}{u b p k r e m n:ℕ}
variable (F:Batch X Y V U) (C:∀ w,Orders (X w))

-- Mixed step assembly
abbrev Zone (w:W):= (F.room w).pos
abbrev Gate (w:W):= (F.fine w).pos
abbrev Exit (w:W):= (F.coarse w).pos
def now (F:Batch X Y V U) (C:∀ w,Orders (X w))(w):= (F.grid w).jVac (C w)
def promote (F:Batch X Y V U)(P:∀ i,Orders (X i))(i:W):= present (firstChannel (F.fine i) (F.coarse i)).native (P i)
def ember (F:Batch X Y V U)(P:∀ i,Orders (X i))(m:ℕ)(w:W):=endHeat m (F.lineL w) (logHeat (F.lineL w) (now F C w) false) (promote F P w)
variable {A B:∀ w,Orders (X w)}
lemma entryPays (h:Folds p L (estate hl (Gate F) S u) v A): Folds p L (estate hl (Zone F) S u) v (promote F A):= by
 refine Folds.offer (A:=fun w=> ((fare (hl w) u (S w)).uses (Zone F w))) (B:=estate hl (Zone F) S u) (fun w=>(firstChannel (F.fine w) (F.coarse w)).native) h
-- cost independent mark output, no t>0 etc
lemma support_run {a:ℕ} (h:Folds p L (estate hl (Gate F) S u) v A)(M:Fund p L hl (Zone F) a (now F C) F.lineL)(N:Beam L (home hl (Zone F) u) F.forecast)(he:u≤a): Folds p L (estate hl (Exit F) S u) v fun w=> (F.grid w).each m (C w) (A w):=by
 have H := stays_end (F.lineL) (entryPays F h) (shorter S he M.beam) M.vac (fun i hi j=>overnight S he (M.work i hi j)) false m
 let R (i:W): Tariff (X i⊕ Y i):= (fare (hl i) u (S i)).uses (Zone F i)
 have hv:Folds p L (estate hl (Zone F) S u) v fun w i r=>draft (F.forecast w) (ember C F A m w i r):=fun i hi j=> Claim.draft_budget (H i hi j) (show Beam L R F.forecast from shorter S le_rfl N)
 intro i hi j; apply Carry.mono (hv i hi j); intro w
 have hh:= mark_crop (lastChannel (F.fine w) (F.coarse w)).native (T:=draft (F.forecast w) (ember C F A m w i j)) (B:=realm (hl w) u (S w)) (y:= (Step.combine (F.fine w) (F.coarse w)).pos); rw [Budget.Channel.native_paid] at hh; exact hh

variable (I:Widths p L hl (Gate F) d S T u b m n v w A B)(G:Fund p L hl (Zone F) (u+b) (now F C) F.lineL)
 (h:Beam L (home hl (Zone F) u) F.forecast)
include I
lemma enter_widths : Widths p L hl (Zone F) d S T u b m n v w (promote F A) (promote F B):= ⟨I.rays,I.nonneg,I.limit₁,I.limit₂,entryPays F I.pay₁,entryPays F I.pay₂,fun i=> ranks_offer _ _ (I.rank₁ i),fun i=>ranks_offer _ _ (I.rank₂ i),fun i=>sym_offer _ _ (I.sort₁ i),fun i=>sym_offer _ _ (I.sort₂ i)⟩
include G h
lemma separate : Folds p L (estate hl (Exit F) (groupUp S T) u) (pledge v w d l b) fun i=> (F.grid i).each (m+n) (C i) (accord (A i) (B i))-accord ((F.grid i).each m (C i) (A i)) ((F.grid i).each n (C i) (B i)) := by
 let H:= enter_widths F I
 let T':=fun i=>treatment F.lineL (now F C) (promote F A) false i
 let S':=fun i=>treatment F.lineL (now F C) (promote F B) false i
 let U':=fun i=>treatment F.lineL (now F C) (fun i=>accord (promote F A i) (promote F B i)) false i
 let Z i:= U' i- composeT (T' i) (S' i)
 let α:= estate hl (Zone F) (groupUp S T) u; let f w:= (lastChannel (F.fine w) (F.coarse w)).native
 let k₀ i:= m+n+3*i; let B':= ember C F B n; let A':= ember C F A m
 let W i:=heated k₀ (Z i)
 have ht:Folds p L α (pledge v w d l b) W:= fun i he r=> Claim.sum _ (Finset.range (m+n+3*i+1)) fun t _=> H.first_joins G false t i he r

 intro e he r
 let α' := estate hl (Exit F) (groupUp S T) u
 have HX: Claim L α' (pledge v w d l b) fun w=> crop (f w) (draft (F.forecast w) (W w e r)):=by
    apply Carry.mono (Claim.draft_budget (ht e he r) (shorter (groupUp S T) le_rfl h)); intro w
    have hh:= mark_crop (lastChannel (F.fine w) (F.coarse w)).native (T:=draft (F.forecast w) (W w e r)) (B:=realm (hl w) u (groupUp S T w)) (y:= (Step.combine (F.fine w) (F.coarse w)).pos); rw [Budget.Channel.native_paid] at hh; exact hh
 convert HX using 1
 ext1 i
 let K:= F.lineL i; let Γ:= now F C i; let A'':=promote F A i; let B'':=promote F B i
 have hP:= Brief.time_once (T' i) (S' i) (timeMark K Γ A'' (G.vac i) (H.rank₁ i) (H.sort₁ i) false) (timeMark K Γ B'' (G.vac i) (H.rank₂ i) (H.sort₂ i) false) (Brief.markend K Γ A'' (G.vac i) false (H.rank₁ i)) (Brief.markend K Γ B'' (G.vac i) false (H.rank₂ i))
 have hS : W i e r= heated k₀ (U' i) e r-accord (A' i) (B' i) e r:=by
    unfold W;change ∑ t∈Finset.range (k₀ e+1), (U' i t e r-composeT (T' i) (S' i) t e r)=_
    rw [Finset.sum_sub_distrib]; exact congr_arg (heated k₀ (U' i) e r- ·) (congr_fun (congr_fun hP e) r)
 have hU : quota (heated k₀ (U' i) e r) 1 ≠ ⊤:= packable _ _ fun k _=> G.price H.union_price false le_rfl (fun i=> ENNReal.mul_ne_top (I.limit₁ i) (I.limit₂ i)) i k e he r
 have hA : Bill (A' i) e := fun t hx r=> packable (Finset.range (m+3*t+1)) _ fun k _=> G.price H.pay₁ false le_rfl H.limit₁ i k t (hx.trans he) r
 have hB : Bill (B' i) e := fun t hx r=> packable (Finset.range (n+3*t+1)) _ fun k _=> G.price H.pay₂ false le_rfl H.limit₂ i k t (hx.trans he) r
 obtain ⟨c,hc,U⟩:=h
 have h' : ember C F (fun i=> accord (A i) (B i)) (m+n) i=heated k₀ (U' i):=by unfold ember promote; rw [ticket_offer]; rfl
 change crop (f i) (draft (F.forecast i) (ember C F (fun i=> accord (A i) (B i)) (m+n) i e r))-accord (fun e j=> crop (f i) (draft (F.forecast i) (A' i e j))) (fun e j=>crop (f i) (draft (F.forecast i) (B' i e j))) e r=crop (f i) (draft (F.forecast i) (W i e r))
 have h'M:= row_to_sup (U i).1
 rw [h',← provision (f i) (K:=F.forecast i) (hc.cost i) h'M (A' i) (B' i) hA hB (end_ranks m false (H.rank₁ i) (G.vac i)) (end_ranks n false (H.rank₂ i) (G.vac i)), hS,draft_minor _ (hc.cost i) h'M _ _ hU (parent (A' i) (B' i) hA hB e le_rfl r)]; rfl
end YM.RegulatorIR.Cluster
