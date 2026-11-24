import YM.RG01Estimate.Starscope
/-! # Choose joint posting for any gauge-side candidate ledger. Preserve paid e forecasts as numbered, no recalculation implicit. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Caddy
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Window Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Shoot Precision SectorMeasure Oriented Reserves
open PhysicalNext PhysicalNext.Repeat Height Beam Brim Match Song
open Next.Scheduling AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Meadow Marlin Trio
open Geo Footprint Animals Abacus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c:Side}(p:BudgetPoint)(A:Listing G c) (M: ℕ→RegularAddress c)
  (F:Collection.Source G c) (P : ℕ→ Config G c→ℝ)
-- retain all hard numbering, and make spaces separated on labels.
def e:= numbering (ℕ⊕ℕ)
def stores : Listing G c:= ⟨Sum.elim A.reg M ∘ e,A.hard⟩
def insertP (V:ℕ→ Config G c→ℝ) := Sum.elim V P ∘ e
def lefty := insertP (0:ℕ→ Config G c→ℝ) P
def righty := insertP P 0
-- notation issue orientation: insertP P V= Sum.elim V P

def posted := Collection.Source.mk (lefty F.logRead) F.hardRead

theorem preserve (U:Config G c)(D:PathData G)(b:Clip)(β τ γ : ℝ) : earlyValue A D b p F β τ γ U= earlyValue (stores A M) D b p (posted F) β τ γ U:= by
   unfold earlyValue Rep.eval Rep.exponent; dsimp only [Collection.frozen]
   have h:(A.read F).additive p U=((stores A M).read (posted F)).additive p U:= by
       unfold Activities.additive
       let f i:= (A.read F).regularOccurrence p i U
       let g i:= ((stores A M).read (posted F)).regularOccurrence p i U
       have hx (i:ℕ) : g (e.symm (.inl i))=f i:= by
          unfold g f Activities.regularOccurrence
          dsimp only [Listing.read,posted,lefty,insertP,stores,Function.comp_apply]; rw [e.apply_symm_apply]; rfl
       have hv (i:ℕ) : g (e.symm (.inr i))=0:= by
          unfold g Activities.regularOccurrence
          dsimp only [Listing.read,posted,lefty,insertP,stores,Function.comp_apply]; rw [e.apply_symm_apply]; simp [masked]
       let j:ℕ↪ℕ:= ⟨fun i=>e.symm (.inl i),e.symm.injective.comp Sum.inl_injective⟩
       change ∑' i,f i=∑' i,g i; symm; refine tsum_eq_tsum_of_ne_zero_bij (fun i:support f=> j i.val) (j.injective.comp Subtype.val_injective) ?_ (fun i=> hx i.val) -- lemma check
       intro i hy; cases h:e i with
       | inl x=> have hs:e.symm (.inl x)=i:=e.symm_apply_eq.mpr h.symm; exact ⟨⟨x,(show f x ≠0 from (hx x).symm ▸ hs.symm ▸ (show g i≠0 from hy))⟩,hs⟩
       | inr x=> exact False.elim (hy (show g i=0 from (congr_arg g (e.symm_apply_eq.mpr h.symm).symm).trans (hv x)))
   rw [h]; rfl

lemma posting_bounds {f y:ℕ→ Config G c→ℝ} {z v:ℝ}(he: Meadow.Budget p A.reg f z)(hv: Meadow.Budget p M y v) : Meadow.Budget p (stores A M).reg (insertP y f) (z+v):= by
   obtain ⟨i,hi,h'⟩:=Acquire.budget_concat he hv; exact ⟨i ∘ e,fun j=>Cost.equiv e (hi j),fun j=> h' (e j)⟩
variable (b : Signed)(s:Site c)
structure Mirrors (v: ℕ→ Config G c→ℝ) where
   walks : Equiv.Perm ℕ
   hooks (i): (M (walks i)).site=Lattice.affine b s (M i).site
   hues (i): (M (walks i)).support=(M i).support.image (Lattice.affine b s)
   posts (i): v (walks i)=v i ∘ pull b s

lemma Moves {K:ℕ→ Config G c→ℝ} (X : (A.read F).Moves b s)(h : Mirrors M b s K) :
      Nonempty (((stores A M).read (revise (posted F) (insertP K F.logRead))).Moves b s):= by
    let v:=Equiv.sumCongr X.ep h.walks
    let r:= Refrain.congo e v
    let f:= Sum.elim A.reg M; let U:= Sum.elim F.logRead K
    have hx i: (f (v i)).site=Lattice.affine b s (f i).site ∧ (f (v i)).support=(f i).support.image (Lattice.affine b s) ∧ U (v i)=U i ∘ pull b s:= by
       rcases i with i|i; exact ⟨X.reg_site _,X.reg_support _,funext (X.valuesE _)⟩
       exact ⟨h.hooks _, h.hues _, h.posts _⟩
    have hu i : e (r i)= v (e i):= Refrain.perch ..
    exact ⟨⟨r,X.kp,(fun i=> hu i|>.symm ▸ (hx (e i)).1 : ∀ i,(f (e (r i))).site=_),(fun i=> hu i|>.symm ▸ (hx (e i)).2.1 : ∀ i,(f (e (r i))).support=_),X.forced_support,X.forced_inventory,X.forced_tests,(fun i P=> by change U (e _) P=_; rw [hu]; exact congr_fun (hx (e i)).2.2 _),X.valuesK⟩⟩

lemma nil_move (h : (A.read F).Moves b s) (g: ℕ→ Config G c→ℝ) (hp:∀ i,g (h.ep i)=g i ∘ pull b s): Nonempty ((A.read (revise F g)).Moves b s):= ⟨⟨h.ep,h.kp,h.reg_site,h.reg_support,h.forced_support,h.forced_inventory,h.forced_tests,fun i=>congr_fun (hp i), h.valuesK⟩⟩

-- pack Rack paired by e for P_diff = -P0 (candidate low) + input P'_low
variable {r : ℕ}{V W : ℕ→ Config G c → ℝ}(N: Rack A r V) {A' : Listing G c}(J:Rack A' r W)

def signedR : Rack (stores A A'.reg) r (insertP (-W) V) where
    atW:= (Finset.disjSum N.atW J.atW).map e.symm.toEmbedding
    seat:= Sum.elim N.seat J.seat ∘ e
    bound i hi:= by
       simp only [mem_map_equiv,Equiv.symm_symm] at hi
       dsimp only [insertP, Function.comp_apply]
       cases h:e i with
       | inl a=> exact N.bound _ (fun hx=> hi (h ▸ (inl_mem_disjSum.mpr hx)))
       | inr a=> change -W a=0; rw [J.bound _ (fun hx=> hi (h ▸ (inr_mem_disjSum.mpr hx))),neg_zero]
    sums i hi:= by
       simp only [mem_map_equiv,Equiv.symm_symm] at hi; dsimp only [insertP, Function.comp_apply]; rcases h:e i with i|i <;> rw [h] at hi
       exact N.sums _ (inl_mem_disjSum.mp hi); exact J.sums _ (inr_mem_disjSum.mp hi)
    paid i hi:= by
       simp only [mem_map_equiv,Equiv.symm_symm] at hi; dsimp only [Function.comp_apply]; rcases h:e i with i|i <;> rw [h] at hi
       exact N.paid _ (inl_mem_disjSum.mp hi); exact J.paid _ (inr_mem_disjSum.mp hi)
    priced i hi:= by
       simp only [mem_map_equiv,Equiv.symm_symm] at hi; dsimp only [Function.comp_apply,stores]; rcases h:e i with i|i <;> rw [h] at hi
       exact N.priced _ (inl_mem_disjSum.mp hi); exact J.priced _ (inr_mem_disjSum.mp hi)

lemma pacts : (signedR A N J).polygon=N.polygon-J.polygon:= by
   funext i; simp only [Rack.polygon, Pi.sub_apply]
   unfold signedR; dsimp only [Rack.seat,Rack.atW,insertP,Function.comp_apply]; rw [sum_map,sum_disjSum]; simp only [Equiv.toEmbedding_apply, e.apply_symm_apply, Sum.elim_inl, Sum.elim_inr,Pi.neg_apply, smul_neg,sum_neg_distrib,sub_eq_add_neg]
end YM.RG01Estimate.Caddy
