import YM.Overlay.Pays
import YM.MergeProof.Magma
import YM.Next.FOUNDATIONS.Regular
import YM.Extra.ITERATION_NO_LOSS.Sums
/-!
# Support-bill adapter. Literal marked E/K, on `Overlay.Bands.Radial`.

All logarithmic Donor leaves (full Dictionary underlying Ω) supplied
origin/table/exponents. Map uses `univ` ONLY for filler log tags and for
log tags violating their incidence and THEREFORE CERTIFIED identically zero.
No budget halo bleed. Fleece false-tag/extraTest stays on each slot.
Supports actual carrier counts for `supBounds`, especially at all
re-centered origins.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Overlay.GapsLocal
open Finset Function Filter MeasureTheory Lattice Wilson RG Marker Push Next.Foundations AbsoluteSums GridApprox.Nil
open MergeProof Merge Accent Extra.Iteration
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical

variable {G:Gauge}{n:Side}{V:Type}[Fintype V][Nonempty V][DecidableEq V]{B:Marker.Census V}
variable {ι:Type}[Countable ι] (R:RG.Rep G n)(S:ι→Support n)(o:V→Site n)(w:V→ℝ){h c k :ℝ}

abbrev Said (B:Marker.Census V):= {u:B.Mode // u.val.Nonempty}
def pinned (X:Support n)(u:Said B):= ∀ i∈ u.val.val, o i∈ X
abbrev concern (ι:Type)(B:Marker.Census V):= ℕ ⊕ (ι×Said B)
abbrev forceLabel (B:Marker.Census V):= ℕ ⊕ Said B
variable {w}
def landfall (p:concern ι B) :Support n:= match p with | .inl _=>univ| .inr (i,j) => if pinned o (S i) j then S i else univ
private def coin (B:Marker.Census V): Said B:=⟨B.fire Classical.ofNonempty, singleton_nonempty _⟩
def pointing (p:concern ι B): Said B:= match p with| .inl _=> coin B| .inr (_,j)=> j
def indicating (p:forceLabel B): Said B:= match p with| .inl _=> coin B| .inr i=> i

def commitLabel (B:Marker.Census V) (ι:Type)[Countable ι] (q:ℕ): concern ι B:= numbering (concern ι B) q
variable (r:V→ℂ)(P:ι→ B.Mode → Config G n → ℂ)(K:ℕ→ Config G n→Poly B)
private def send_p : concern ι B → Config G n→ℂ
   | .inl _ => 0
   | .inr (i,j)=> P i j.val
private def send_k (i:ℕ)(U:Config G n):forceLabel B→ℂ
   | .inl _ => 0
   | .inr j=> (K i U).part j.val

def surface : Bands B R where
   origins:=o
   units:=r
   support:=landfall S o ∘ numbering (concern ι B)
   rays:=Subtype.val ∘ pointing ∘ numbering (concern ι B)
   marks _ q:= (indicating (numbering (forceLabel B) q)).val
   H:= send_p P ∘ numbering (concern ι B)
   entries i j U:= send_k K i U (numbering (forceLabel B) j)
-- readout with no omission: when pinned, literally. When degree empty or footprint fails, inert.
omit [Fintype V] in -- Bands extra uses? here no no. keep when used H proof etc
lemma committedE (p:ι)(j:Said B) (i:ℕ) (hi: (numbering (concern ι B)) i= .inr (p,j)) (h:pinned o (S p) j):
    let D:= surface R S o r P K
    D.support i = S p ∧ D.rays i=j.val ∧ D.H i=P p j.val:=by
  intro D; unfold D surface; dsimp only [Function.comp_apply]; simp only [hi, landfall,if_pos h,pointing,send_p,true_and]
omit [Fintype V] in
lemma committedK (j:Said B)(p i:ℕ)(hi:numbering (forceLabel B) i= .inr j):let D:= surface R S o r P K
    D.marks p i=j.val ∧ D.entries p i=fun U=> (K p U).part j.val:=by intro D; unfold D surface; simp only [hi, send_k, indicating, true_and]

local notation "D'" => surface R S o r P K
variable (hp:∀ i (u:Said B),¬pinned o (S i) u→ P i u.val=0)(hP:∀ i u,R.p.Regular (S i) (P i u))
    (hK:∀ i u,¬(R.activities.forced i).eligible R.p.threshold u→ K i u=0)
    (hA:∀ i,Accent.Borne o (R.activities.forced i).support (K i) R.p.threshold)
omit [Countable ι] [Fintype V] [Nonempty V] [DecidableEq V] in
private lemma regular_empty (p:BudgetPoint)(S:Support n)(o:Site n):p.Regular S (0:Config G n→ℂ)∧ p.supBounds o S (0:Config G n→ℂ) 0:=by
   have h:= regular_bound_sum (G:=G) (P:=p) (s:=S) (o:=o) (∅:Finset Unit) 0 0 (fun i hi=> False.elim (Finset.notMem_empty i hi))
   simpa only [sum_empty] using h

include hp hP hK hA
omit [Fintype V] in
lemma displayed : (surface R S o r P K).Active:=by
   have ht (i:concern ι B)(j:V)(h:j∈(pointing i).val.val): o j∈ landfall S o i:=by
      cases i with
      | inl i=> exact mem_univ _
      | inr p=> rcases p with ⟨p,j⟩; simp only [landfall]; split; next h'=> exact h' _ h
                next=> exact mem_univ _
   have HH(i:concern ι B):R.p.Regular (landfall S o i) (send_p P i):=by
      cases i with
      | inl i=> exact (regular_empty _ _ 0).1
      | inr p=> rcases p with ⟨i,j⟩; simp only [landfall,send_p]; split
                next he=> exact hP i j.val
                next h=> rw [hp i j h]; exact (regular_empty _ _ 0).1
   have h (i:ℕ)(z:forceLabel B): let f U:= send_k K i U z; (f≠ 0 → pinned o (R.activities.forced i).support (indicating z)) ∧ UsesFinal R.p.threshold (R.activities.forced i).support f ∧ (∀ U, f U≠0 → (R.activities.forced i).eligible R.p.threshold U) ∧ Measurable f ∧ GaugeInvariant f:=by
      intro f; rcases z with p|p; · exact ⟨fun h=>(h rfl).elim,fun _ _ _ _=>rfl,fun _ h=>(h rfl).elim,measurable_const,fun _ _=>rfl⟩
      have hs:=hA i; refine ⟨fun h=>?_,fun U V hu hv=>congr_arg (fun g=>g.part p.val) (hs.home _ _ hu hv),fun U h=>?_, hs.me _,fun v U=> congr_arg (fun g=>g.part p.val) (hs.turns v U)⟩
      · by_contra he; exact h (funext fun U=> hs.scope U p.val he)
      by_contra hn; apply h; simp only [f,send_k]; rw [hK _ _ hn,Poly.part_nil]
   exact ⟨fun i=> (pointing (numbering (concern ι B) i)).prop,fun i=> ht _,fun i=> HH (numbering _ i), fun i j=> (indicating (numbering (forceLabel B) j)).prop,fun i j=> (h i (numbering _ j)).1,fun i j=>(h i (numbering _ j)).2.1,fun i j=>(h i (numbering _ j)).2.2.1,fun i j=> (h i (numbering _ j)).2.2.2.1,fun i j=> (h i (numbering _ j)).2.2.2.2⟩

omit hP hA hK hp
-- both spends in physical, non-negative rooted norm
variable (v:V→ℝ)(hv:∀ i,0 < v i)
omit [Nonempty V] [Fintype V] [Countable ι] in
private lemma singleForecast (u:B.Mode→ℝ)(h:∀ i,0 ≤ u i) (f:Said B→ℝ)(he:∀ i,0≤ f i)(hh:∀ i:Said B,f i≤ u i.val)(t:ℝ)(ht:∑ i,u i ≤ t): SumBudget f t := by
   refine ⟨he,Summable.of_finite,?_⟩; rw [tsum_fintype]; apply le_trans (sum_le_sum (s:=univ) (fun i _=> hh i)); rw [← Finset.sum_image Subtype.val_injective.injOn]; exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>h i)).trans ht

omit [Fintype V] [Nonempty V] [DecidableEq V] [Countable ι] in
private lemma zeroCover {α:Type} (f:α→ℝ)(h:∀ i,f i=0): SumBudget f 0:=by rw [funext h]; exact Extra.Multi.Budget.zero le_rfl
include hv hA hp
variable (u w e κ:ℝ)
omit [Fintype V] in
theorem funds (hk:Towed v (fun i=>(R.activities.forced i).support) K R.p.B R.p.supportExponent (e*κ))(hu:∀ i,v i * ‖r i‖ ≤ u) (hκ:0<κ)(a:ι→ B.Mode→ℝ)(ha:∀ i j,0≤ a i j)(ht:Ac.Hit S R.p.B (fun i=> wordsPrice v (a i)) R.p.supportExponent w)(hY:∀ i j k,k∈S i→R.p.supBounds k (S i) (P i j) (a i j)): (surface R S o r P K).Radial v u w e κ:=by
   let g (p:concern ι B):= match p with| .inl _=> 0| .inr (i,j)=> if pinned o (S i) j then a i j.val else 0
   have hg(p:concern ι B):0≤g p∧∀ x∈ (pointing p).val.val,R.p.supBounds (o x) (landfall S o p) (send_p P p) (g p):=by
      rcases p with l|⟨p,j⟩; · exact ⟨le_refl _, fun x _=>(regular_empty _ _ _).2⟩
      simp only [g,pointing,landfall,send_p]; split
      next h=> exact ⟨ha p _,fun i hi=>hY p j.val _ (h i hi)⟩
      next hn=> rw [hp _ _ hn]; exact ⟨le_rfl,fun i _=> (regular_empty _ _ _).2⟩
   obtain ⟨b,hb,hV,hB⟩:=hk; choose f h' hF hφ using hB
   let X i:= (R.activities.forced i).support; let a'(p:ℕ)(k:forceLabel B):= match k with | Sum.inl _ => 0 | Sum.inr j=> if pinned o (X p) j then f p j.val else 0
   have hA'(p:ℕ)(k:forceLabel B):0≤a' p k∧∀ U, ‖send_k K p U k‖≤ a' p k:=by
      cases k with
      | inl k=> exact ⟨le_rfl,fun U=> (by change ‖(0:ℂ)‖≤0; rw [norm_zero])⟩
      | inr j=> simp only [a']; split
                next h=> exact ⟨h' p j.val,fun U=>hF p U j.val⟩
                next h=> exact ⟨le_rfl, fun U=> by simp only [send_k]; rw [(hA p).scope U j.val h,norm_zero]⟩
   refine ⟨hv,hu,hκ,⟨g ∘ numbering _,fun i=> hg _, fun i=> Cost.equiv (numbering (concern ι B)) (f:=fun p=> if i∈ (pointing p).val.val then Poly.toll v (pointing p).val * R.p.mass (landfall S o p) (g p) else 0) ?_⟩,⟨fun i=> a' i.1 (numbering _ i.2),fun i j=> hA' _ _, fun i=> ?_⟩⟩
   · rw [← zero_add w]; refine Cost.sum (by apply zeroCover; intro x; simp [g,BudgetPoint.mass]) (Cost.product (f:=fun j=> if o i ∈ S j then wordsPrice v (a j)*Real.exp (R.p.supportExponent*coverNumber R.p.B (S j)) else 0) (ht _) (fun j=> ?_))
     let y:=Real.exp (R.p.supportExponent* coverNumber R.p.B (S j)); have hG(k:B.Mode):0≤ Poly.toll v k * a j k:= mul_nonneg (Poly.worth hv _).le (ha j _)
     by_cases h:o i∈ S j; swap
     · rw [if_neg h]; refine zeroCover _ (fun x=>?_); split; next hj=> simp only [g]; rw [if_neg (show ¬ pinned o (S j) x from fun hh=>h (hh i hj))]; simp only [BudgetPoint.mass]; ring
       next=>rfl
     rw [if_pos h]; refine singleForecast (fun k:B.Mode=> (Poly.toll v k * a j k)*y) (fun k=> mul_nonneg (hG _) (Real.exp_pos _).le) _ ?_ ?_ _ (by rw [← Finset.sum_mul]; rfl)
     · intro x; split; exact mul_nonneg (Poly.worth hv _).le (mul_nonneg (Real.exp_pos _).le (hg (.inr (j,x))).1); rfl
     intro x; split
     next hj=>
       simp only [pointing,g,landfall]; split; next h=> simp only [BudgetPoint.mass,y]; ring_nf; rfl
       next=> simp only [BudgetPoint.mass]; rw [mul_zero,mul_zero]; exact mul_nonneg (hG _) (Real.exp_pos _).le
     next=> exact mul_nonneg (hG _) (Real.exp_pos _).le
   -- apply product with ∀ p hit
   apply Cost.product (hV (o i)); intro p; let y:= Real.exp (R.p.supportExponent*coverNumber R.p.B (X p)); let B₀ (k:B.Mode):= Poly.toll v k * (f p k); have hP(k):0 ≤ B₀ k := mul_nonneg (Poly.worth hv _).le (h' p _)
   apply Cost.equiv (numbering (forceLabel B)) (f:=fun k=>if i∈ (indicating k).val.val then Poly.toll v (indicating k).val * R.p.mass (X p) (a' p k) else 0)
   by_cases hp:o i∈X p; swap
   · rw [if_neg (show o i ∉ (R.activities.forced p).support from hp)]; refine zeroCover _ (fun k=>?_)
     rcases k with k|k
     · split <;> first | rfl | simp [a',BudgetPoint.mass]
     split; next hj=> simp only [a']; rw [if_neg (show ¬ pinned o (X p) k from fun hh=> hp (hh i hj))]; simp only [BudgetPoint.mass]; ring
     next=> rfl
   rw [if_pos (show o i∈ (R.activities.forced p).support from hp)]
   refine Cost.enlarge (Cost.sum (B:= b p * y) (A:=0) ?_ ?_) (by rw [zero_add])
   · apply zeroCover; intro k; split
     next=> simp only [BudgetPoint.mass,a']; ring
     next=> rfl
   refine singleForecast (fun k:B.Mode=>B₀ k*y) (fun k=> mul_nonneg (hP k) (Real.exp_pos _).le) _ ?_ ?_ _ ?_
   · intro k; split; exact mul_nonneg (Poly.worth hv _).le (mul_nonneg (Real.exp_pos _).le (hA' p (.inr k)).1); rfl
   · intro k; split
     next h=> simp only [a',B₀,indicating]; split
              next h=> simp only [BudgetPoint.mass,y]; ring_nf; rfl
              next=> simp only [BudgetPoint.mass]; rw [mul_zero,mul_zero]; exact mul_nonneg (hP _) (Real.exp_pos _).le
     next=> exact mul_nonneg (hP _) (Real.exp_pos _).le
   rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hφ _) (Real.exp_pos _).le
omit hA hp hv
include hp
variable (hk:∀ i U,(K i U).part B.quiet=Complex.ofReal (R.activities.K i U))
include hk
-- literal E, K law at post – no missing zero-flag assumption. Physical
-- pointwise truth via all fields, norms always in the surface ledger.
omit hp [Fintype V] in
lemma everyK (U:Config G n)(i:ℕ):(D').each i U= K i U :=by
   let e:=numbering (forceLabel B); let f (k:forceLabel B):= Poly.send (indicating k).val (send_k K i U k)
   have hl: HasSum (f ∘ (Sum.inl : ℕ→forceLabel B)) 0 := by simp [Function.comp_def,f,send_k]
   have hr: Summable (f ∘ Sum.inr):= Summable.of_finite
   have hz:(∑' k, f (e k))= (∑' k, f k):=e.tsum_eq _
   unfold Bands.each; rw [show (∑' j,(D').tagged i j U)= _ from hz,Summable.tsum_sum hl.summable hr]; change _+ ((∑' i,(f ∘ Sum.inl) i)+_)=_ -- parentheses
   rw [hl.tsum_eq, tsum_fintype,zero_add]; let a:= B.quiet; let l:=Finset.univ.filter (fun i:B.Mode=> i.val.Nonempty); let p:=K i U; let v (i':B.Mode):= Poly.send i' (p.part i')
   have h : l=(univ.erase a):=by
      ext i; constructor
      · intro h; exact mem_erase.mpr ⟨fun hx=> nonempty_iff_ne_empty.mp ((mem_filter.mp h).2) (Subtype.ext_iff.mp hx),mem_univ _⟩
      intro h; exact mem_filter.mpr ⟨mem_univ _, nonempty_iff_ne_empty.mpr (fun he=> ne_of_mem_erase h (Subtype.ext he))⟩
   rw [← hk]; change v a+(∑ i:Said B,v i.val)=p
   rw [show (∑ i:Said B,v i.val)=∑ i∈l,v i from (Finset.sum_subtype l (by simp [l]) v).symm,h, add_sum_erase _ _ (mem_univ _)]; exact Poly.studs p
omit hk
lemma atAll (U:Config G n)(hc:(D').Active)(hf:(D').Radial v u w e κ):
    (D').extra U=(∑ i:V,Poly.send (B.fire i) (r i))+ ∑' p:ι, ∑ i:Said B,Poly.send i.val (masked R.p.threshold (S p) (P p i.val) U):=by
   let F' := numbering (concern ι B)
   let f (p:concern ι B):= Poly.send (pointing p).val (masked R.p.threshold (landfall S o p) (send_p P p) U)
   have hp' (i): (D').ray i U=f (F' i):= rfl
   have hg(k:ℕ): f (.inl k)=0:=by
      simp [masked,f,send_p]
   have hh: Summable (fun i=>f i):=(F'.summable_iff (f:=f)).1 (((D').bulkBound hc hf U).1.congr hp')
   have hL : HasSum (f ∘ (Sum.inl : ℕ→concern ι B)) 0:=by simp_rw [Function.comp_def,hg]; exact hasSum_zero
   have hR: Summable (fun j=> f (.inr j)):= hh.comp_injective Sum.inr_injective
   unfold Bands.extra; rw [show (∑' i, (D').ray i U)= _ from (tsum_congr hp').trans (F'.tsum_eq f),Summable.tsum_sum hL.summable hR, hR.tsum_prod]; change _+ ((∑' i,(f ∘ Sum.inl) i)+_) = _
   rw [hL.tsum_eq,zero_add]; refine congr_arg (_+·) (tsum_congr fun i=>?_); rw [tsum_fintype]; apply Finset.sum_congr rfl; intro j _; simp only [f,pointing,landfall,send_p]
   split; rfl; next h=> rw [hp _ _ h]; simp [masked]
omit hp [Fintype V] in
lemma splitH {P L V' : ι→ B.Mode → Config G n → ℂ}(a b : V→ℂ) (h:P=L+V'):(surface R S o r P K).H=(surface R S o a L K).H+(surface R S o b V' K).H:=by
   ext i; change send_p P ((numbering _) i) _= _; unfold surface; simp only [Function.comp_apply,Pi.add_apply]; generalize numbering (concern ι B) i=p
   rcases p with j|⟨a,b⟩ <;> simp [send_p,h]
end YM.Overlay.GapsLocal
