import YM.OPE.Compatible.Trees.Splice

/-!
# Cost of replacement and its accounting
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Set Filter Cov Display
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V:Type} [PartialOrder V][OrderBot V][Fintype V] (E:Origin V)
    {G:Gauge} {C:Family G} {F:Extraction.Order} {S:Table C.book} (U:Spec.Final C F S)
    {l:Type}{φ:Filter l} {T:l→ℝ} {t:V→ℝ}{s:l→ V→ ℝ}{X:l→ V→ E4}
    {M η :ℝ}(L:Layer E φ T M η t s X)(Z: Services C F S)
    (P:Finset V)(H:Crown P) {v:V}

def payload (p:V→ S.Tag)(t:V→ℝ) := ∑ i : brim E P, ((p i.val).fst:ℝ)*t (par E i.val)
def demand (p:V→ S.Tag)(t:V→ℝ) (k:ℝ) := payload E P p t-k*t ⊥

def portion (v:V) (p:V→ S.Tag) := bill (picked (glen E P v) p)
lemma portion_root (p:V→ S.Tag) : portion E P ⊥ p=bill (picked (brim E P) p) := by unfold portion; rw [glen_bot]

lemma plateau_pay {v:V} (hv:v∈P) (h:Light P t v) (p:V→S.Tag): payload E P p t=
    (portion E P v p:ℝ)*t v+∑ i:shore E P v, ((p i.val).fst:ℝ)*t (par E i.val) := by
  unfold payload; rw [glen_sum E P v fun i=> ((p i).fst:ℝ)*t (par E i)]
  congr 1; unfold portion bill; rw [Nat.cast_sum,Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h (par E i.val) (((on_brim ..).mp (Finset.mem_filter.mp i.2).1).2.2) (glen_touch E P hv i.2)]; rfl

lemma payload_light (h:Light P t ⊥)(p:V→ S.Tag) : payload E P p t=(bill (picked (brim E P) p):ℝ)*t ⊥ := by
  unfold payload bill; rw [Nat.cast_sum,Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _
  rw [h _ (((on_brim ..).mp i.2).2.2) bot_le]; rfl

include H
lemma painted_pay (p:V→ S.Tag)(hv:v∈rest P)(a:Tones U): payload E (trim P v) (paint U v p a) t=
    a.fst*t (par E v)+∑ i:shore E P v, ((p i.val).fst:ℝ)*t (par E i.val) := by
  unfold payload; rw [trim_sum E P v (fun i=> ((paint U v p a i).fst:ℝ)*t (par E i)) H hv]; unfold paint; rw [update_self]; congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [update_of_ne (shore_ne E P v i.2)]
lemma gross (p:V→ S.Tag)(h:Light P t v)(hv:v∈rest P)(a:Tones U)(k:ℝ) :
    ((portion E P v p:ℝ)-(a.fst:ℝ))*t v+demand E (trim P v) (paint U v p a) t k=
      demand E P p t k-a.fst*jump E t v := by
  unfold demand; rw [painted_pay E U P H p hv,plateau_pay E P (Finset.mem_erase.mp hv).2 h]; dsimp [jump]; ring

-- choose some highest strict edge, even if other subtrees are changing much faster
include L
variable [φ.NeBot]
lemma Light.may : Light P t ⊥ ∨ ∃ v∈ rest P, Light P t v ∧ 0<jump E t v := by
  let B := (rest P).filter fun i => 0<jump E t i
  have hx (v:V)(hv:v∈P) (hg:∀ i∈ B, ¬ v < i) : Light P t v := by
    intro u; apply journey E (P:=fun u => u∈P→ v ≤ u → t u=t v)
    · intro _ e; rw [le_bot_iff.mp e]
    intro i hi ih hw e
    rcases e.lt_or_eq with e|rfl
    · have ht : ¬ 0<jump E t i := fun g=> hg i (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hi,hw⟩,g⟩) e
      exact Eq.trans (le_antisymm (sub_nonpos.mp (le_of_not_gt ht)) (L.order E (H.inner hw) (par_le ..)))
        (ih (H.roots (par_le ..) hw) (touch_par E e))
    rfl
  rcases B.eq_empty_or_nonempty with h|h
  · exact Or.inl (hx ⊥ H.base (fun i hi => (Finset.notMem_empty i (h ▸ hi)).elim))
  right; obtain ⟨v,hv⟩ := B.exists_maximal h
  obtain ⟨hu,ht⟩ := Finset.mem_filter.mp hv.1
  refine ⟨v,hu,hx _ (Finset.mem_erase.mp hu).2 ?_,ht⟩
  exact fun i hi e=> e.not_ge (hv.2 hi e.le)
include Z
lemma shoot_rate (p:V→ S.Tag)(hv:v∈P) (h:Light P t v) (a:Tones U):
  RateLE φ T (fun i=> shoot E U P v a (s i) (X i) p) (((portion E P v p:ℝ)-(a.fst:ℝ))*t v) := by
  have hu := H.inner hv
  have hκ := L.upper_separation E P H h
  have he : RateLE φ T (fun i=>lens U a (picked (glen E P v) (X i)) (picked (glen E P v) p) (X i v))
      (((portion E P v p:ℝ)-(a.fst:ℝ))*t v) := by
    rcases (L.bounds v hu).1.lt_or_eq with h|ht
    · exact step_rate U Z L.flow (picked _ p) hκ
        (L.enveloped E (Subtype.val: ↑(glen E P v)→ V) hu (fun i=>(Finset.mem_filter.mp i.2).2)) h a
    rw [← ht,mul_zero]; rw [← ht] at hκ
    let F := (legends U).readIn a.fst a
    exact (ray_shallow U Z L.flow (picked _ p) hκ
      (L.inch E (Subtype.val: ↑(glen E P v)→ V) hu (fun i=>(Finset.mem_filter.mp i.2).2)) a.fst).linear
        L.flow (LinearMap.toContinuousLinearMap (F.restrictScalars ℝ))
  refine he.congr ?_
  filter_upwards [later (I:=↑(glen E P v)) U a (Layer.fade E L _ hu)] with i hi
  exact Eq.symm (hi _ _ _)
lemma same_light (h:Light P t ⊥) (p:V→ S.Tag)(a:Tones U) :
    RateLE φ T (fun i=>frontierCoefficient E U P a (s i) (X i) p) (demand E P p t a.fst) := by
  have hp := shoot_rate E U L Z P H p H.base h a
  rwa [funext (f:=fun i=> shoot E U P ⊥ a (s i) (X i) p) (g:=fun i=> frontierCoefficient E U P a (s i) (X i) p)
    (fun i=> (direct_bot E U P a (s i) (X i) p).symm),portion_root,sub_mul,← payload_light E P h] at hp

lemma shoots_with {κ:ℝ} (p:V→S.Tag)(h:Light P t v)(hv:v∈rest P)(a:Tones U)(k:ℝ)(u:l→ℂ) (e:RateLE φ T u
    (demand E (trim P v) (paint U v p a) t k-κ)) : RateLE φ T (fun i=> shoot E U P v a (s i) (X i) p*u i)
      (demand E P p t k-(a.fst:ℝ)*jump E t v-κ) := by
  have hp := (shoot_rate E U L Z P H p (Finset.mem_erase.mp hv).2 h a).mul e
  rwa [← add_sub_assoc,gross E U P H] at hp <;> assumption
lemma zip_pay (p:V→S.Tag)(h:Light P t v)(hv:v∈rest P)(a:Tones U)(k:ℝ)(u:l→ℂ) (e:RateLE φ T u
    (demand E (trim P v) (paint U v p a) t k)) : RateLE φ T (fun i=> shoot E U P v a (s i) (X i) p*u i)
      (demand E P p t k) := by
  have hp := (shoot_rate E U L Z P H p (Finset.mem_erase.mp hv).2 h a).mul e
  rw [gross E U P H p h hv] at hp
  exact hp.mono (sub_le_self _ (mul_nonneg (Nat.cast_nonneg _)
    (sub_nonneg.mpr (L.order E (H.inner (Finset.mem_erase.mp hv).2) (par_le ..)))))
end YM.OPE.Arboreal
