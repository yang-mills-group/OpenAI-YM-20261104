import YM.MS.Cylinder.Sites

/-!
# BV derivatives as cylinder operations

The only unrooted infinite sums are regarded as bulk functionals up to translation.
   To apply their differential to any stencil use finite root operation `force`.
   Its derivative gluing includes the constant case.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Cylinder.Lab
open Function Set Finset Koszul Plane
variable {R A B P Q J : Type*} [CommRing R] {p : Sector A} {s:Finset P}

/-! local loop for a pair single type, and arbitrary s map. -/
-- Utility: additivity of sums with support shrinking. `finsum` proof arbitrary.
variable {E : Type*}[AddCommGroup E][Module R E]
lemma sums (s:Finset P) (F:P→E) (h:∀ x,x∉s→ F x=0): ∑ᶠ x,F x=∑ x∈s,F x:= finsum_eq_sum_of_support_subset _ (fun x hx=> Classical.byContradiction fun he=> hx (h x he))
variable (K:P→Seed A P R→ₗ[R] E) (HK: ∀ (F: Seed A P R)(s: Finset P), BoundBy (s:Set P) F→∀ x,x∉s→ K x F=0)
def joinOne (K:P→Seed A P R→ₗ[R] E) (HK: ∀ (F: Seed A P R)(s: Finset P), BoundBy (s:Set P) F→∀ x,x∉s→ K x F=0) : Seed A P R→ₗ[R] E where
    toFun F:=∑ᶠ x,K x F
    map_add' f g:= by obtain ⟨s,hs,hg⟩:= each_side f g; rw [sums s _ (HK (f+g) _ (hs.add hg)), sums s _ (HK f _ hs), sums s _ (HK g _ hg),← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun _ _=> map_add ..
    map_smul' c f:= by obtain ⟨s,hs⟩:= obliges f; rw [sums s _ (HK (c • f) _ (hs.smul c)),sums s _ (HK f _ hs), Finset.smul_sum]; exact Finset.sum_congr rfl fun _ _=> map_smul ..
lemma join_k (F: Seed A P R)(h:BoundBy (s:Set P) F): joinOne K HK F=∑ x∈s,K x F := sums s _ (HK F _ h)
lemma join_total [Fintype P] (F:Seed A P R): joinOne K HK F=∑ x:P,K x F:= join_k K HK F (show BoundBy (↑(Finset.univ (α:=P)):Set P) F from by simp only [Finset.coe_univ,BoundBy, Set.preimage_univ, Uses.entire]) -- lint
abbrev On (A P R : Type*)[CommRing R]:= Seed A P R→ₗ[R] Seed A P R
def heart (i j:A) : On A P R:= joinOne (fun x=> (enter (j,x)).comp (enter (i,x))) (fun F s h x hv=>by change enter _ (enter _ F)=_; rw [notEnter _ h (i,x) (fun hh=> hv hh),map_zero])
lemma heart_by (i j:A)(F:Seed A P R)(h:BoundBy (s:Set P) F): heart i j F=∑ x∈s,enter (j,x) (enter (i,x) F):= join_k _ _ _ h
lemma heart_all [Fintype P](i j:A)(F:Seed A P R): heart i j F=∑ x:P,enter (j,x) (enter (i,x) F):= by unfold heart; rw [join_total]; rfl
lemma heart_stays (i j:A)(F:Seed A P R)(h:BoundBy (s:Set P) F): BoundBy (s:Set P) (heart i j F):= by rw [heart_by _ _ F h]; simp only [BoundBy,sum_stack]; exact Uses.sum (fun x _=> (h.drop _).drop _)
lemma heart_transport {r:P→Q}(i j:A)(F:Seed A P R)(h:BoundBy (s:Set P) F)(hr:InjOn r (s:Set P)):
    transport r (heart i j F) = heart i j (transport r F):= by
    classical
    rw [heart_by i j (transport r F) (s:=s.image r) (by rw [Finset.coe_image]; exact relax F h r),Finset.sum_image hr,heart_by i j F h,map_sum]; apply Finset.sum_congr rfl; intro v hv; rw [← transport_single r hr (enter (i,v) F) (h.drop _) (j,v) hv,← transport_single r hr F h (i,v) hv]; rfl

section tr
variable [AddCommGroup P]
lemma heart_shift (i j:A)(F:Seed A P R)(x:P): Lab.Shift x (heart i j F)=heart i j (Shift x F):= by
    obtain ⟨s,hs⟩:= obliges F; exact heart_transport _ _ _ hs (injOn_univ.mpr (add_right_injective x) |>.mono (Set.subset_univ _))
-- trace density gradient in any position of the translated stencil.
def force (i:A)(y:P) : On A P R:= joinOne (fun x=> (Lab.Shift (y-x)).comp (enter (i,x))) (fun F s h x hv=> by rw [LinearMap.comp_apply,notEnter F h _ (fun hk=> hv hk),map_zero])
lemma force_at (F:Seed A P R)(h:BoundBy (s:Set P) F)(i:A)(y:P): force i y F=∑ x∈s, Lab.Shift (y-x) (enter (i,x) F):= join_k _ _ _ h
lemma forces (F:Seed A P R)(i:A)(x y:P): force i (x+y) F= Lab.Shift y (force i x F):= by obtain ⟨s,hs⟩:= obliges F; rw [force_at F hs,force_at F hs,map_sum]; refine Finset.sum_congr rfl fun i hi=> ?_; rw [shift_add]; congr 2; abel
lemma force_finite [Fintype P] (F:Seed A P R)(i:A)(x:P): force i x F=enter (i,x) (sumHome F):= by
    unfold force; rw [join_total,total_uses,map_sum]; simp_rw [LinearMap.comp_apply,shift_enter F]; simp only [sub_add_cancel]; simpa only [sub_eq_add_neg,Equiv.trans_apply,Equiv.neg_apply, show ∀ y,(Equiv.addLeft x) y=x+y from fun _=>rfl] using Equiv.sum_comp (Equiv.neg P |>.trans (Equiv.addLeft x)) (fun z=> enter (i,x) (Lab.Shift z F)) -- check identity
end tr
end YM.MS.Cylinder.Lab
