import YM.OPE.Compatible.Satin.Fold
import YM.OPE.Compatible.Lux.Orders
/-!
# Transfer whole discrepancy plus subtraction of another root vector for arbitrary multi-word report.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cov.Display
open Function Filter MeasureTheory Survey
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book} (U:Spec.Final C f S)
variable {I J B l:Type} [FI : Fintype I] [FJ : Fintype J] [Fintype B] {φ : Filter l} {T k : l → ℝ} {n:ℕ} {z:l→ S.Field n}
-- arity I compared with a finite sum of words of arity J, after subtracting z
lemma allotted (O : l → E4) (X : l → I → E4) (Y : l → J → E4)
    (p : l → I → S.Tag) (q : B → l → J → S.Tag) (a : B → l → ℂ)
    (hT : Tendsto T φ atTop) (hp : ∀ᶠ i in φ,0 ≤ k i)
    (hx : Tendsto (fun i => away (X i) (O i)) φ (𝓝 0))
    (hx' : ∀ᶠ i in φ, Injective (X i))
    (hy : Tendsto (fun i => away (Y i) (O i)) φ (𝓝 0))
    (hy' : ∀ᶠ i in φ, Injective (Y i))
    (h : ∀ (K:Type) [Fintype K] (w : K → S.Tag) (y : l → K → E4) {δ : ℝ},
      0 < δ → (∀ᶠ i in φ, ClearOf (O i) (y i) δ) → PaidWeight φ T k (fun i =>
        kernel S (beside (X i) (y i)) (beside (p i) w) - (∑ b, a b i *
          kernel S (beside (Y i) (y i)) (beside (q b i) w))-Cov.insert S S (O i) (y i) w _ (z i))) :
    PaidWeight φ T k (fun i => ray U n (X i) (p i) (O i) -
        (∑ b, a b i • ray U n (Y i) (q b i) (O i))-z i) := by
  let N : (Unit⊕B)⊕Unit → Type := Sum.elim (Sum.elim (fun _ => I) (fun _ => J)) (fun _=>Unit)
  let w (j:l):= sole (⟨n,z j⟩: S.Tag)
  let t : (b : (Unit⊕B)⊕Unit) → l → N b → E4 := Sum.rec (Sum.rec (fun _ => X) (fun _=>Y)) (fun _ i=>sole (O i))
  let v : (b : (Unit⊕B)⊕Unit) → l → N b → S.Tag := Sum.rec (Sum.rec (fun _ => p) q) (fun _=>w)
  let c : (Unit⊕B)⊕Unit → l → ℂ := Sum.elim (Sum.elim (fun _ _ => 1) (fun b i => - a b i)) (fun _ _=> -1)
  let F : Fintype Unit:=inferInstance; letI NF : ∀ b, Fintype (N b) := Sum.rec (Sum.rec (fun _ => FI) (fun _ => FJ)) (fun _=> F)
  have he : Fits N O t φ := by
    constructor
    · rintro (⟨b|b⟩|t)
      exact hx
      exact hy
      refine tendsto_const_nhds.congr fun i=>?_ ; exact funext fun _=> (sub_self (O i)).symm
    rintro (⟨b|b⟩|t)
    exact hx'
    exact hy'
    exact Eventually.of_forall fun i=> injective_of_subsingleton (sole (O i))
  refine PaidWeight.alter (extendList U (a:=c) (p:=v) hT hp he ?_ n) ?_
  · intro M F' p y δ hδ hh; apply PaidWeight.alter (h _ p y hδ hh)
    filter_upwards [Fits.separated _ _ _ he (.inr ()) _ hδ hh] with i hi
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]; simp only [Fintype.sum_unique]
    change _ = (1 * _ + ∑ b:B, (-a b i)* kernel S (beside (Y i) (y i)) (beside (q b i) p))+ (-1)* kernel S (beside (sole (O i)) (y i)) (beside (w i) p)
    rw [Cov.insert_apply S U.room.kernel.laws.toSymmetric (fun _=>le_rfl) _ _ _ _ _  hi ,one_mul]; simp_rw [neg_mul,Finset.sum_neg_distrib,one_mul,sub_eq_add_neg]; rfl
  filter_upwards with i
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]; simp only [Fintype.sum_unique]
  change ((1:ℂ) • (ray U n (X i) _ _) + ∑ b:B, (-a b i) • ray U n _ (q b i) _) + (-1:ℂ) • ray U n (sole (O i)) (sole (⟨n,z i⟩:S.Tag)) (O i)=_
  unfold ray; rw [show away (sole (O i)) (O i)=sole 0 from funext fun _=> sub_self _,ascend_fix _ U.phase.transport.spots U.room.kernel U.phase.transport.motion]; simp only [one_smul,neg_smul,Finset.sum_neg_distrib,sub_eq_add_neg]; try rfl
lemma readFZero (a:Tones U)(i: Mode U.sector.derivatives)(P:Prescription U.sector.derivatives)(h:i.fst<a.fst):
    (legends U).readIn a.fst a (P.loaded i a.fst)=0:=by
    let n:=a.fst; let V:=legends U; let W:= V.readIn n a
    have hb: (facets U).part a.fst n (P.loaded i n)=0:= by rw [P.cost _ ((full_bands ..).2 h.le), MultipleContact.Splitting.part_rise (facets U) U.room.kernel.laws.toSymmetric U.phase.transport.injection h.le,MultipleContact.Splitting.beyondZero (facets U) h,LinearMap.zero_apply]
    exact Eq.trans (V.readIt n a _) ((congr_arg ((V.axisSet n).coord a.snd) (Subtype.ext hb)).trans (map_zero _))
lemma exact_grade (P:Prescription U.sector.derivatives)(h:P.Coherent)(a:Tones U): ∃ b:Mode U.sector.derivatives,b.fst=a.fst:=by
    by_contra! hf
    let V:=legends U; let n:=a.fst; let W:= V.readIn n a; let v:= V.there n a
    have ht : W v=1:= by unfold v W; rw [V.one_grade U.room.kernel.laws.toSymmetric U.phase.transport.injection _ _ _ ((shadows ..).2 le_rfl) ((shadows ..).2 le_rfl),if_pos rfl]
    have hv : W v=0:=by
       conv_lhs => rw [← (h n).rebuilds v,map_sum]
       simp_rw [map_smul]; exact Finset.sum_eq_zero fun b hb=> (by rw [show W (P.loaded b n)=0 from readFZero U a b P ((full_bands .. |>.mp hb).lt_of_ne (hf b)),smul_zero])
    exact one_ne_zero (ht.symm.trans hv)
end YM.OPE.Cov.Display
