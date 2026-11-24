import YM.OPE.Compatible.Trees.Kept
import YM.OPE.Compatible.Trees.Sights

/-!
# Replacing a subtree on a plateau

Arbitrary high horizon makes an arbitrarily low rate error at the *root*,
provided this is a Light subtree with positive gap to parent. No claim of
uniformity for that horizon if geometry changed to a different filter/regime;
the statements we later transfer back to uniform estimates involve only the
*fixed* finite budgets and horizons of the Nest, not this auxiliary horizon.
Proof: spend powers of the one positive gap, exterior fixed data includes
also the finite detector demands at the root. Projection transfer with the
same prescription defined on the replaced frontier configurations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Set Filter Cov Display
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V:Type} [PartialOrder V][OrderBot V][Fintype V] (E:Origin V)
    {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(U:Spec.Final C F S)
    {l:Type}{φ:Filter l}{T:l→ℝ} {t:V→ℝ}{s:l→ V→ ℝ}{X:l→ V→ E4}
    {M η c :ℝ}(L:Layer E φ T M η t s X)(Z: Services C F S)

-- initially all active internal from `heart V`. frontierCoefficient of any frontier.
def frontierCoefficient (P:Finset V) (a:Tones U) (s:V→ ℝ) (x:V→ E4) (p:V→ S.Tag) : ℂ :=
  beam U a (s ⊥) (picked (brim E P) x) (picked (brim E P) p) (x ⊥)
def shoot (P:Finset V) (v:V) (a:Tones U) (s:V→ ℝ) (x:V→ E4) (p:V→ S.Tag) : ℂ :=
  beam U a (s v) (picked (glen E P v) x) (picked (glen E P v) p) (x v)
lemma direct_bot (P:Finset V) (a:Tones U) (s:V→ ℝ) (x:V→ E4) (p:V→ S.Tag) :
    frontierCoefficient E U P a s x p=shoot E U P ⊥ a s x p := by unfold frontierCoefficient shoot; rw [glen_bot]

def paint (v:V)(p:V→ S.Tag)(a:Tones U):V→ S.Tag:= update p v (title U a)

section
-- bridge to drift on truncated basis without needing injectivity of clustered
-- inputs. Works also on full canopy.
variable {I J:Type} [Fintype I][Fintype J]
lemma ink (n:ℕ) (r:Viewers U) (s:ℝ)(x:I→ E4)(p:I→ S.Tag) (o:E4)(y:J→ E4)(w:J→ S.Tag)
    (hy : Injective (beside (sole o) y)) : Cov.insert S (spectator U r) o y w n (trunc U n s x p o) =
      ∑ a∈ shades (facets U) n, beam U a s x p o * kernel (spectator U r) (beside (sole o) y)
        (beside (sole (title U a)) w) := by
  let V := spectator U r
  let hv := spectate U r
  unfold trunc; rw [map_sum]; refine Finset.sum_congr rfl fun a ha=> ?_
  rw [map_smul,Catalogue.present _ _ a ((shadows ..).mp ha), Cov.insert,
    lowerOne V (Ward.expose ∘ w) _ _ (spectate_ready U r) hv.laws.toSymmetric hy _ (spectate_respects U r)]
  change beam U a s x p o * _ = _
  exact congr_arg _ (insert_apply S hv.laws.toSymmetric (spectate_respects U r) o y w _ _ hy)

lemma bill_beside (p:I→ S.Tag)(q:J→ S.Tag): bill (beside p q)=bill p+bill q:= by
  unfold bill; rw [Fintype.sum_sum_type]; rfl
end

variable [φ.NeBot]
variable (P:Finset V)(H:Crown P){v:V}(hp:v∈rest P) (hh:Light P t v) (hδ:0<jump E t v)
  (p:V→ S.Tag)(n:ℕ)
section
-- tests with arbitrary finite exteriors, including viewer uniform
variable {J:Type} [Fintype J] {Y:l→ J→ E4} (q:J→ S.Tag) (r:l→Viewers U)
variable (hc:0<c) (hy:∀ᶠ i in φ, ClearOf (X i ⊥) (Y i) c)
include hc hy Z L H hh hp hδ
lemma splice : RateLE φ T (fun i=>
      kernel (spectator U (r i)) (beside (picked (brim E P) (X i)) (Y i)) (beside (picked (brim E P) p) q) -
        ∑ a∈ shades (facets U) n, shoot E U P v a (s i) (X i) p * kernel (spectator U (r i))
          (beside (picked (brim E (trim P v)) (X i)) (Y i)) (beside (picked (brim E (trim P v)) (paint U v p a)) q))
    ((bill (picked (glen E P v) p):ℝ)*t v-(n+1:ℝ)*jump E t v+(bill (picked (shore E P v) p):ℝ)+bill q) := by
  letI p' : shore E P v ⊕ J→ S.Tag := beside (picked (shore E P v) p) q
  let y (i:l):= beside (picked (shore E P v) (X i)) (Y i)
  have hv := H.inner (Finset.mem_erase.mp hp).2
  have hb := L.bounds _ (internal_le hv (par_le E v))
  have ha : Kept φ T 1 y:= L.words_shore E P H hc hy
  have ht := L.words_intervals E P H hp hc hy
  have he := single_rate U Z L.flow (picked (glen E P v) p) p' r (L.upper_separation E P H hh)
    (L.enveloped E (Subtype.val: ↑(glen E P v)→ V) hv (fun j => (Finset.mem_filter.mp j.2).2))
    ht (sub_pos.mp hδ) hb.1 ha hb.2 n
  dsimp only [p'] at he
  rw [mul_one,bill_beside,Nat.cast_add,← add_assoc] at he
  refine he.congr ?_
  have h := L.fade E v hv
  filter_upwards [(L.prices v hv).pos,(h.mono_right nhdsWithin_le_nhds).eventually
    (gt_mem_nhds (Signal.period_pos (supplies S) n)),
    L.words_exist E P H hc hy,L.words_exist E (trim P v) (remains _ H (Finset.mem_erase.mp hp).1) hc hy,
    ((Kept.sole _ _ _ 1).chorus ha (ht.mono hb.2)).inject] with i hi hg he hw hR
  let ht := (spectate U (r i)).laws.toSymmetric
  rw [from_brim E P v ht (X i) p _ _ he.1,← trunc_ray U n hi hg.le,
    ink U n (r i) (s i v) _ _ (X i v) (beside (picked (shore E P v) (X i)) (Y i)) _ hR]
  apply congr_arg
  apply Finset.sum_congr rfl; intro a _
  rw [passing E P v ht _ p (title U a) _ _ H hp hw.1]; rfl
end
include hp L Z H hh hδ
lemma slice_ray (k:ℕ) : RateLE φ T (fun i=>
      ray U k (picked (brim E P) (X i)) (picked (brim E P) p) (X i ⊥) -
        ∑ a∈ shades (facets U) n, shoot E U P v a (s i) (X i) p • ray U k
          (picked (brim E (trim P v)) (X i)) (picked (brim E (trim P v)) (paint U v p a)) (X i ⊥))
    ((bill (picked (glen E P v) p):ℝ)*t v-(n+1:ℝ)*jump E t v+(bill (picked (shore E P v) p):ℝ)+
      palm (supplies S) k) := by
  let a (b:↑(shades (facets U) n)) (i:l) := shoot E U P v b.val (s i) (X i) p
  let O (i:l) := X i ⊥
  let Y (_:↑(shades (facets U) n)) (i:l) := picked (brim E (Arboreal.trim P v)) (X i)
  let u (b:↑(shades (facets U) n)) (_:l):= picked (brim E (Arboreal.trim P v)) (paint U v p b.val)
  let c:= (bill (picked (glen E P v) p):ℝ)*t v-(n+1:ℝ)*jump E t v+(bill (picked (shore E P v) p):ℝ)+palm (supplies S) k
  have hs := finiteEye_exchange (κ:=c) U k O (fun i=> picked (brim E P) (X i)) Y
    (fun _=>picked (brim E P) p) u a L.flow (L.inch E (Subtype.val: ↑(brim E P)→ V) L.canopy (fun _=>bot_le))
    ((L.rough_separation E P H _ (Finset.Subset.refl _)).inject)
    (fun _ => L.inch E (Subtype.val: ↑(brim E (Arboreal.trim P v))→ V) L.canopy (fun _=>bot_le))
    (fun _ => (L.rough_separation E _ (remains P H (Finset.mem_erase.mp hp).1) _ (Finset.Subset.refl _)).inject)
    (fun K _ w y δ hw h hY => by
      have he := (splice (c:=δ) E U L Z P H hp hh hδ p n w (fun _=>none) h hY).mono (show _ ≤ c from
        add_le_add le_rfl (Nat.cast_le.mpr hw))
      refine he.congr (Eventually.of_forall fun i => ?_)
      simp only [unselected_view]
      refine congr_arg (_- ·) (Eq.symm ?_)
      exact Finset.sum_coe_sort (shades (facets U) n) fun a=> shoot E U P v a (s i) (X i) p * kernel S
          (beside (picked (brim E (trim P v)) (X i)) (y i)) (beside (picked (brim E (trim P v)) (paint U v p a)) w))
  refine hs.congr (Eventually.of_forall fun i => ?_)
  refine congr_arg (_- ·) ?_
  exact Finset.sum_coe_sort (shades (facets U) n) fun a=> shoot E U P v a (s i) (X i) p • ray U k
          (picked (brim E (trim P v)) (X i)) (picked (brim E (trim P v)) (paint U v p a)) (X i ⊥)

lemma spliced_coeff (a:Tones U) : RateLE φ T (fun i=>
      frontierCoefficient E U P a (s i) (X i) p - ∑ b∈ shades (facets U) n,
        shoot E U P v b (s i) (X i) p * frontierCoefficient E U (trim P v) a (s i) (X i) (paint U v p b))
    ((bill (picked (glen E P v) p):ℝ)*t v-(n+1:ℝ)*jump E t v+(bill (picked (shore E P v) p):ℝ)
      + palm (supplies S) a.fst) := by
  let F := (legends U).readIn a.fst a
  refine ((slice_ray E U L Z P H hp hh hδ p n a.fst).linear L.flow
    (LinearMap.toContinuousLinearMap (F.restrictScalars ℝ))).congr ?_
  filter_upwards [later (I:=↑(brim E P)) U a L.reach,later (I:=↑(brim E (trim P v))) U a L.reach] with i hi hv
  change F _=_
  unfold frontierCoefficient
  rw [map_sub,map_sum,hi]; simp_rw [map_smul,hv]; rfl

omit Z L H hp hh in
-- horizons after refinement allowed to depend on limiting geometry, not phases or additional tests at this cap;
-- even the dependence on κ harmless
lemma investment (A κ : ℝ) : ∀ᶠ n:ℕ in atTop, A - (n+1:ℝ)*jump E t v ≤ κ := by
  obtain ⟨m,hm⟩ := exists_nat_gt ((A-κ)/jump E t v)
  filter_upwards [eventually_ge_atTop m] with n hn
  have hx : (m:ℝ) ≤ (n:ℝ) := Nat.cast_le.mpr hn
  have hg : A-κ < (n+1:ℝ)*jump E t v := (div_lt_iff₀ hδ).mp (hm.trans_le (hx.trans (by linarith)))
  linarith only [hg]
end YM.OPE.Arboreal
