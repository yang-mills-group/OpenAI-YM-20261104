import YM.OPE.Compatible.Trees.Layer
import YM.OPE.Compatible.First

/-!
# Feeding layers into the ordinary OPE
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Set Filter Cov Display
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V:Type}[PartialOrder V][OrderBot V][Fintype V](E:Origin V)
variable {l:Type}{φ:Filter l}{T:l→ℝ} {t:V→ℝ}{S:l→ V→ ℝ}{X:l→ V→ E4}
    {M η c :ℝ}(L:Layer E φ T M η t S X)
    (P:Finset V)(H:Crown P)

/-- all active internal on that subtree have the same rate -/
def Light (t:V→ℝ)(v:V) := ∀ u∈P,v ≤ u → t u=t v
omit [OrderBot V] [Fintype V] in
lemma bud_light (t:V→ℝ){v:V}(h:Maximal (· ∈ P) v): Light P t v:= fun _ hu e => congr_arg t
  (le_antisymm (h.2 hu e) e)

variable {G:Gauge}{Q:Family G} (W : Table Q.book)
include L
lemma Layer.enough : 0 ≤ envelope V M := mul_nonneg (Nat.cast_nonneg _) L.extent

section Reach
variable {I:Type}[Fintype I] (p : I→ V) {v:V} (hv:v∈heart V) (h : ∀ a, v ≤ p a)
include hv h p
lemma Layer.inch : Tendsto (fun i => away (X i ∘ p) (X i v)) φ (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _)
    (L.stays.mono (fun i hi => (pi_norm_le_iff_of_nonneg
      (mul_nonneg (L.enough E) ((hi.pos v hv).le))).mpr ?_))
    (by simpa using ((L.fade E v hv).mono_right nhdsWithin_le_nhds).const_mul (envelope V M))
  exact fun j => hi.reaches E L.extent hv (h j)
lemma Layer.enveloped : enveloped φ T (t v) (fun i=>X i ∘ p) (fun i=> X i v) := by
  exact ((((RateLE.const (envelope V M) L.flow).mul ((L.prices v hv).pays L.flow)).mono (zero_add _|>.le)).of_norm_le
    (L.stays.mono (fun i hi => (pi_norm_le_iff_of_nonneg
      (mul_nonneg (L.enough E) ((hi.pos v hv).le))).mpr fun j => hi.reaches E L.extent hv (h j))))
lemma Layer.coverage (W : Table Q.book) (hx : ∀ᶠ i in φ, Injective (X i ∘ p)) :
    ∀ᶠ i in φ, Covered W (S i v) (X i ∘ p) (X i v) := by
  filter_upwards [hx,L.stays,(L.fade E v hv).eventually (valid_geometry (I:=I) (S:=W) (envelope V M))]
    with i hx hi he using he _ _ hx fun j => hi.reaches E L.extent hv (h j)
end Reach
lemma verge {u v:V} (h : ¬ u ≤ v) (h' : ¬ v ≤ u) {b : ℝ} (ht:t (couple E u v)<b) :
    ∀ᶠ i in φ, Real.exp (-b*T i) < ‖X i u-X i v‖ := by
  have hp := (L.prices _ (heart_mem.mpr ⟨u,separate_left E h⟩))
  have hw := ((RateIs.const L.flow L.space).mul hp).overtakes (RateLE.exp (-b) L.flow) L.flow
    (by linarith only [ht])
  exact hw.mp (L.stays.mono fun _ hi he => lt_of_lt_of_le he (hi.fork E h h'))

lemma centered_further {I J:Type} [Fintype I] [Fintype J] {Y:l→ J→ E4}
    (p:I→ V)(hc:0<c) (hy:∀ᶠ i in φ,ClearOf (X i ⊥) (Y i) c) : Intervals φ T 0 (fun i=>X i ∘ p) Y := by
  have hg := Layer.inch E L p L.canopy (fun _=>bot_le)
  intro b hb; have hh := half_pos hc
  filter_upwards [hy,hg.norm.eventually (gt_mem_nhds (show ‖(0:I→ E4)‖< c/2 from by simpa using hh)),
      ((RateIs.exp (-b) L.flow).tends (neg_lt_zero.mpr hb) L.flow).eventually (gt_mem_nhds hh)]
    with i hy he hv j k
  refine lt_of_lt_of_le (show Real.exp (-b*T i)<c/2 from hv) ?_; change c/2 ≤ ‖X i (p j)-Y i k‖
  have hx : ‖X i (p j)-X i ⊥‖ < c/2 := lt_of_le_of_lt (norm_le_pi_norm (away (X i ∘ p) (X i ⊥)) j) he
  linarith only [hx,norm_sub_rev (X i ⊥) (X i (p j)),c_dist_point (X i ⊥) (X i (p j)) (Y i k),hy.openSpace k]

include H
lemma Layer.brim_separation (A:Finset V) (ha:A⊆brim E P) {u:ℝ}
    (hq : ∀ i∈ A, ∀ j∈ A,i≠j → t (couple E i j) ≤ u) : Kept φ T u (fun i =>picked A (X i)) := by
  intro b hb
  exact eventually_all.mpr fun x:A => eventually_all.mpr fun y:A => eventually_all.mpr fun h:x≠y =>
    let e := mt Subtype.ext h
    verge E L (brim_apart E P H (ha x.2) (ha y.2) e) (brim_apart E P H (ha y.2) (ha x.2) (Ne.symm e))
      (lt_of_le_of_lt (hq _ x.2 _ y.2 e) hb)
lemma Layer.rough_separation (A:Finset V) (ha:A⊆brim E P) : Kept φ T 1 (fun i =>picked A (X i)) :=
  L.brim_separation E P H A ha fun i hi _ hj e => (L.bounds _
    (heart_mem.mpr ⟨i,separate_left E (brim_apart E P H (ha hi) (ha hj) e)⟩)).2
lemma Layer.upper_separation {v:V} (h:Light P t v) : Kept φ T (t v)
    (fun i => picked (glen E P v) (X i)) := by
  refine L.brim_separation E P H (glen E P v) (Finset.filter_subset ..) ?_
  intro i hi j hj e; obtain ⟨hi,ht⟩ := Finset.mem_filter.mp hi; obtain ⟨hj,hq⟩ := Finset.mem_filter.mp hj
  exact (h _ (H.roots (touch_par E (separate_left E (brim_apart E P H hi hj e))) (((on_brim ..).mp hi).2.2))
    (ancestors_couple E ht hq)).le
omit L H in
lemma glen_bot : glen E P ⊥=brim E P := by simp [glen]
lemma Layer.at_base (h:Light P t ⊥) : Kept φ T (t ⊥) (fun i=> picked (brim E P) (X i)) := by
  have he := L.upper_separation E P H h
  rwa [glen_bot] at he
lemma Layer.live {v:V} (hv:v∈P) : ∀ᶠ i in φ, Covered W (S i v) (picked (glen E P v) (X i)) (X i v) :=
  L.coverage E (Subtype.val: ↑(glen E P v) → V) (H.inner hv)
    (fun i => (Finset.mem_filter.mp i.2).2) W (L.rough_separation E P H _ (Finset.filter_subset ..)).inject
lemma Layer.live_bot : ∀ᶠ i in φ,Covered W (S i ⊥) (picked (brim E P) (X i)) (X i ⊥) := by
  have h := Layer.live E L P H W H.base
  rwa [glen_bot] at h

variable {v:V} (hv:v∈rest P)
include hv
lemma Layer.facing [φ.NeBot] : Intervals φ T (t (par E v)) (fun i=>sole (X i v))
    (fun i=> picked (shore E P v) (X i)) := by
  have hg := H.inner (Finset.mem_erase.mp hv).2
  intro b hb
  refine eventually_all.mpr fun _ : Unit => eventually_all.mpr fun y : shore E P v => ?_
  have hu := Finset.mem_filter.mp y.2
  have he : ¬ y.val ≤ v := fun h => ((on_brim ..).mp hu.1).1 (H.roots h (Finset.mem_erase.mp hv).2)
  exact verge E L hu.2 he
    (lt_of_le_of_lt (L.order E (internal_le hg (par_le ..)) (touch_par E (separate_left E hu.2))) hb)
variable {J:Type} [Fintype J] {Y:l→ J→ E4} (hc:0<c) (hy : ∀ᶠ i in φ, ClearOf (X i ⊥) (Y i) c)
include hy hc
omit hv in
lemma Layer.words_shore : Kept φ T 1 (fun i => beside (picked (shore E P v) (X i)) (Y i)) :=
  (L.rough_separation E P H (shore E P v) (Finset.filter_subset ..)).chorus
    (((free_clear L.flow hc hy).1).mono zero_le_one)
    ((centered_further E L (Subtype.val: ↑(shore E P v)→ V) hc hy).mono zero_le_one)
include hv
lemma Layer.words_intervals [φ.NeBot] : Intervals φ T (t (par E v)) (fun i=>sole (X i v))
    (fun i=>beside (picked (shore E P v) (X i)) (Y i)) := by
  intro b hb
  have hz := centered_further E L (sole v) hc hy
  have hp := L.facing E P H hv
  filter_upwards [hp b hb,hz b (lt_of_le_of_lt (L.bounds _
    (internal_le (H.inner (Finset.mem_erase.mp hv).2) (par_le ..))).1 hb)] with i hi he t w
  rcases w with j|j; exacts [hi t j,he t j]
omit hv in
lemma Layer.words_exist : ∀ᶠ i in φ, Injective (beside (picked (brim E P) (X i)) (Y i)) ∧
    Injective (beside (sole (X i ⊥)) (Y i)) := by
  obtain ⟨he,hp⟩ := free_clear L.flow hc hy
  exact ((L.rough_separation E P H (brim E P) (Finset.Subset.refl _)).chorus
    (he.mono zero_le_one) ((centered_further E L (Subtype.val: ↑(brim E P)→ V) hc hy).mono zero_le_one)).inject.and
    (((Kept.sole φ T _ 0).chorus he hp).inject)
end YM.OPE.Arboreal
