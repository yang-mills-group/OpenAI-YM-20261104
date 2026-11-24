import YM.OPE.Compatible.Exchange
import YM.OPE.Exchange.Coherence

/-!
# Using the available estimates

`SingleSubpower` statements in `YM.OPE.Single` have finished all cutoff
and replication estimates, in a coordinated construction `Services` on
one actual Final. We also use *stages* in those theorems: `RateLE` for the
complex compatible detectors, with the exterior at a different (positive
exponential gap) rate or rate zero. This doesn't refit separate detectors
to subsequent queries, or ask for cutoff-uniform constants through trees.
Use only separated point configurations in the same continuum hierarchy.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cov.Display
open Function Set Filter Table MeasureTheory
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {L:Register G} {A : Table L} {C:Family G} {f:Extraction.Order} {S:Table C.book}
  (U : Spec.Final C f S)
variable {I J B l:Type} [Fintype I] [Fintype J] {φ : Filter l} {T : l → ℝ} {κ t b s : ℝ}
  {X:l → I → E4} {Y:l → J → E4} {O:l → E4}

/-- Total input weights in their announced filtration levels. -/
def bill (p : I → A.Tag) : ℕ := ∑ i, (p i).1
lemma bill_expose (p : I → A.Tag) : bill p = sigma (Ward.expose ∘ p) := rfl
lemma bill_one (p : A.Tag) : bill (sole p) = p.1 := by simp [bill,sole]

variable (H : Services C f S) {P : Prescription U.sector.derivatives} (hp : P.Coherent)
  [φ.NeBot] (hT : Tendsto T φ atTop)

include H hp hT
lemma shadow_fit (p:I→ S.Tag) (w:J→ S.Tag) (r:l→Viewers U) (hx: Kept φ T s X)
    (hh:enveloped φ T s X O) (ht: Intervals φ T b (fun i=> sole (O i)) Y)
    (hs:b < s) (hb:0 ≤ b) (hy:Kept φ T t Y) (hg:b ≤ t) (n:ℕ) : RateLE φ T (fun i =>
      kernel (spectator U (r i)) (beside (X i) (Y i)) (beside p w) -
      Cov.insert S (spectator U (r i)) (O i) (Y i) w n (shadow P n (X i) (Ward.expose ∘ p) (O i)))
       ((bill p:ℝ)*s-(n+1:ℝ)*(s-b)+(bill w:ℝ)*t) := by
  let p' := Ward.expose ∘ p
  let w' := Ward.expose ∘ w
  have hw := arrangement_cost U P n p' w' hT H hp hh hx (lt_of_le_of_lt hb hs) hy ht hb hg hs
  have hy' := ((Kept.sole φ T O t).chorus hy (ht.mono hg)).inject
  have hx' := ((hx.mono (le_max_left s t)).chorus (hy.mono (le_max_right s t))
    ((Rec_spacing hT ht hh hs).mono (le_trans hg (le_max_right s t)))).inject
  apply RateLE.transfer hw
  filter_upwards [hx',hy'] with i hi hi'
  rw [kernel_expose,beside_commutes,Cov.insert,
    compatible_shadows P _ (spectate U (r i)) (spectate_respects U (r i)) (spectate_ready ..) w' hi']
  -- q arguments
  have hh := glance_bound U (r i) (groundError U P n (X i) p' (O i) (Y i) w')
  rw [glance_terms _ _ _ _ _ _ _ _ (r i) hi hi'] at hh; exact hh

omit hp in
lemma count_words (p : I → S.Tag) (w:J→ S.Tag) (r:l→Viewers U) (hx: Kept φ T s X)
    (hy:Kept φ T t Y) (ht: Intervals φ T s X Y) (hb:0 ≤ s) (hh:s ≤ t) :
    RateLE φ T (fun i => kernel (spectator U (r i)) (beside (X i) (Y i)) (beside p w))
      ((bill p:ℝ)*s+(bill w:ℝ)*t) := by
  simp_rw [kernel_expose,beside_commutes]
  exact viewer_cost U H.schedule (Ward.expose ∘ p) (Ward.expose ∘ w) hT r hx hy ht hb hh

-- Insertion price for growing labels in their true stage. All estimates
-- in all character hierarchies.
omit hp in
lemma count_insert (n:ℕ) (v:l→ S.Field n) (w:J→ S.Tag) (r:l→Viewers U)
    (ht:Intervals φ T b (fun i=> sole (O i)) Y) (hb:0 ≤ b) (hy:Kept φ T t Y) (hg:b ≤ t)
    (hv:RateLE φ T v κ) : RateLE φ T
      (fun i=> Cov.insert S (spectator U (r i)) (O i) (Y i) w n (v i))
      (κ+(n:ℝ)*b+(bill w:ℝ)*t) := by
  let F := Module.finBasis ℂ (S.Field n)
  let q (i) : S.Field n →ₗ[ℂ] ℂ := Cov.insert S (spectator U (r i)) (O i) (Y i) w n
  have he j : RateLE φ T (fun i => q i (F j)) ((n:ℝ)*b+(bill w:ℝ)*t) := by
    have h := count_words U H hT (sole (⟨n,F j⟩:S.Tag)) w r (Kept.sole φ T O b) hy ht hb hg
    rw [bill_one] at h
    apply RateLE.congr h
    filter_upwards [((Kept.sole φ T O t).chorus hy (ht.mono hg)).inject] with i hi using (insert_apply S
      (spectate ..).laws.toSymmetric (spectate_respects U (r i)) _ (Y i) w n (F j) hi).symm
  have hh : (fun i => Cov.insert S (spectator U (r i)) (O i) (Y i) w n (v i)) = fun i =>
      ∑ j, F.coord j (v i) * q i (F j) := by
    ext1 i; change q i _ = _
    conv_lhs => rw [← F.sum_repr (v i), map_sum]
    simp_rw [map_smul]; rfl
  rw [hh,add_assoc]
  apply RateLE.sum hT; intro j _
  exact (hv.linear hT (LinearMap.toContinuousLinearMap ((F.coord j).restrictScalars ℝ))).mul (he j)

lemma ray_v_shadow (p : I → S.Tag) (hx : Kept φ T s X) (he : enveloped φ T s X O)
    (hs : 0 < s) (n : ℕ) : RateLE φ T (fun i => ray U n (X i) p (O i) -
      shadow P n (X i) (Ward.expose ∘ p) (O i)) (((bill p:ℝ)-(n+1:ℝ))*s) := by
  let v (i:l) := shadow P n (X i) (Ward.expose ∘ p) (O i)
  let Y (_:Unit) (i:l) := sole (O i)
  let q (_:Unit) (i:l) := sole (⟨n,v i⟩:S.Tag)
  have h (i:l) : ray U n (Y () i) (q () i) (O i) = v i := by
    unfold ray
    rw [show away (Y () i) (O i) = sole 0 from funext fun j => sub_self (O i)]
    exact ascend_fix _ U.phase.transport.spots U.room.kernel U.phase.transport.motion _ _
  have hy (b:Unit): Tendsto (fun i=>away (Y b i) (O i)) φ (𝓝 0) := by
    rw [show (fun i=>away (Y b i) (O i)) = fun _ => 0 from funext fun i=> funext fun t=>sub_self _]
    exact tendsto_const_nhds
  apply RateLE.congr
    (F:=fun i:l => ray U n (X i) p (O i) - ∑ j:Unit,(1:ℂ) • ray U n (Y j i) (q j i) (O i))
  · refine exchange U O X Y (fun _=>p) q (fun _ _=>1) hT (RateLE.tends he (neg_lt_zero.mpr hs) hT)
      hx.inject hy (fun _ => Eventually.of_forall fun _ => injective_of_subsingleton _) ?_ n
    intro K _ w y δ hδ hh
    obtain ⟨hw,ht⟩ := free_clear hT hδ hh
    have hm := shadow_fit U H hp hT p w (fun _=>none) hx he ht hs le_rfl hw le_rfl n
    rw [mul_zero,add_zero,sub_zero,← sub_mul] at hm
    apply RateLE.congr hm
    filter_upwards [((Kept.sole φ T O 0).chorus hw ht).inject] with i hi
    rw [Fintype.sum_unique, one_mul]; exact congr_arg _ (insert_apply S U.room.kernel.laws.toSymmetric (show S.respects S from fun _ => le_rfl) _ _ _ _ _ hi)
  filter_upwards with i; rw [Fintype.sum_unique]
  rw [one_smul,show (default:Unit)=() from rfl,h]
end YM.OPE.Cov.Display
