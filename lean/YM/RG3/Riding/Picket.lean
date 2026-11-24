import YM.RG3.Riding.Semis
/-! # Buy new box article directly from canopy/towed

With all quiet. Caption radiator & roots separately on R.Book before
script alignment. Use .supplier. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Riding
open RG Wilson Lattice Function Marker Overlay RG3.Script RG3.Held
 RG3.Forms RG3.Ink Extra.Trajectories Extra.Iteration Extra.Multi Ac Push.Local Press
 Push.AbsoluteSums Push.Corrected MergeProof Accent Finset
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {n : Side}{V:Type*}[DecidableEq V]{R:Census V}{G:Gauge}
  (P:Rep G n){ζ:V→Site n}{w:V→ℝ}(hw:∀ v,0<w v)
variable (f : Box n→ Config G n→Poly R)

variable (ζ) in
def pick : Article (mortar n) P.p G R ζ where
  address i:= mason G i
  flow i:=f i.val

-- meas of poly map from component for any config
lemma joint {Ω : Type*}[MeasurableSpace Ω]{g:Ω→Poly R}(hg:∀ i,Measurable fun x=>(g x).part i):Measurable g:= by
  let p i x:= Poly.send i ((g x).part i)
  have hh:g= fun x=>∑ i:R.Mode,p i x := by
    funext U; ext i; rw [Poly.part_sum]; classical simp [p, Poly.part_send]
  rw [hh]; exact Finset.measurable_sum univ (fun i _=> (Bands.sends _).measurable.comp (hg _))

variable (h : ∀ i,Flow ζ i (f i) P.p.threshold)(he: ∀ i U,(f i U).part R.quiet=bass P i U){e t:ℝ}
include h he
lemma conditioned (hp:P.activities.Valid P.p e t): (pick P ζ f).Sound:=by
  constructor
  · intro i; have ht:=h i.val
    refine ⟨ht.turns,joint ht.me,ht.home,fun U j hj s hs=>ht.toBorne.place j U hj (mem_image_of_mem _ hs)⟩
  · intro i U hc
    exact ⟨((h i.val).permits U hc).1,trivial⟩
  · intro i U; change ((f i.val U).part _).im=0; rw [he]; exact chorus P _ _ hp
  · intro i; exact MeasurableSet.univ
  · intro i k U; exact Iff.rfl
  intro i _ _ _ _; rfl

-- virtual broth filled by equality bass at all configurations. Canopy.S at G,p to active Deck with physical Poly result.
omit h he in
lemma pick_host : (pick P ζ f).Hosting (virtual R G P ζ) pin:=by
  refine ⟨rfl,fun i=>?_,fun i=>?_,fun i U he=>?_⟩
  all_goals unfold virtual; rw [Article.currency]; first|rfl|trivial
 omit h in
lemma cooking (hp:P.activities.Valid P.p e t)(i:ℕ)(U:Config G n) : (pick P ζ f).broth pin i U=((virtual R G P ζ).activities.K i U:ℂ):=by
  let W:=material R G P ζ
  change _=((W.ledger P).activities.K i U:ℂ)
  rw [← W.ledger_q P (feed_sound R G ζ P hp)]
  refine tsum_congr fun j=>?_ ; change (f j.val.val U).part R.quiet=(Poly.send _ _).part _
  rw [he,Poly.part_send,if_pos rfl]

omit he
lemma clustering (U:Config G n): (pick P ζ f).cluster U=field (fun j=> f j U) (flags P.p.threshold U):=by
  classical
  let φ : mortar n ↪ Box n:= ⟨Subtype.val,Subtype.val_injective⟩
  let ν(s:Finset (mortar n)):=s.map φ
  unfold Article.cluster field; rw [tsum_fintype]
  have ht : Injective ν:=by unfold ν; exact Finset.map_injective _
  let F(i:Finset (mortar n)):= (pick P ζ f).pack U i
  let g:= grid (fun j=> f j U) (flags P.p.threshold U)
  have hp i:F i=g (ν i):=by
    unfold F Article.pack g grid
    have hq:(pick P ζ f).room U i ↔ Accent.Pattern (flags P.p.threshold U) (ν i):=by
      unfold Article.room Accent.Pattern; apply and_congr
      · unfold ν Set.PairwiseDisjoint Set.Pairwise; simp only [Finset.mem_coe, Finset.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, ne_eq, Function.Embedding.apply_eq_iff_eq]
        rfl -- maybe weird
      unfold ν; rw [map_eq_image,image_biUnion]; rfl
    rw [if_congr hq rfl rfl,Finset.prod_map]; rfl
  have hl : Finset.univ.sum F=(univ.image ν).sum g:= by rw [sum_image ht.injOn]; exact sum_congr rfl (fun i _=>hp i)
  rw [hl]
  symm; refine sum_subset (subset_univ _) (fun i _ hi=>?_) |>.symm -- check
  have he : ∃ j∈i,¬ Sure j:=by
    by_contra! hm; let c:=i.subtype Sure
    refine hi (mem_image.mpr ⟨c,mem_univ _,?_⟩)
    ext j; unfold ν c; simp only [mem_map]
    constructor
    · rintro ⟨k,hk,rfl⟩; exact (mem_subtype.mp hk)
    intro hj
    refine ⟨(⟨j,hm j hj⟩:mortar n),mem_subtype.mpr hj,rfl⟩
  obtain ⟨j,hj,hI⟩:=he
  unfold grid; split; exact prod_eq_zero hj (not_ne_iff.mp (fun he=>hI ((h j).permits U he).2));rfl

end YM.RG3.Riding
