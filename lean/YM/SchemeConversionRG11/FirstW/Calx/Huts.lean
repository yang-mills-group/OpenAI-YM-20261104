import YM.SchemeConversionRG11.FirstW.Lien.Singer
/-! Cost accounting on moving cover boxes (after image removal). -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function MeasureTheory Filter Set Metric Topology Lattice Pert Pert.Align Laurent
open scoped BigOperators Classical
variable {T : Itinerary} {E : Type*} [NormedAddCommGroup E] {R r : ℝ}
abbrev Moss (T : Itinerary) (i : ℕ) (x : Cover) := Full.incVec (T.gap i) x
def Jam (T : Itinerary) (R : ℝ) (i : ℕ) (x : Cover) := ‖Moss T i x‖ ≤ R
lemma small_mark (T : Itinerary) (i : ℕ) (x : Cover) : T.gap i * ((size x:ℕ):ℝ) ≤ 4*‖Moss T i x‖ := by
 have ht:(size x:ℝ) ≤ 4*(yard x:ℝ):=by exact_mod_cast size_yard x
 unfold Moss; rw [mover_norm _ (T.positive _).le]; nlinarith [yard_toE x,T.positive i]
lemma entryM (T : Itinerary) (R : ℝ) : ∀ᶠ i in atTop,∀ x,Jam T R i x → lift (wrap (T.period i) x)=x := by
 filter_upwards [entrance T (4*R)] with i hi x hx; apply hi; change ‖Moss T i x‖≤R at hx; exact (small_mark T i x).trans (by linarith)
lemma birthM (ht:r>R) (x:Cover) : ∀ᶠ i in atTop, ∀ v:Cover,Jam T R i v → Jam T r i (v+x) := by
 filter_upwards [(inc_const T x).norm.eventually (gt_mem_nhds (show ‖(0:E4)‖<r-R by rw [norm_zero]; linarith))] with i hi v hv
 unfold Jam Moss at *; change ‖Full.incVec (T.gap i) x‖ < r-R at hi; rw [inc_add]; exact (norm_add_le ..).trans (by linarith only [hv,hi])
def pod (T : Itinerary) (R : ℝ) (i : ℕ) := (boxN (⌈R/T.gap i⌉₊)).filter (Jam T R i)
lemma in_pod (i:ℕ)(x:Cover): x∈pod T R i ↔ Jam T R i x := by
 rw [pod,Finset.mem_filter]; refine and_iff_right_of_imp (fun h => ?_); rw [mem_boxN]; unfold Jam Moss at h
 have hp: (yard x:ℝ) ≤ R/T.gap i:= by rw [le_div_iff₀ (T.positive i)]; rw [mover_norm _ (T.positive _).le] at h; nlinarith only [h,yard_toE x,T.positive i]
 exact_mod_cast hp.trans (Nat.le_ceil _)
def Lives (T : Itinerary) (R : ℝ) (f : ℕ → Cover→E) := ∀ᶠ i in atTop,∀ v:Cover,f i v ≠ 0 → Jam T R i v
lemma Lives.mono {f:ℕ → Cover→E} (h : Lives T R f) (he:R≤r) : Lives T r f := Eventually.mono h (fun _ hi _ hv=> le_trans (hi _ hv) he)
lemma Lives.plus {f g:ℕ → Cover→E} (h:Lives T R f) (p:Lives T R g): Lives T R (fun i x=>f i x+g i x):= (h.and p).mono fun i hi x hx=> by
    by_cases h:f i x=0; · exact hi.2 x (by simpa only [h,zero_add] using hx)
    exact hi.1 x h
lemma Lives.back {f : ℕ → Cover→E}(h:Lives T R f)(p:R<r)(s:Cover): Lives T r (fun i x=>f i (x+s)) := (h.and (birthM p (-s))).mono fun i hi x hx=> by simpa only [add_neg_cancel_right] using hi.2 (x+s) (hi.1 _ hx)
abbrev expenditure (T : Itinerary) (f : ℕ → Cover→E) (i : ℕ) := ∑ x:Site (T.period i),f i (Lattice.lift x)
lemma stackV (T : Itinerary) (R : ℝ) (f:ℕ → Cover→E) (h:Lives T R f) : (fun i=>expenditure T f i)=ᶠ[atTop] fun i=> ∑ x∈pod T R i,f i x := by
 filter_upwards [h,entryM T R] with i hi he
 let s:=pod T R i; let L:=lift (n:=T.period i); let q : Finset (Site (T.period i)):= Finset.univ.filter (fun x=> L x∈s)
 have hz : (∑ x:Site (T.period i), f i (lift x))=∑ x∈q,f i (L x):= by
   symm; refine Finset.sum_subset (Finset.subset_univ _) fun x _ hx=>?_ ; by_contra h; exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(in_pod ..).mpr (hi _ h)⟩)
 unfold expenditure; rw [hz]
 refine Finset.sum_bij (fun x _=> L x) (fun x hx=> (Finset.mem_filter.mp hx).2) (fun x _ y _ h=>?_ ) (fun y hy=>?_ ) (fun _ _=>rfl)
 · rw [←wrap_lift x,←wrap_lift y]; exact congrArg _ h
 let x:=wrap (T.period i) y; have hp : L x=y:= he y ((in_pod ..).mp hy)
 exact ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,show L x∈s from hp.symm ▸ hy⟩,hp⟩
-- moving limit including passing subsequences, for Bound.
def Harbor (T : Itinerary) (p : ℕ → Cover) (x : E4) := Tendsto (fun i=>Moss T i (p i)) atTop (𝓝 x)
lemma nextDoor (T : Itinerary) (σ:ℕ→ℕ)(hs:Tendsto σ atTop atTop) (q:∀ i,Site ((Rig.path T σ hs).period i)) (x:E4) (hr:sails (Rig.path T σ hs) q x): Harbor (Rig.path T σ hs) (fun i=>lift (q i)) x:=hr
def Loom (T : Itinerary) (K : Set E4) (f:ℕ → Cover→E)(g:E4→E):= ∀ σ:ℕ→ℕ,∀ hs : Tendsto σ atTop atTop,∀ x∈K,∀ p:ℕ → Cover,Harbor (Rig.path T σ hs) p x → Tendsto (fun i=> f (σ i) (p i)) atTop (𝓝 (g x))
lemma Loom.rent {S A:Set E4}{f:ℕ → Cover→E}{g:E4→E} (h:Loom T S f g) (he:IsCompact A)(hs : A⊆S) : ∃ C>0,∀ᶠ i in atTop,∀ v:Cover,Moss T i v∈ A → ‖f i v‖≤C := by
 by_contra! hp
 have hq (i:ℕ): ∃ j≥i,∃ v:Cover,Moss T j v∈A ∧ (i:ℝ)+1 < ‖f j v‖:= frequently_atTop.1 (hp ((i:ℝ)+1) (by positivity)) _
 choose n hn p hx h using hq
 obtain ⟨x,u,r,s,H⟩:= he.isSeqCompact (x:=fun i=> Moss T (n i) (p i)) hx
 let m:=s.tendsto_atTop; let S':= (tendsto_atTop_mono (f:=id) hn tendsto_id).comp m
 have hh:= (‹Loom ..› (n ∘ r) S' x (hs u) (fun i=>p (r i)) H).norm
 obtain ⟨j,hj,e⟩:= (hh.eventually (gt_mem_nhds (lt_add_one ‖g x‖)) |>.and ((tendsto_natCast_atTop_atTop.comp m).eventually (eventually_ge_atTop ‖g x‖))).exists
 exact not_lt.mpr (show (r j:ℝ)+1 ≥ ‖f (n (r j)) (p (r j))‖ from hj.le.trans (add_le_add e le_rfl)) (h (r j))
-- DCT importer
variable {c : ℕ→Side}
def Foot (T : Itinerary) (i : ℕ) (x : Cover) := T.gap i*stepY x
lemma limb {i:ℕ}{x:Cover} (h:Jam T R i x) : Foot T i x≤R+T.gap i := by -- i/x undeclared
 unfold Foot stepY; unfold Jam Moss at h; rw [mover_norm _ (T.positive _).le] at h; nlinarith only [h,yard_toE x,T.positive i]
variable {f:ℕ → Cover→E} {g:E4→E}
def NearCost (T : Itinerary) (f : ℕ → Cover→E) := ∃ C>0, ∀ᶠ i in atTop,∀ v:Cover, (Foot T i v)^3 * ‖f i v‖ ≤ C
def Hollow (T : Itinerary) (f : ℕ → Cover→E)(g:E4→E):= ∀ x:E4,x≠0 → ∀ p:ℕ → Cover,Harbor T p x → Tendsto (fun i=> f i (p i)) atTop (𝓝 (g x))
lemma mount [NormedSpace ℝ E] [CompleteSpace E] (h: Lives T R f)(hc : MarkGrid T c)(hp : NearCost T f)(ht: Hollow T f g) : Integrable g ∧ Tendsto (fun i=> (T.gap i)^4 • expenditure T f i) atTop (𝓝 (∫ x,g x)) := by
 obtain ⟨C,hC,H⟩:=hp
 refine sum_local (K:=g) (F:=fun i x=>f i (lift x)) hc hC.le (C:=C) (R:=R+1) ?_ ((volume.ae_ne 0).mono fun x hx p hs=> ht x hx _ hs) -- cover lift sailing inference
 filter_upwards [H,h,T.cutoff.eventually (ge_mem_nhds (by norm_num: (0:ℝ)<1))] with i hi hl e x
 exact ⟨fun hw=> (limb (hl (lift x) hw)).trans (by linarith),hi (lift x)⟩
end YM.RG11.FirstW
