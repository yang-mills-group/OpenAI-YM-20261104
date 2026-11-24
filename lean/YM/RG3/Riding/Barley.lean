import YM.RG3.Riding.Index
/-!
# Chart-independent realization of compressed K profiles

Build virtual Rep (needs Motion also at zeros; all gauge cutoffs retained),
using only C.Hasse P lawful and aggregated quiet re/K profile. Hosts also
future K mergers without additional slots. Prove no Jacobian or beta change.
Cases of profile where uneligible automatically vanish but keep them in the
pointwise sum `anthem`. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Riding
open RG Wilson Lattice Function Marker Overlay RG3.Script RG3.Held
 RG3.Forms RG3.Ink Extra.Trajectories Extra.Iteration Extra.Multi Ac Push.Local Press
 Push.AbsoluteSums Push.Corrected MergeProof Accent Finset
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {n : Side}{V:Type*}[DecidableEq V]{R:Census V}{G:Gauge}
  {P : Rep G n}{p:BudgetPoint}{ζ:V→Site n}{w:V→ℝ}
def mortar (n:Side):= {i: Box n // Sure i}
instance : Fintype (mortar n):= by unfold mortar; apply Fintype.ofFinite
instance : DecidableEq (mortar n):= Classical.decEq _
-- mortar projection abbrev?
variable (G) (i:mortar n)
def mason : ForcedAddress G n:=⟨i.val.1,i.val.2,i.property.1,i.property.2,fun _=>True⟩
variable (P R ζ)
def material : Article (mortar n) P.p G R ζ where
  address i:= mason G i
  flow i U:=Poly.send R.quiet (bass P i.val U)

-- physical sound on collapsed profile, includes true tests which no
-- longer read dormant aliases. Other tests P not discarded because bass
-- K values require old reads; outer past masks still exactly serialized in entry.
lemma feed_sound (P:Rep G n){e t:ℝ}(h:P.activities.Valid P.p e t): (material R G P ζ).Sound:=by
  constructor
  · intro i; obtain ⟨hm,ha,hf,-⟩:=anthem P h i.val
    refine ⟨fun k U=>congrArg (Poly.send _) (ha k U), (Bands.sends _).measurable.comp hm,fun U V hu hv=> congrArg (Poly.send _) (hf U V hu hv),fun U j hj=>?_⟩
    change (Poly.send R.quiet _).part j ≠0 at hj; rw [Poly.part_send] at hj; split at hj
    next hv=> rw [hv]; intro v hh; exact (Finset.notMem_empty v hh).elim
    next => exact (hj rfl).elim
  · intro i U hv; obtain ⟨-, -, -, H⟩:= anthem P h i.val
    have ht:= H U (fun hr=> hv ((congrArg (Poly.send _) hr).trans (Poly.send_zero _)))
    exact ⟨ht.1,trivial⟩
  · intro i U; change ((Poly.send R.quiet _).part R.quiet).im=0; rw [Poly.part_send,if_pos rfl]; exact chorus P _ _ h
  · intro i; exact MeasurableSet.univ
  · intro i U v; exact Iff.rfl
  intro i _ _ _ _; rfl

lemma safe_stamps (s:Signed)(a:Site n) (v:mortar n):Sure (stampK s a v.val):=by
  change Sure (whirl s a v.val.1,whirl s a v.val.2)
  rw [wheel,wheel]; exact ⟨v.property.1.image _,image_subset_image v.property.2⟩

def bricks (s:Signed) (a:Site n):Equiv.Perm (mortar n):=
  let E:=s.actEquiv.toEquiv.trans (Equiv.addRight a)
  let w x:= (x:Support n).map E.symm.toEmbedding
  have he(v:mortar n): Sure (w v.val.1, w v.val.2):= by
    constructor
    · exact v.property.1.map
    exact Finset.map_subset_map.mpr v.property.2
  { toFun v:= ⟨stampK s a v.val,safe_stamps s a v⟩
    invFun v:= ⟨_,he v⟩
    left_inv v:= Subtype.ext (show (stampK s a).symm (stampK s a v.val)=v.val from Equiv.symm_apply_apply ..)
    right_inv v:=Subtype.ext (show (stampK s a) ((stampK s a).symm v.val)=v.val from Equiv.apply_symm_apply ..) }

lemma spun (P:Rep G n)(s:Signed)(a:Site n)(E:P.activities.Moves s a) : Nonempty ((material R G P ζ).Spin s a):= by
  refine ⟨bricks s a,fun j=> ?_,fun j=>?_,fun _ _=>Iff.rfl,fun j U=>?_⟩
  · exact wheel s a _
  · exact wheel s a _
  change (Poly.send R.quiet (bass P _ U)).part _=(Poly.send R.quiet _).part _
  rw [Poly.part_send,Poly.part_send]
  change (if R.quiet=R.quiet then bass P (stampK s a j.val) U else _)=(if R.quiet=R.quiet then _ else _)
  simp only [ite_true,melody P E]

-- use any quiet envelope at its strong support exponent
lemma priced {a:mortar n→ℝ}(hp:∀i,0≤a i)(ho:∀i:mortar n,∀ U,‖bass P i.val U‖ ≤ a i){δ:ℝ}
    (hh:Hit (fun i:mortar n=> i.val.1) P.p.B a P.p.supportExponent δ):
    (material R G P ζ).Budget w δ:=by
  let f (i:mortar n) := Poly.send R.quiet (a i:ℂ)
  refine ⟨f,?_,?_⟩
  · rintro i U j; change ‖(Poly.send _ _).part _‖ ≤ ((Poly.send _ _).part _).re∧ ((Poly.send _ _).part _).im=0; simp only [Poly.part_send]; split; exact ⟨ho i _,rfl⟩; simp
  simp_rw [f,Poly.solo,Poly.quiet_toll,one_mul,Complex.norm_real,Real.norm_of_nonneg (hp _)]
  exact hh
-- virtual host includes every shape
-- marker type per use chosen by caller; `virtual` reduces to definition independent of ζ and R. Use Unit to align better (no Choice)? transparency simp-RULE. -/
def virtual := (material R G P ζ).ledger P
lemma accessible : Accessible (virtual R G P ζ) := by
  intro a
  let b:mortar n:=⟨(a.support,a.inventory),⟨a.inventory_ne,a.inventory_sup⟩⟩
  refine ⟨Extra.Trajectories.pin b,?_⟩
  unfold virtual; rw [Article.currency]; exact ⟨rfl,rfl,fun _ _=> trivial⟩
lemma insured {σ C Λ e w0 t:ℝ}(h:P.Lawful σ C Λ e w0)(hw:∀i,0<w i){a:mortar n→ℝ}(hp:∀i,0≤a i)(ho:∀i:mortar n,∀ U,‖bass P i.val U‖ ≤ a i)
    (hh:Hit (fun i:mortar n=> i.val.1) P.p.B a P.p.supportExponent t): (virtual R G P ζ).Lawful σ C Λ e t :=
    (material R G P ζ).lawful P rfl (feed_sound R G ζ P h.labels) hw (priced R G P ζ hp ho hh) le_rfl h.paths h.labels.regular h.labels.boundE h.labels.moves (fun s b=>spun R G ζ P s b (Classical.choice (h.labels.moves ..))) -- check arguments
end YM.RG3.Riding
