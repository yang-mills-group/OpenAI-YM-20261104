import YM.MergeProof.Copse
import YM.RG3.Script.Coffers
/-!
# Join owner constructions through AGGREGATED box inventory

MergeProof/Accent Canopy, using PhysicalNext.Repeat.Legato movements
supplied on hE.Floral, exposes plate profiles in full marker algebra,
strong-hit at p.exp+1 y=straw in pre-mergers. Not an address equality
on P.activities.K: here exact relation without asserting their norm
immediately. Field read supported by Pattern, physical exhibit with
original P rather than changing denominator. This and future Riding
allows retaining actual vacuum & replacing any force partners while moving
through an aggregate-only reserve, then sell back onto exact H.Lens without
asking that P.raw overwritten addresses have that reserve. Useful even if
P/KBound alone doesn't qualify. No change to masks/jets, p keeps p.order.
Need price gate on y prior to publication (not inferred; see Riding.Contract).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Riding
open RG Wilson Lattice Function Marker Overlay RG3.Script RG3.Held
 RG3.Forms RG3.Ink Extra.Trajectories Extra.Iteration Extra.Multi Ac Push.Local Press
 Push.AbsoluteSums Push.Corrected MergeProof Accent Finset
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {n : Side}{V:Type*}[DecidableEq V]{R:Census V}{G:Gauge}
  {P : Rep G n}{p:BudgetPoint}{ζ:V→Site n}{w:V→ℝ}
  (T:Bands R P)

def virus (i : Box n) (U:Config G n):Poly R:= cram (barcode P.activities) (fun j=>T.each j U) i
-- summability from Radial&w ledger per label imported; find lemma
def fleet [Fintype V] := play P R (virus T)

/-- Exact evaluation using regrouped inventories. Labels need not be
injective on barcode. Includes all terms, not only marked zeros. -/
lemma exposed [Fintype V] (D:Deck R P)(U:Config G n)
    (hd:Summable (fun i=> Poly.price w (D.contents.each i U)))(hw:∀i,0<w i):
    D.density U=fleet D.contents D.log U:=by
  unfold Deck.density fleet play
  congr 2
  change D.contents.cluster U=field (cram _ _) _
  rw [rock_out P.activities P.p U _ hw hd]; rfl

def micro (i : ℕ)(U:Config G n):Poly R:=∑' j,T.tagged i j U

def red (i:Box n)(U:Config G n):Poly R:= cram (barcode P.activities) (fun j=>micro T j U) i

def bass (P:Rep G n)(i: Box n)(U:Config G n):ℂ:=profile P.activities (fun j=> Complex.ofReal ∘ P.activities.K j) i U

lemma chorus (P : Rep G n)(i:Box n)(U:Config G n) {δ c: ℝ}(h:P.activities.Valid P.p δ c):(bass P i U).im=0:=by
  have ht : Summable (fun j:ℕ=> (P.activities.K j U:ℂ)):= (mass_crest P.activities h U).hasSum.map Complex.ofRealCLM Complex.continuous_ofReal |>.summable
  unfold bass profile cram
  change Complex.imCLM (∑' j: {j // barcode P.activities j=i},(P.activities.K j.val U:ℂ)) = _
  rw [Complex.imCLM.map_tsum (show Summable (fun j:{j//barcode P.activities j=i}=> (P.activities.K j.val U:ℂ)) from ht.comp_injective Subtype.val_injective)]
  exact tsum_zero
-- never uses Rotate of P' yet: For all labels show gauge etc under regrouping. retain Ω receipts separately.
lemma anthem (P:Rep G n){δ k : ℝ}(h:P.activities.Valid P.p δ k) (I:Box n):
    Measurable (bass P I) ∧ GaugeInvariant (bass P I) ∧ UsesFinal P.p.threshold I.1 (bass P I) ∧
    ∀ U,bass P I U ≠ 0→ I.1∩flags P.p.threshold U=I.2 ∧ Sure I:=by
  unfold bass profile cram
  refine ⟨Measurable.tsum (fun j=>Complex.continuous_ofReal.measurable.comp (h.forced.meas j.val)),fun g U=>?_ ,fun U V hX he=>?_,fun U Hp=>?_⟩
  · exact tsum_congr fun j=> congrArg Complex.ofReal (h.forced.sym _ _ _)
  · apply tsum_congr; rintro ⟨j,rfl⟩; exact congrArg Complex.ofReal (h.forced.reads j U V hX he)
  by_contra hr; apply Hp; refine (tsum_congr (g:=fun _=>0) (fun j=>?_)).trans tsum_zero
  rcases j with ⟨j,HJ⟩; dsimp; norm_cast
  by_contra H; rw [← HJ] at hr
  exact hr ⟨(h.forced.permit _ _ H).1,(P.activities.forced j).inventory_ne,(P.activities.forced j).inventory_sup⟩

-- additional rotation even over forall aliases; no price consumed & no choice
-- of changing supports on virtual stocks (pure affine motion). -/
def whirl (s:Signed)(b:Site n) : Equiv.Perm (Support n):=
  (s.actEquiv.toEquiv.trans (Equiv.addRight b)).finsetCongr
lemma wheel (s:Signed)(b:Site n)(x:Support n): whirl s b x=x.image (affine s b):= by ext y; simp [whirl,Lattice.affine,map_eq_image]; rfl

def stampK (s:Signed)(b:Site n) : Equiv.Perm (Box n):= Equiv.prodCongr (whirl s b) (whirl s b)
lemma hero (P:Rep G n){s:Signed}{b:Site n}(E:P.activities.Moves s b)(i:ℕ) : barcode P.activities (E.kp i)= stampK s b (barcode P.activities i):= by
  unfold barcode stampK; apply Prod.ext
  · change _=whirl _ _ _; rw [wheel]; exact E.forced_support i
  change _=whirl _ _ _; rw [wheel];exact E.forced_inventory i

def fit (P:Rep G n){s:Signed}{b:Site n}(E:P.activities.Moves s b)(I:Box n) : {i // barcode P.activities i=I} ≃ {i // barcode P.activities i=stampK s b I} where
  toFun i:=⟨E.kp i.val,by rw [hero _ E,i.property]⟩
  invFun i:=⟨E.kp.symm i.val,by apply (stampK s b).injective; rw [← hero _ E,Equiv.apply_symm_apply,i.property]⟩
  left_inv i:= Subtype.ext (Equiv.symm_apply_apply ..)
  right_inv i:= Subtype.ext (Equiv.apply_symm_apply ..)
lemma melody (P:Rep G n){s:Signed}{b:Site n}(E:P.activities.Moves s b)(I:Box n)(U:Config G n):bass P (stampK s b I) U=bass P I (pull s b U):=by
  unfold bass profile cram
  rw [← Equiv.tsum_eq (fit P E I)]
  refine tsum_congr fun i=>congrArg Complex.ofReal (E.valuesK _ _)

-- summability on tagged rows suffices. modeling density push through exact book before re-expression, integrate via Ξ .envelope.
lemma volume (P:Rep G n){δ c : ℝ}(h:P.activities.Valid P.p δ c)(U:Config G n): Summable (fun i=> Poly.send R.quiet (P.activities.K i U:ℂ)):=by
  let F(i):=(P.activities.K i U:ℂ)
  have ht:Summable F:= (mass_crest P.activities h U).hasSum.map Complex.ofRealCLM Complex.continuous_ofReal |>.summable
  -- continuous additive map send R quiet
  let q:ℂ→+ Poly R:={ toFun:= Poly.send R.quiet, map_zero':=Poly.send_zero _, map_add' _ _:=by ext i; simp only [Poly.part_plus,Poly.part_send]; split <;> ring }
  exact (ht.hasSum.map q (Bands.sends _)).summable

lemma song (P : Rep G n){δ c : ℝ}(h:P.activities.Valid P.p δ c)(U:Config G n)(i:Box n):
    cram (barcode P.activities) (fun j=> Poly.send R.quiet (P.activities.K j U:ℂ)) i= Poly.send R.quiet (bass P i U):=by
  unfold bass profile cram; ext l; rw [Poly.share (show Summable (fun j:{j//barcode P.activities j=i}=> Poly.send R.quiet (↑(P.activities.K j.val U):ℂ)) from (volume (R:=R) P h U).comp_injective Subtype.val_injective)]
  by_cases h:l=R.quiet
  · simp [h,Poly.part_send]
  simp_rw [Poly.part_send,if_neg h,tsum_zero]

lemma reads (T:Bands R P){δ c : ℝ}(h:P.activities.Valid P.p δ c)(U:Config G n)(hs:Summable fun i=>micro T i U)(i:Box n) : virus T i U= Poly.send R.quiet (bass P i U)+ red T i U:=by
  rw [← song P h]
  unfold virus red cram
  exact ((volume P h U).comp_injective Subtype.val_injective).tsum_add ((hs).comp_injective Subtype.val_injective)
end YM.RG3.Riding
