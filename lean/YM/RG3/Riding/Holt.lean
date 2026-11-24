import YM.RG3.Riding.Barley
/-! # The literal physical reconstruction through compressed dictionary

and any further books built around it. Proof at *all configurations*,
using fired flags and original weather, preserves kernels & orientations
and Couple law denominator. Includes price of quiet K at stronger input
ON VIRTUAL FOLIO (not on old). Need strongest exponent on economic Towed
K (e.g. output p.exp+1 with v.straw for one Script at p). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Riding
open RG Wilson Lattice Function Marker Overlay RG3.Script RG3.Held
 RG3.Forms RG3.Ink Extra.Trajectories Extra.Iteration Extra.Multi Ac Push.Local Press
 Push.AbsoluteSums Push.Corrected MergeProof Accent Finset
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {n : Side}{V:Type*}[DecidableEq V](R:Census V){G:Gauge}
  (P : Rep G n){p:BudgetPoint}{ζ:V→Site n}{w:V→ℝ}
variable {R}
-- crammed K agrees EXACTLY
lemma concord (ζ : V→ Site n){δ t: ℝ}(h:P.activities.Valid P.p δ t)(i:Box n) (U:Config G n): bass (virtual R G P ζ) i U=bass P i U:=by
  let W:=material R G P ζ
  let Q:= W.ledger P
  have hi(c:mortar n) : Q.activities.forced (pin c) = mason G c:= W.currency P c
  have hu : ∀ c:mortar n, (Q.activities.K (pin c) U:ℂ)=bass P c.val U:=by
    intro c; rw [W.fixed]
    change Complex.ofReal (((Poly.send R.quiet _).part R.quiet).re)= _
    rw [Poly.part_send,if_pos rfl]; exact Complex.ext rfl (chorus P _ _ h).symm
  have ht j (hh:j∉Set.range (pin (α:=mortar n))):Q.activities.K j U=0:= congrFun (W.blankK P j hh) U
  by_cases hI:Sure i
  · unfold bass profile cram; let c:mortar n:=⟨i,hI⟩
    let j₀ : {j : ℕ // barcode Q.activities j = i}:=⟨pin c,by unfold barcode; rw [hi]; rfl⟩
    change (∑' j:{j//barcode Q.activities j=i},(Q.activities.K j.val U : ℂ))=bass P i U
    rw [tsum_eq_single j₀]
    · exact hu c
    intro j hh
    by_cases hg:j.val∈Set.range (pin (α:=mortar n)); swap
    · exact_mod_cast ht _ hg
    obtain ⟨l,hL⟩:=hg
    have hj: l.val=i := by have hh:=j.property; unfold barcode at hh; rw [← hL,hi l] at hh; exact (show (l.val.1,l.val.2)=_ from hh)
    have hk:l=c:=Subtype.ext hj
    exact (hh (Subtype.ext (hL.symm.trans (congrArg pin hk)))).elim
  -- no address on either uses such an impossible box
  have hv (Q:Rep G n): bass Q i U=0:= by
    haveI : IsEmpty {j//barcode Q.activities j=i}:= ⟨fun j=> hI (j.property ▸ ⟨(Q.activities.forced j.val).inventory_ne,(Q.activities.forced j.val).inventory_sup⟩)⟩
    unfold bass profile cram; exact tsum_empty
  exact (hv _).trans (hv _).symm

variable (ζ)
lemma dual {σ C Λ e t t':ℝ}(h:P.Lawful σ C Λ e t)(hp:(virtual R G P ζ).activities.Valid (virtual R G P ζ).p e t')(U:Config G n):
    (virtual R G P ζ).activities.gas (virtual R G P ζ).p U=P.activities.gas P.p U:=by
  let F (i : Box n):= Poly.send R.quiet (bass P i U)
  have he (i) : (F i).part R.quiet = bass P i U:=by unfold F; rw [Poly.part_send,if_pos rfl]
  have hh i: (F i).part R.quiet= bass (virtual R G P ζ) i U:= (he i).trans (concord (R:=R) P ζ h.labels i _).symm
  apply Complex.ofReal_injective
  exact (stage₀ (virtual R G P ζ).activities (virtual R G P ζ).p U (F:=F) (mass_crest _ hp _) hh).symm.trans (stage₀ P.activities P.p U (mass_crest _ h.labels _) he)
lemma exponent (U : Config G n):(virtual R G P ζ).exponent U=P.exponent U:=rfl
lemma equality {σ C Λ e t t':ℝ}(h:P.Lawful σ C Λ e t)(hp:(virtual R G P ζ).activities.Valid (virtual R G P ζ).p e t')(U:Config G n):(virtual R G P ζ).eval U=P.eval U:= by
  unfold Rep.eval; rw [exponent (ζ:=ζ) P,dual (R:=R) P ζ h hp U] -- order

-- strong certificate on virtual ledger at actual exponent. supply once.
structure Slate (S δ:ℝ) (a:mortar n → ℝ) : Prop where
  nonneg i:0 ≤ a i
  owns (i:mortar n)(U:Config G n): ‖bass P i.val U‖ ≤ a i
  hit:Hit (fun i:mortar n=>i.val.1) P.p.B a S δ

def concrete (a:mortar n→ℝ):ℕ→ℝ:=unpin a 0
variable {S δ:ℝ}{a:mortar n→ℝ} (h:Slate P S δ a)
include h
lemma billed :
    (∀ i,0 ≤ concrete a i ∧ ∀ U,‖(virtual R G P ζ).activities.K i U‖ ≤ concrete a i) ∧
      Hit (fun i=>((virtual R G P ζ).activities.forced i).support) P.p.B (concrete a) S δ:=by
  let W:=material R G P ζ
  have he j (hp:j∉ Set.range (pin (α:=mortar n))):concrete a j=0:=unpin_blank _ _ hp
  have hl(j:mortar n):concrete a (pin j)=a j:=unpin_pin ..
  constructor
  · intro i; by_cases hh:i∈Set.range (pin (α:=mortar n))
    · obtain ⟨j,rfl⟩:=hh; rw [hl]; refine ⟨h.nonneg _,fun U=>?_⟩
      unfold virtual; rw [Article.fixed]; change ‖Complex.re ((Poly.send R.quiet _).part R.quiet)‖ ≤ _
      rw [Real.norm_eq_abs,Poly.part_send,if_pos rfl]
      exact (Complex.abs_re_le_norm _).trans (h.owns j U)
    unfold virtual; rw [Article.blankK _ P i hh,he i hh]; simp
  intro i
  refine Pad.absolute pin (pin_injective (α:=mortar n)) (fun j=>?_ ) ?_ (h.hit i)
  · unfold virtual; dsimp only; simp only [Article.currency,hl]; rfl
  intro j hj; by_contra ht; apply hj; dsimp only; rw [he j ht]; split <;> simp
end YM.RG3.Riding
