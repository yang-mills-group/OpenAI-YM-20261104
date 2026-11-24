import YM.RG3.Script.Pipes

/-!
# Buying reconstruction into actuated regular errors, then issuing

Synergy with local cumulant/analytic/local iteration obligations: evaluate
on C decks. Read = ALL signed terms behind the compact-hull analytic test
at THEIR actual masks (or unmasked globals, or purchased kernels). Conserve
the headers up to this explicit list, which has no K suppliers. Then low
jet test & high analytic grants on the grouped germs and conservation only
on actual common masks. Need strong support OR radius/halo supplies to price
this (`lit`,`Survey`). Don't require the original regular modified terms to
have close coefficients to each other termwise, they are only charged to
the flag layer once; use the full occupied-root convention. Alternatives
for unanchored vacuum displacements later. This is a pure-source operation;
the incoming full K may encode also unmarked partners of prior transports.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Script
open Function Lattice RG Wilson Overlay Marker RG3.Forms RG3.Render RG3.Press Ac Extra.Multi Push.AbsoluteSums MeasureTheory Extra.Iteration
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {n:Side} {ι V:Type*} [DecidableEq V] {R:Census V} {ζ:V→Site n} {G : Gauge}
  {A : Estate n R} (T : A.Truss ι G)
  (F : ℕ→ Config G n→ℂ)
  (a b c d u v σ : ℝ)
  {w : V→ℝ} {p : BudgetPoint}
  {q : Edition ζ R G}

namespace Estate.Truss
def LogRepair (p : BudgetPoint): A.plan.Repair G ι ℕ:=⟨T.strand p,A.trace p F⟩

structure Agreement [Fintype V] (w : V→ℝ)(p : BudgetPoint) (ζ:V→Site n) (M:ℕ)(a c d:ℝ) (coupon : ℕ→ℝ): Prop where
  estate : A.Legal ζ
  places : T.Laws ζ
  occupied : Occupancy ζ M
  solvent : ∃ f : ι→ℝ,T.Strap w p (a+1) d f
  commonMask i U : Healthy p.threshold (A.region i) U → T.stated i U= F i U
  regular i : p.Regular (A.region i) (F i)
  price i x : x∈A.region i → p.supBounds x (A.region i) (F i) (coupon i)
  tariffs v : SumBudget (per p.B (a+1) w A.style A.region coupon v) c

variable {T F c d a} {f : ℕ→ℝ} {M : ℕ}
variable [Fintype V]

lemma issuedBy [Countable ι] {u:ι→ℝ} (h:T.Agreement F w p ζ M (p.supportExponent+1) c d f) (h1:T.Strap w p (p.supportExponent+1+1) d u)(hw : ∀ i,0<w i)
    (hc : 0 ≤ c)(hd : 0 ≤ d):
    let Q:=T.LogRepair F p
    let tariff:=(M:ℝ)*siteFactor p.B*d+(M:ℝ)*siteFactor p.B*c
    Join p Q.read.tally ((A.render ζ F).log p) w ζ Q.notes (Q.rates u f) tariff ∧
      (A.render ζ F).Principle p ∧ (A.render ζ F).Grant p w (p.supportExponent+1+1) 0 c 0 f:=by
  intro Q tariff
  let a:=p.supportExponent+1; let B:=p.B
  let f₁:= u
  have hf:=T.admission h.estate hw h.occupied hd h1
  have ht i : A.post i∈ A.region i:= (Next.Rank.Spindle.doors _).mpr (by simp)
  have he:= Estate.pay h.estate hw h.occupied hc (fun i=>h.price i _ (ht i)) h.tariffs
  have hl : Q.Local p ζ:= ⟨T.certified ζ _ h.places h.estate, Estate.credits h.regular h.estate,fun i U hi=>by
    change Healthy p.threshold (A.region i) U at hi; change (T.strand p).peek i U = (A.trace p F).peek i U; rw [T.apparent p i U hi,h.commonMask i U hi,Estate.snap,masked_eq _ _ _ _ hi]⟩
  have ha : 0≤a:=by have:=p.exponent_pos; unfold a; linarith
  let g:=Q.notes
  have hP:g.Worth w B a (Q.rates f₁ f) tariff:= Q.purchase hw ha hf he
  have hK:g.Keeps p ζ:=Q.lawful hl
  let L:=A.render ζ F
  have hhot i : Feed.hot (g.mode i):= fun H=> (A.hot i).ne_empty (congrArg Subtype.val H)
  refine ⟨⟨hK,hP,hhot,fun U=>?_⟩,Estate.advised h.regular h.estate,
    Estate.insured (fun i=>(h.price i _ (ht i)).1) (fun i y hy=>h.price _ _ (h.estate i y hy)) h.tariffs⟩
  have hE:= hf.counted hw ha U; have hE':= he.counted hw ha U
  have hm : (Q.newWay.tally U)=L.log p U:=by
    change _=((∑ i:V, Poly.send (R.fire i) (L.pure i))+_)+L.footer.chord
    unfold L Estate.render Estate.verse; simp only [Pi.zero_apply,Poly.send_zero,Finset.sum_const_zero,zero_add,Forms.Captions.chord,tsum_zero,add_zero]; rfl
  have hr : (Q.notes.text U)= Q.read.tally U-Q.newWay.tally U:= by
    change g.text U=_; unfold Feed.text; simp_rw [if_pos (hhot _)]
    let s:=hE.sub hE'
    have h:= s.tsum_eq
    refine (tsum_congr (fun i=>?_)).trans h
    change Poly.send (A.style i) (_-_) = Poly.send (A.style i) _-Poly.send (A.style i) _
    ext i; simp only [sub_eq_add_neg,Poly.part_plus,Poly.part_neg,Poly.part_send]; split <;> first|simp|rfl
  rw [hr,hm]; abel


lemma issued [Countable ι] (h:T.Agreement F w p ζ M (p.supportExponent+1) c d f)(hw : ∀ i,0<w i)
    (hc : 0 ≤ c)(hd : 0 ≤ d):
    let Q:=T.LogRepair F p
    let tariff:=(M:ℝ)*siteFactor p.B*d+(M:ℝ)*siteFactor p.B*c
    ∃ bills:ℕ→ℝ, Join p Q.read.tally ((A.render ζ F).log p) w ζ Q.notes bills tariff ∧
      (A.render ζ F).Principle p ∧ (A.render ζ F).Grant p w (p.supportExponent+1+1) 0 c 0 f:=by
  intro Q tariff
  obtain ⟨u,H⟩:=h.solvent
  exact ⟨_, issuedBy h H hw hc hd⟩

section short
open Axial Pan Next.Rank.Spindle
structure Dawn (K : ℕ) (p : BudgetPoint)(m : ℕ→ℝ)(T : Estate.Truss A ι G) where
  eps : ℕ→ℝ
  high : ℕ→ℝ
  through : ℕ→ℕ
  order : p.order ≤ K
  shoots i : Axial.Ordinary (T.stated i ∘ increment 1) (through i) K (dues p (A.radius i)) (eps i) (high i)
  fresh i : balance G K (through i) (dues p (A.radius i)) (eps i) (high i) ≤ m i
-- alternate palette representation may avoid analytic estimates on Q=Links; require still local F but only compare raw discrepancy on TRUE hull mask
structure Bright (K:ℕ)(p:BudgetPoint)(m:ℕ→ℝ)(F:ℕ→Config G n→ℂ) (eps high : ℕ→ℝ) (through:ℕ→ℕ)(paint : (i:ℕ)→ Palette G (A.radius i)→ℂ) : Prop where
  order : p.order ≤ K
  shoots i : Axial.Ordinary (paint i) (through i) K p.threshold (eps i) (high i)
  fresh i : ModeEstimate.Tariff G K (A.radius i) (through i) p (eps i) (high i) ≤ m i
  horizon i U : Healthy p.threshold (A.region i) U→F i =ᶠ[𝓝 U] paint i ∘ palette (A.radius i) (A.post i)
  chart i : GaugeInvariant (F i) ∧ LocalOn ↑(A.region i) (F i) ∧ Measurable (F i)

omit [Fintype V] in
lemma covered {K}(h:Dawn (A:=A) K p f T)(hS:Rules G)(hn:∀ i,2*(A.radius i+1)<n.val)
    (hα:∀ i,4*(A.radius i:ℝ)*p.threshold ≤ hS.c)(hJump:∀ i,dues p (A.radius i)<SelectedOrderedKernels.radius G K)
    [Countable ι](hL:T.Laws ζ): ∀ i,p.Regular (A.region i) (T.stated i) ∧ ∀ x∈A.region i,p.supBounds x (A.region i) (T.stated i) (f i):=by
  intro i
  obtain ⟨hw,hX,hY⟩:=T.status ζ hL i
  obtain ⟨H,HH⟩:= rent hw hY (h.shoots i) (o:=A.post i) (Finset.Subset.refl _) hS (hα i) (hn i) (hJump i) hX h.order
  exact ⟨H,fun x hx=> ⟨(HH x hx).1.trans (h.fresh _),fun y hh l hh' hL=>(HH x hx).2 y hh l hh' hL|>.trans (h.fresh _)⟩⟩

omit [Fintype V] in
lemma shines {K eps high through paint}(h:Bright (A:=A) K p f F eps high through paint)(hn:∀ i,2*(A.radius i+1)<n.val): ∀ i,p.Regular (A.region i) (F i) ∧ ∀ x∈A.region i,p.supBounds x (A.region i) (F i) (f i):=by
  intro i
  obtain ⟨hi,hL,hB⟩ := h.chart i
  obtain ⟨H,hx⟩ := ModeEstimate.elevated (hn i) hi hB hL (Finset.Subset.refl _) (h.horizon i) (h.shoots i) h.order
  refine ⟨H,fun y he=>⟨(hx y he).1.trans (h.fresh _),fun U hU l hh ha=>((hx y he).2 _ hU l hh ha).trans (h.fresh _)⟩⟩
end short
end Estate.Truss
end YM.RG3.Script
