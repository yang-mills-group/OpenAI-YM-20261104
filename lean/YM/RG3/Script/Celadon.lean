import YM.RG3.Script.Horns

/-!
# Preserve sources on the full Deck through canonical SPRAY and K subtraction

Represent comparison with the formal/model Deck Z living on SAME P & origins.
Never need to identify Z's merged K names with the produced ones; issue the
conservative subtraction when assessing the error (cost the full divided K
receipt for both).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Script.Edition
open Function Lattice RG Wilson Overlay Marker RG3.Forms RG3.Render RG3.Press RG3.Primary RG3.Law Ac Extra.Multi Push.AbsoluteSums MeasureTheory Extra.Iteration Source Push.Local Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {n : Side} {V : Type} [DecidableEq V] [Fintype V]{R:Census V}{ζ:V→Site n}{G : Gauge}
 {P : Rep G n}(d d':Deck R P)(e : Edition ζ R G)

/-- Rest deck. Complete K tagged discrepancy on its own addresses, NOT
compare in evaluated gas. -/
def jetty : Deck R P where
  contents := {
    origins:=ζ, support:=e.home, units:=e.pure, rays:=e.pins,H:=e.song
    marks i:=blend (d.contents.marks i) (d'.contents.marks i)
    entries i:=blend (d.contents.entries i) (-d'.contents.entries i) }
  captions:=e.footer

variable {e}
omit [Fintype V] in
lemma lyric (he:e.Principle P.p)(h:d.Active)(h':d'.Active)(hz:d.contents.origins=ζ)(hZ:d'.contents.origins=ζ): (jetty d d' e).Active:= by
  let T:= (jetty d d' e).contents
  have hv i j : (T.marks i j).val.Nonempty ∧ (T.entries i j≠0 → ∀ s∈ (T.marks i j).val,ζ s∈(P.activities.forced i).support) ∧
      UsesFinal P.p.threshold (P.activities.forced i).support (T.entries i j) ∧ (∀ x, T.entries i j x≠0→(P.activities.forced i).eligible P.p.threshold x) ∧ Measurable (T.entries i j) ∧ GaugeInvariant (T.entries i j):= by
    cases hx: numbering (ℕ⊕ℕ) j with
    | inl j=>
      simp only [T,jetty,from_left _ _ hx,← hz]
      exact ⟨h.articles.occurs _ _,h.articles.retained _ _,h.articles.inspects _ _,h.articles.keeps _ _,h.articles.meas _ _,h.articles.invi _ _⟩
    | inr j=>
      unfold T jetty blend; simp only [comp_apply,hx,Sum.elim_inr,← hZ,Pi.neg_apply,neg_ne_zero]
      refine ⟨h'.articles.occurs _ _,h'.articles.retained _ _,(fun a b ha hb=> congrArg Neg.neg (h'.articles.inspects i j a b ha hb)), h'.articles.keeps _ _,(h'.articles.meas _ _).neg,fun k U=> congrArg Neg.neg (h'.articles.invi i j k U)⟩
  exact ⟨⟨he.hot,he.rem,he.reg,fun i j=> (hv i j).1,fun i j=>(hv i j).2.1,fun i j=>(hv i j).2.2.1,
    fun i j=>(hv i j).2.2.2.1,fun i j=>(hv i j).2.2.2.2.1,fun i j=>(hv i j).2.2.2.2.2⟩,he.vertical⟩

variable {w : V→ℝ}

private def numberRows : ℕ × ℕ ≃ (ℕ×ℕ)⊕(ℕ×ℕ):= (Equiv.prodCongr (Equiv.refl ℕ) (numbering (ℕ⊕ℕ))).trans (Equiv.prodSumDistrib ..)

omit [Fintype V] in
lemma kept {a u c Y:ℝ}{f:ℕ→ℝ}(he:e.Grant P.p w a u c Y f)(ha:P.p.supportExponent ≤ a){b i j x i' j' x' t t':ℝ}
    (h:d.Budget w i j t b x)(h':d'.Budget w i' j' t' b x'): (jetty d d' e).Budget w u c (t+t') b Y:= by
  obtain ⟨hx,hM⟩:= grant (d:=d) he h.radial.pure ha
  let T:=(jetty d d' e).contents
  obtain ⟨z,hz,H⟩:=h.radial.hits; obtain ⟨z',hz',H'⟩:=h'.radial.hits
  let g : ℕ×ℕ→ℝ:= fun i=>blend (fun j=>z (i.1,j)) (fun j=>z' (i.1,j)) i.2
  refine ⟨⟨h.radial.pure,hx.allowance,h.radial.factor,hx.bulk, g,fun i j=>?_,fun i=>?_⟩, hM⟩
  · cases hy:numbering (ℕ⊕ℕ) j with
    | inl s => simpa only [T,jetty,g,from_left _ _ hy] using! hz i s
    | inr s => simpa only [jetty,g,from_right _ _ hy,Pi.neg_apply,norm_neg] using! hz' i s
  let S (d : Deck R P)(c:ℕ×ℕ→ℝ)(j:ℕ×ℕ):=if i∈(d.contents.marks j.1 j.2).val then Poly.toll w (d.contents.marks j.1 j.2)*P.p.mass (P.activities.forced j.1).support (c j) else 0
  change SumBudget (S (jetty ..) g) _
  rw [show S (jetty d d' e) g= (fun i=> Sum.elim (S d z) (S d' z') (numberRows i)) from ?_,add_mul]; swap
  · funext j; unfold numberRows g S jetty
    cases hi:numbering (ℕ⊕ℕ) j.2 with
    | inl k=> simp [blend,hi,Prod.map_def,Equiv.prodSumDistrib]
    | inr k=> simp [blend,hi,Prod.map_def,Equiv.prodSumDistrib]
  exact Cost.equiv _ (Cost.sum (f:=Sum.elim (S d z) (S d' z')) (H i) (H' i))

lemma log_jetty (e:Edition ζ R G):(jetty d d' e).log=e.log P.p:=rfl

def Kbase (i : ℕ)(U : Config G n)(P : Rep G n):Poly R:= Poly.send R.quiet (P.activities.K i U:ℂ)

lemma packed {b i j x i' j' x' t t' mv mk:ℝ}
    (h:d.Budget w i j t b x)(h':d'.Budget w i' j' t' b x')(hn:d.Active)(hn':d'.Active)(hP:P.activities.Valid P.p mv mk)(e:Edition ζ R G) (i U):
    d.contents.each i U=d'.contents.each i U+((jetty d d' e).contents.each i U-Kbase i U P):=by
  let Q j:=d.contents.tagged i j U; let S j:=d'.contents.tagged i j U
  have hQ: Summable Q:= (d.contents.baseBound hn.articles h.radial hP U).1 _
  have hS: Summable (fun j=> -S j):= Summable.neg ((d'.contents.baseBound hn'.articles h'.radial hP U).1 i)
  change Kbase i U P+tsum Q = Kbase i U P+tsum S+((Kbase (R:=R) i U P + _)- Kbase i U P)
  let D:=(jetty d d' e).contents
  rw [add_sub_cancel_left,show (fun j=>D.tagged i j U) = blend Q (fun j=>-S j) from ?_,(blended hQ hS).2,tsum_neg]; swap
  · funext j; cases he:numbering (ℕ⊕ℕ) j with
    | inl k=> simp [D,jetty,Q,S,Bands.tagged,blend,he]
    | inr k=> simp [D,jetty,Q,S,Bands.tagged,blend,he]; ext; simp only [Poly.part_send,Poly.part_neg]; split <;> simp
  abel

variable (a : Deck R P)

/-- Singleton equality w.r.t full Deck (all partners intact incl
shared tags, captions). Doesn't require canonical here. Later use with
`Law.candle`. Multi-source consumer should instead expand the *full* d
using the log and additive sector specification; no linearity of d at
higher grades claimed. -/
lemma one_stamp {Θ Θ' Θ₀ : V→ℝ} {u c d'0 b a0 u' c' d'1 b' a' u₀ c₀ d'2 b₀ a'₀ δ K:ℝ}
    (h:d.Active)(h':d'.Active)(H:a.Active)(he:d.Budget Θ u c d'0 b a0)
    (he':d'.Budget Θ' u' c' d'1 b' a')(hA:a.Budget Θ₀ u₀ c₀ d'2 b₀ a'₀)(hP:P.activities.Valid P.p δ K)
    (hl:d.log=d'.log+a.log) (hf : ∀ i U,d.contents.each i U=d'.contents.each i U+(a.contents.each i U-Kbase i U P)) (s:V)(U):
    (d.density U).part (R.fire s)=(d'.density U).part (R.fire s)+(a.density U).part (R.fire s):= by
  have hL:= congrArg (fun i : Config G n→ Poly R=> (i U).part (R.fire s)) hl
  simp_rw [Pi.add_apply,Poly.part_plus] at hL
  have hf₁ i:= congrArg (fun x : Poly R=> x.part (R.fire s)) (hf i U)
  have hZ i : (Kbase (R:=R) i U P).part (R.fire s)=0:= by rw [Kbase,Poly.part_send,if_neg (R.fire_hot _)]
  simp_rw [sub_eq_add_neg,Poly.part_plus,Poly.part_neg,hZ,neg_zero,add_zero] at hf₁
  have hg i := (inked s d h he hP i U).1
  have hg' i := (inked s d' h' he' hP i U).1
  have hG i := (inked s a H hA hP i U).1
  have hp (i:Finset ℕ): (d.contents.packet i U).part R.quiet=(d'.contents.packet i U).part R.quiet ∧
      (d.contents.packet i U).part R.quiet=(a.contents.packet i U).part R.quiet ∧
      (d.contents.packet i U).part (R.fire s)=(d'.contents.packet i U).part (R.fire s)+(a.contents.packet i U).part (R.fire s):= by
    unfold Bands.packet; split
    · simp_rw [MergeProof.Accent.shockProd₀,MergeProof.Accent.shockProd,hg,hg',hG,hf₁,add_mul]; rw [Finset.sum_add_distrib]; simp
    simp
  have hd(X:Deck R P) (HX:X.Active){w u c t b z}(HB:X.Budget w u c t b z):
      (X.density U).part (R.fire s)=(Real.exp (P.exponent U):ℂ)*((X.contents.cluster U).part (R.fire s)+(X.log U).part (R.fire s)*(X.contents.cluster U).part R.quiet):= by
    unfold Deck.density; rw [Poly.part_smul,MergeProof.Accent.shock,Poly.pass_part _ (X.quiet HX HB U),MergeProof.Accent.whisper _ _ (X.quiet HX HB U) s,one_mul]
  rw [hd d h he, hd d' h' he', hd a H hA,hL]
  have hc : (d.contents.cluster U).part R.quiet=(d'.contents.cluster U).part R.quiet ∧
      (d.contents.cluster U).part R.quiet=(a.contents.cluster U).part R.quiet ∧
      (d.contents.cluster U).part (R.fire s)=(d'.contents.cluster U).part (R.fire s)+(a.contents.cluster U).part (R.fire s):= by
    have hb (q:Deck R P) {w u c t b y}(H:q.Active)(h:q.Budget w u c t b y):= (q.contents.population H.articles h.radial hP U).1
    simp_rw [Bands.cluster,Poly.share (hb d h he),Poly.share (hb d' h' he'),Poly.share (hb a H hA)]
    have hs:=(hb d' h' he').hasSum.map (Poly.get (R.fire s)) (Poly.part_cont _)
    have Hs:=(hb a H hA).hasSum.map (Poly.get (R.fire s)) (Poly.part_cont _)
    constructor
    · exact tsum_congr (fun i=>(hp i).1)
    constructor
    · exact tsum_congr (fun i=>(hp i).2.1)
    rw [tsum_congr (fun i=>(hp i).2.2)]; exact Summable.tsum_add hs.summable Hs.summable
  rw [← hc.2.1,←hc.1,hc.2.2]; ring
end YM.RG3.Script.Edition
