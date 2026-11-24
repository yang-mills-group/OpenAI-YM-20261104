import YM.RG3.Script.Estate
 import YM.RG3.Forms.Rewrite

/-! # Quantitative pure-source additive transports before the merger.
Several can stack, each charging s through true information before scalar
or invariant tests. Don't spend the K divisor each time! Compose the edits
and publish once if only one K reserve. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Script
open Function Lattice RG Wilson Overlay Marker RG3.Forms RG3.Render RG3.Press Ac Extra.Multi Push.AbsoluteSums MeasureTheory Extra.Iteration
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {n:Side} {α V:Type*} [DecidableEq V] {R:Census V} {ζ:V→Site n} {G : Gauge} [Fintype V]

lemma living {p} {q:Edition ζ R G}{u v d a:ℝ}{w:V→ℝ}{f:ℕ→ℝ}(hw:∀ i,0<w i)(he:q.Principle p)(h:q.Grant p w a u v d f)(ha:p.supportExponent ≤ a) (U:Config G n):
    Summable (fun i=>q.birth p i U) ∧ Summable (fun j=>Poly.send (q.footer.tag j) (q.footer.value j)):= by
  have hr:= label_budget hw h.nn ha h.more
  have hC:= q.footer.chords he.vertical (show q.footer.Paid w p d from ⟨label_budget hw (fun _=>norm_nonneg _) ha h.captions⟩) hw
  let F (j):=Poly.toll w (q.pins j)*p.mass (q.home j) (f j)
  have hi : Summable F:= (per_system (P:=q.pins) (c:=v) (fun i=>mul_nonneg (Poly.worth hw _).le (mul_nonneg (Real.exp_pos _).le (h.nn i))) he.hot hr).2.1
  refine ⟨(Poly.budgeted hw hi (fun i=>?_)).1,hC.1⟩
  unfold Edition.birth F; rw [Poly.solo]; apply mul_le_mul_of_nonneg_left _ (Poly.worth hw _).le
  apply le_trans _ (p.loMass _ _ (h.nn _))
  obtain ⟨x,hx⟩:=he.hot i
  by_cases hy:Healthy p.threshold (q.home i) U
  · rw [masked_eq _ _ _ _ hy]; exact (h.pay _ _ hx).2 U hy [] (Nat.zero_le _) (by simp)
  rw [masked_ne _ _ _ _ hy,norm_zero]; exact h.nn _

/-- Price/seal on arbitrary additive logs (including intermediate emissions
not yet declared Formula.Conserved on d). Always tested at +1 cover exponent
before final Test. Use with receipts a≥p.supportExponent+2 on Rooted to
arrange. Asks Kept/stratum correspondence rather than post-adjustment
comparison. -/
structure Join (p:BudgetPoint) (x y : Config G n→ Poly R) (w:V→ℝ) (ζ:V→Site n)
    {ι:Type*} (f:Feed G n R ι)(b:ι→ℝ)(δ:ℝ):Prop where
  keeps : f.Keeps p ζ
  worth : f.Worth w p.B (p.supportExponent+1) b δ
  pure (i): Feed.hot (f.mode i)
  fusion U : x U=y U+f.text U

namespace Join
variable {ι I:Type*}{p:BudgetPoint}{w:V→ℝ}{s u : ℝ}{f:Feed G n R ι}{b:ι→ℝ}{x y z:Config G n→Poly R}
variable (h:Join p x y w ζ f b s)
include h
 omit [Fintype V] in
lemma texts (hw:∀i,0<w i) (U:Config G n):
    f.text U=(∑' i, Poly.send (f.mode i) (f.value i U)) ∧ Summable (fun i=>Poly.send (f.mode i) (f.value i U)):= by
  unfold Feed.text; simp_rw [if_pos (h.pure _)]
  have ha : 0 ≤ p.supportExponent+1:= (by linarith [p.exponent_pos])
  refine ⟨trivial,(Poly.budgeted hw (h.worth.weighted_enough ha hw) (fun i=>show Poly.price w (Poly.send (f.mode i) (f.value i U)) ≤ _ from ?_)).1⟩
  rw [Poly.solo]; exact mul_le_mul_of_nonneg_left (h.worth.always ..) (Poly.worth hw _).le

 omit [Fintype V] in
lemma dark0 (c:Column R n) (U:Config G n) : (f.slip c U).part R.quiet=0:= by
  unfold Feed.slip; split
  next ht=> rw [Poly.part_send,if_neg (Ne.symm ht)]
  next ht=>
    unfold Feed.row
    have H (j : f.office c) : Feed.hot (Feed.domain c):= by rw [← f.serves c j]; exact h.pure _
    rw [tsum_congr (g:=fun _=>0) (fun i=>(ht (H i)).elim),tsum_zero,Complex.zero_re,Real.exp_zero,Complex.ofReal_one,sub_self,map_zero]; rfl

variable (f) (g:Feed G n R I)
def series : Feed G n R (ι⊕I) := ⟨Sum.elim f.column g.column,Sum.elim f.value g.value⟩
variable {g f}

 omit [Fintype V] in
set_option maxHeartbeats 550000 in
lemma again {c:I→ℝ}(hg:Join p y z w ζ g c u)(hw:∀i,0<w i): Join p x z w ζ (series f g) (Sum.elim b c) (s+u):= by
  let F:=series f g
  have hr i : Feed.hot (F.mode i):=by cases i <;> first|exact h.pure _|exact hg.pure _
  have H : F.Keeps p ζ:= by
    constructor
    · exact fun i _ h=> (h (hr i)).elim
    · rintro (i|i) <;> first|exact h.keeps.gauge _|exact hg.keeps.gauge _
    · rintro (i|i) <;> first|exact h.keeps.borel _|exact hg.keeps.borel _
    · rintro (i|i) <;> first|exact h.keeps.read _|exact hg.keeps.read _
    · rintro (i|i) <;> first|exact h.keeps.flags _|exact hg.keeps.flags _
    rintro (i|i) <;> first|exact h.keeps.origin _|exact hg.keeps.origin _
  have he := h.worth
  have ht :=hg.worth
  refine ⟨H,⟨fun i=>?_ , fun i=>?_,fun i=>?_⟩,hr,fun i=>?_⟩
  · cases i <;> first|exact he.positive _|exact ht.positive _
  · cases i <;> first|exact he.always _|exact ht.always _
  · apply Cost.sum (he.budget (x:=i)) (ht.budget (x:=i)) -- no implicit x?
  rw [h.fusion,hg.fusion,add_assoc]
  congr 1
  unfold Feed.text; change (∑' j,if Feed.hot (g.mode j) then _ else _) + _=∑' j, if Feed.hot (F.mode j) then Poly.send (F.mode j) (F.value j i) else 0
  simp_rw [if_pos (h.pure _),if_pos (hg.pure _),if_pos (hr _)]
  apply (add_comm ..).trans; symm; exact Summable.tsum_sum (f:=fun j=>Poly.send (F.mode j) (F.value j i)) ((h.texts hw i).2) ((hg.texts hw i).2)

 omit [Fintype V] in
lemma beside (A : Config G n→ Poly R): Join p (A+x) (A+y) w ζ f b s:= ⟨h.keeps,h.worth,h.pure,fun U=>by change A U+_ = A U+_+_;rw [h.fusion,add_assoc]⟩

section Print
variable [Nonempty V] [Countable ι] {P:Rep G n} {d D:Deck R P} {mark vac:ℝ}
variable (hJ:Join P.p d.log D.log w ζ f b s)(hz:d.contents.origins=ζ)
include hJ
omit h

def publish (X:Billboard d.contents w P.p.B (P.p.supportExponent+1) vac mark) (hw:∀i,0<w i)
    (hP:P.activities.ForcedFamily P.p)(hD:d.Active)(hS:s≤1) : RG3.Forms.Test d f s w vac mark:= {
       toBillboard:= X, radii:=hw, check:=hP, articles:=hD.articles, cents:=b, budget:=hJ.worth,
       slip:= by rw [hz]; exact hJ.keeps, sufficesStamp:=hS }

 include hz
/-- Registered pure source transport preserving the whole input at P,
also if caller model had different forced tags/discrepancies. Prices on K
at chosen radii taken at operation, restoring afterwards is separate
(see scaling). Don't run multiple times spending the reserve multiple
times---fusion first. -/
theorem copy (X:Billboard d.contents w P.p.B (P.p.supportExponent+1) vac mark) (hw:∀i,0<w i) (hP:P.activities.ForcedFamily P.p)(hD:d.Active)(hS:s≤1)
    (χ γ : ℝ) (hχ : 1 ≤ χ)(hu : χ*(vac+mark)+2*s ≤ γ) (hγ : 0≤γ)
    (green : (P.p.B+P.p.B+1:ℕ)^4*(γ:ℝ) ≤ 1)(HA:Accessible P)(Hζ:D.contents.origins=ζ) {Θ δ c d' b₀ a}
    (hb:d.Budget Θ δ c d' b₀ a) {δ0 c0 d0 b1 a0:ℝ} (Hδ : (Real.exp γ-1)/χ ≤ d0*b1)(Hb:0<b1)
    (ht:Article.Contents D.contents)(HX:Article.LogBounds D.contents w δ0 c0)(hc:D.captions.Sound D.contents.origins)(hy:D.captions.Paid w P.p a0):
    let out:=(hJ.publish hz X hw hP hD hS).task HA D
    out.Active ∧ out.Budget w δ0 c0 d0 b1 a0 ∧ out.density=d.density:=by
  apply Test.stay _ χ γ hχ hu hγ green HA ?_ hJ.dark0 hb hD Hδ Hb ht HX hc hy
  constructor
  · rfl
  · rw [hz,Hζ]
  · intro i; unfold Feed.bare; simp_rw [if_pos (hJ.pure _)]; simp
  exact hJ.fusion
end Print
end Join
end YM.RG3.Script
