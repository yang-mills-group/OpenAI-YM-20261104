import YM.RG3.Render.Scores

/-!
# Mixed assembly at slats

Eq parts evaluated first pointwise on common masks & their actual complement,
then repacked into new Cartesian/label addresses; no analytic termwise
differentiation or use of an extension off the group. Provide front channel
unchanged to consume only changes in Test. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Render.Stage.Repair
open RG RG3.Forms RG3.Press Marker Lattice Wilson Finset Function MeasureTheory Overlay Ac Push.AbsoluteSums
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {V : Type*} [DecidableEq V] {R : Census V} {P : Rep G n} (d : Deck R P)
variable {I J α : Type*} {t : Render.Stage n R α} (S : t.Repair G I J)
variable {w B a δ δ' u b}

/-- Split the summed overlay from an additive feed with absolute purchase.
No prescription for where its factors can be used (merged in Forms.Test).
Supply `Keeps` after assigning predicates to line.
-/
theorem remit (v : V → Site n) (f : Feed G n R α) (h : f.Keeps P.p v) (hw : ∀ i,0<w i) (ha : 0 ≤ a)
    (hp : f.Worth w B a u δ) (U : Config G n) :
    ∑' i,Poly.send (f.mode i) (f.value i U)=Poly.send R.quiet (f.bare U) + f.text U := by
  have hs := hp.usage ha hw U
  let hot (i:α) := if Feed.hot (f.mode i) then Poly.send (f.mode i) (f.value i U) else 0
  let cold (i:α) := if Feed.hot (f.mode i) then (0:ℝ) else (f.value i U).re
  have hf : Summable cold := Summable.of_norm ((hs.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => show ‖cold i‖ ≤ _ from by
    unfold cold; split; simp; exact Complex.abs_re_le_norm _)))
  let Q : ℝ →+ Poly R := (Poly.bead R).toAddMonoidHom.comp Complex.ofRealAm
  have hh : HasSum (fun i => Q (cold i)) (Poly.send R.quiet (f.bare U)) :=
    hf.hasSum.map Q ((Bands.sends _).comp Complex.continuous_ofReal)
  have he : Summable hot := (Poly.budgeted hw (hp.weighted_enough ha hw) fun i => by
    unfold hot; split
    · rw [Poly.solo]; exact mul_le_mul_of_nonneg_left (hp.always i U) (Poly.worth hw _).le
    rw [Poly.zero_price]; exact mul_nonneg (Poly.worth hw _).le (hp.positive i)).1
  rw [← hh.tsum_eq,show f.text U = tsum hot from rfl, ← hh.summable.tsum_add he]
  refine tsum_congr (fun i => ?_)
  unfold cold hot; split
  next h' => rw [map_zero,zero_add]
  next h' =>
    rw [add_zero]; change _ = Poly.send R.quiet _
    rw [not_ne_iff.mp h']; congr 1
    exact Complex.ext rfl (h.real i U h')

variable [Fintype V]

/-- Caller need compare analytic identities only on the *stronger actual
mask*. Still needs identify own decompositions literally on Config including
clipped paths and signed pieces---not an equivalence modulo represented
articles. -/
structure Bulletin (Q : Rep G n) (o : Deck R Q) : Type _ where
  ambient : Config G n → Poly R
  first U : header P d U=ambient U+S.read.tally U
  second U : header Q o U=ambient U+S.newWay.tally U
  rebate : S.Local P.p d.contents.origins

variable {Q : Rep G n} (o : Deck R Q)

theorem publish [Countable I] [Countable J] (z : S.Bulletin d Q o) (clock : P.p=Q.p) (he : d.contents.origins=o.contents.origins)
    (hw : ∀ i,0<w i) (ha : 0≤a) (hr : S.read.Price w B a δ u) (ho : S.newWay.Price w B a δ' b)
    {v i r s x y v' i' r' s' x' y'} (hd : d.Active) (ht : d.Budget v i r s x y) (hD : o.Active) (hT : o.Budget v' i' r' s' x' y') :
    S.notes.Keeps P.p d.contents.origins ∧ S.notes.Worth w B a (S.rates u b) (δ+δ') ∧ Adjust d S.notes Q o := by
  have H := S.purchase hw ha hr ho
  have hh := S.lawful z.rebate
  have hv (U) : header P d U=header Q o U+Poly.send R.quiet (S.notes.bare U)+S.notes.text U := by
    rw [z.first,z.second,add_assoc,add_assoc,← remit (P:=P) d.contents.origins S.notes hh hw ha H U]
    congr 1
    have h1 := hr.counted hw ha U
    have h2 := ho.counted hw ha U
    have hsum := (h1.sub h2).tsum_eq
    suffices heq : (∑' i,Poly.send (S.notes.mode i) (S.notes.value i U))=S.read.tally U-S.newWay.tally U by rw [heq]; abel
    refine (tsum_congr (fun i => ?_)).trans hsum
    change Poly.send _ (_-_) = _
    apply Poly.ext; intro i'
    simp only [sub_eq_add_neg,Poly.part_plus,Poly.part_send,Poly.part_neg]
    unfold notes Feed.mode; dsimp only; split <;> simp
  refine ⟨hh,H,clock,he,fun U => ?_,fun U => ?_⟩
  · suffices (↑(P.exponent U):ℂ)=↑(Q.exponent U)+↑(S.notes.bare U) by
      exact Complex.ofReal_injective (this.trans (Complex.ofReal_add ..).symm)
    have hc := congrArg (fun x : Poly R => x.part R.quiet) (hv U)
    simpa only [header, Poly.part_plus, Poly.part_send,↓reduceIte,d.quiet hd ht,o.quiet hD hT,H.quiet_text ha hw,add_zero] using hc
  apply Poly.ext; intro i
  by_cases h : i=R.quiet
  · subst i
    rw [Poly.part_plus,d.quiet hd ht,o.quiet hD hT,H.quiet_text ha hw,add_zero]
  have hh := congrArg (fun x : Poly R => x.part i) (hv U)
  simpa only [header,Poly.part_plus,Poly.part_send,if_neg h,zero_add,add_zero] using hh
end YM.RG3.Render.Stage.Repair
