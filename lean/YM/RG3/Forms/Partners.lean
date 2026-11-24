import YM.RG3.Forms.Caption
import YM.Extra.MULTISOURCE_BOUNDS.Root

/-!
# Hard partner hit account at required reserve

KBound at actual p does NOT supply this hit at stronger supportExponent by
itself. Let suppliers keep their pre-publication bounds at the stronger exponent
on the same p geometry. Marked supply may have only per-name root receipts,
importance-sampled (`w`) or ordinary; convert at fixed occupancy of *names*
into even the per-site incoming norm (uses one more exponential from marked
receipts). Supports and price numbers fixed across coupling/steps for THIS
operation, no shape reset assumed feasible. Keep all actual tests/value-zero
regions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Forms
open RG3.Ink RG3.Press Marker Lattice Wilson RG Function MeasureTheory Ac Overlay Extra.Multi Finset Push.Corrected
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {V : Type*} [DecidableEq V] {R : Census V}
variable {P : Rep G n} (t : Bands R P)

/-- Fast quiet and possibly only rooted marked at stronger support exponent `a`
(one additional unit if `Hall`). We don't demand P be fitted if repackaging
from an intermediate step. -/
structure Partners (w : V → ℝ) (B : ℕ) (a k E : ℝ) where
  vac : ℕ → ℝ
  bill : ℕ × ℕ → ℝ
  vac_pos : ∀ i,0≤vac i
  bill_pos : ∀ j,0≤bill j
  vacant : ∀ i U, ‖P.activities.K i U‖ ≤ vac i
  cover : ∀ i j U, ‖t.entries i j U‖ ≤ bill (i,j)
  anchors : ∀ i j s, s∈(t.marks i j).val → bill (i,j)>0 → t.origins s ∈ (P.activities.forced i).support
  poles : Hit (fun i => (P.activities.forced i).support) B vac a k
  rooted : Rooted (fun j : ℕ × ℕ => (t.marks j.1 j.2).val) (fun j => (P.activities.forced j.1).support) B (a+1)
    (fun j => Poly.toll w (t.marks j.1 j.2)*bill j) E

/-- If fund already comes with per-site hit rather than per-name. Keep full
count and not assume disjoint occurrence until pricing the merger. -/
structure Billboard (w : V → ℝ) (B : ℕ) (a k E : ℝ) where
  vac : ℕ → ℝ
  bill : ℕ × ℕ → ℝ
  vac_pos : ∀ i,0≤vac i
  bill_pos : ∀ j,0≤bill j
  vacant : ∀ i U, ‖P.activities.K i U‖ ≤ vac i
  cover : ∀ i j U, ‖t.entries i j U‖ ≤ bill (i,j)
  poles : Hit (fun i => (P.activities.forced i).support) B vac a k
  advert : Hit (fun j : ℕ × ℕ => (P.activities.forced j.1).support) B (fun j => Poly.toll w (t.marks j.1 j.2)*bill j) a E

namespace Partners
variable [Fintype V] {B M a k E} {w : V→ℝ} (X : Partners t w B a k E)

def array (ht : t.Active) (hw : ∀ i,0<w i) (ho : Occupancy t.origins M) (hE : 0 ≤ E) :
    Billboard t w B a k ((M:ℝ)*siteFactor B * E) where
  vac := X.vac
  bill := X.bill
  vac_pos := X.vac_pos
  bill_pos := X.bill_pos
  vacant := X.vacant
  cover := X.cover
  poles := X.poles
  advert := root_hit ho (fun j => mul_nonneg (Poly.worth hw _).le (X.bill_pos _)) hE (fun j e => by
    obtain ⟨s,hs⟩ := ht.occurs j.1 j.2
    exact ⟨s,hs,X.anchors j.1 j.2 _ hs (lt_of_le_of_ne (X.bill_pos _) (fun H => ne_of_gt e (by
       rw [← H,mul_zero])))⟩) X.rooted
end Partners

namespace Billboard
variable {t} {B : ℕ} {a k E : ℝ} {w : V → ℝ} (X : Billboard t w B a k E)

def merch (i : ℕ) := Poly.send R.quiet (X.vac i : ℂ) + ∑' j,Poly.send (t.marks i j) (X.bill (i,j) : ℂ)

structure Qualitative (i : ℕ) (U : Config G n) : Prop where
  stock : Summable (fun j => t.tagged i j U)
  boost : Summable (fun j => Poly.send (t.marks i j) (X.bill (i,j):ℂ))
  receipts : Width.Covered (t.each i U) (X.merch i)

lemma adequate (hw : ∀ i, 0 < w i) (ha : 0 ≤ a) : Summable fun j : ℕ × ℕ => Poly.toll w (t.marks j.1 j.2)*X.bill j :=
  let h := Letters.Frame.from_hit B a E _ (fun j => (P.activities.forced j.1).inventory_ne.mono (P.activities.forced j.1).inventory_sup)
    (fun i : ℕ × ℕ => mul_nonneg (Poly.worth hw (t.marks i.1 i.2)).le (X.bill_pos i)) ha X.advert
  h.2.1

lemma rows (hw : ∀ i, 0<w i) (ha : 0 ≤ a) (i : ℕ) : Summable fun j => Poly.toll w (t.marks i j)*X.bill (i,j) :=
    (adequate (t:=t) (a:=a) X hw ha).comp_injective (f:=fun j => Poly.toll w (t.marks j.1 j.2)*X.bill j) (i:=Prod.mk i) (Prod.mk_right_injective _)

lemma cost_merch (hw : ∀ i, 0<w i) (ha : 0≤a) (i : ℕ) : Summable (fun j => Poly.send (t.marks i j) (X.bill (i,j):ℂ)) ∧
    Poly.price w (X.merch i) ≤ X.vac i + ∑' j,Poly.toll w (t.marks i j)*X.bill (i,j) := by
  have hi j : ‖((X.bill (i,j)):ℂ)‖=X.bill (i,j) := (Complex.norm_real _).trans (Real.norm_of_nonneg (X.bill_pos _))
  obtain ⟨hx,hX⟩ := Poly.budgeted hw (X.rows hw ha i) fun j => show Poly.price w (Poly.send (t.marks i j) (X.bill (i,j) : ℂ)) ≤ _ from by rw [Poly.solo,hi]
  exact ⟨hx, (Poly.addition hw ..).trans (add_le_add (by rw [Poly.solo,Poly.quiet_toll,one_mul,Complex.norm_real,Real.norm_of_nonneg (X.vac_pos _)]) hX)⟩

lemma qual (hw : ∀ i,0<w i) (ha : 0 ≤ a) (i : ℕ) (U : Config G n) : X.Qualitative i U := by
  obtain ⟨hx,_⟩ := X.cost_merch hw ha i
  have he := (Poly.budgeted hw (X.rows hw ha i) fun j => show Poly.price w (t.tagged i j U)≤ _ from by
    rw [Bands.tagged,Poly.solo]; exact mul_le_mul_of_nonneg_left (X.cover i j U) (Poly.worth hw _).le).1
  refine ⟨he,hx,fun s => ?_⟩
  have hf : Summable (fun j => (Poly.send (t.marks i j) (X.bill (i,j) : ℂ)).part s) := (hx.hasSum.map (Poly.get s) (Poly.part_cont s)).summable
  have hh : Summable (fun j => ((Poly.send (t.marks i j) (X.bill (i,j):ℂ)).part s).re) := (hf.hasSum.map Complex.reCLM Complex.continuous_re).summable
  have H (j) : ‖(t.tagged i j U).part s‖ ≤ ((Poly.send (t.marks i j) (X.bill (i,j):ℂ)).part s).re := by
    unfold Bands.tagged; simp only [Poly.part_send]; split
    · exact X.cover ..
    rw [norm_zero]; exact le_rfl
  have HS := hh.of_nonneg_of_le (fun j => norm_nonneg _) H
  simp only [Bands.each, merch, Poly.part_plus,Poly.share hx,Poly.share he, Complex.add_re,Complex.add_im]
  change ‖_‖ ≤ _ + Complex.reCLM (∑' j : ℕ,(Poly.send (t.marks i j) (X.bill (i,j):ℂ)).part s) ∧
    _ + Complex.imCLM (∑' j : ℕ,(Poly.send (t.marks i j) (X.bill (i,j):ℂ)).part s)=0
  rw [Complex.reCLM.map_tsum hf,Complex.imCLM.map_tsum hf]
  constructor
  · apply (norm_add_le ..).trans (add_le_add ?_ ((norm_tsum_le_tsum_norm HS).trans (HS.tsum_le_tsum H hh)))
    simp only [Poly.part_send]; split
    · simpa using X.vacant i U
    simp
  have him (z : R.Mode) (u : ℝ) : ((Poly.send z (u:ℂ)).part s).im=0 := by rw [Poly.part_send]; split <;> rfl
  change _ + ∑' j, ((Poly.send _ (X.bill (i,j):ℂ)).part s).im=_
  simp_rw [him,tsum_zero,zero_add]

lemma purchase (hw : ∀ i,0 < w i) (ha : 0 ≤ a) : Hit (fun i => (P.activities.forced i).support) B (fun i => Poly.price w (X.merch i)) a (k+E) := by
  intro x
  let f (j : ℕ × ℕ) := if x∈(P.activities.forced j.1).support then Poly.toll w (t.marks j.1 j.2)*X.bill j*Real.exp (a*coverNumber B (P.activities.forced j.1).support) else 0
  have h : SumBudget f E := X.advert x
  let g (i : ℕ) := ∑' j,f (i,j)
  have hg : SumBudget g E := ⟨fun i => tsum_nonneg fun j => h.1 _, ((summable_prod_of_nonneg h.1).mp h.2.1).2, h.2.1.tsum_prod ▸ h.2.2⟩
  let z (i : ℕ) := if x∈(P.activities.forced i).support then X.vac i * Real.exp (a*coverNumber B (P.activities.forced i).support) else 0
  refine Push.AbsoluteSums.budget_mono (Push.AbsoluteSums.budget_plus (show SumBudget z k from X.poles x) hg) (fun i => ?_) (fun i => ?_)
  · split
    · exact mul_nonneg (Poly.nonnegative hw _) (Real.exp_pos _).le
    exact le_rfl
  dsimp only [z,g,f]; split_ifs with h
  · have he := X.cost_merch hw ha i
    exact (mul_le_mul_of_nonneg_right he.2 (Real.exp_pos _).le).trans_eq (by simp_rw [tsum_mul_right,add_mul])
  simp_rw [tsum_zero,zero_add]
  exact le_rfl

include X in
lemma locality (hw : ∀ i, 0 < w i) (ha : 0 ≤ a) (H : t.Active) (hP : P.activities.ForcedFamily P.p) (i : ℕ) :
    Width.LocalCharge P.p t.origins (P.activities.forced i).support (t.each i) := by
  refine ⟨fun k U => ?_, ?_, fun U W ha he => ?_, fun U x he j hx => ?_⟩
  · unfold Bands.each; rw [hP.sym i k U]; unfold Bands.tagged; simp_rw [H.invi _ _ k U]
  · unfold Bands.each Bands.tagged; refine Measurable.add ((Bands.sends _).measurable.comp (Complex.continuous_ofReal.measurable.comp (hP.meas i))) (Measurable.tsum fun j => ?_)
    exact (Bands.sends _).measurable.comp (H.meas _ _)
  · unfold Bands.each Bands.tagged; rw [hP.reads i U W ha he]; simp_rw [H.inspects i _ U W ha he]
  by_contra hj
  apply he
  have hx' : x ≠ R.quiet := by rintro rfl; exact notMem_empty j hx
  rw [Bands.each,Poly.part_plus, Poly.part_send,if_neg hx', zero_add, Poly.share (X.qual hw ha _ _).stock]
  refine (tsum_congr (g:=fun _ => 0) (fun c => ?_)).trans tsum_zero
  by_cases hc : t.marks i c=x
  · unfold Bands.tagged; rw [hc,Poly.part_send,if_pos rfl]
    have hz : t.entries i c=0 := not_ne_iff.mp fun w => hj (H.retained i c w _ (hc.symm ▸ hx))
    exact congrFun hz U
  simp [Bands.tagged, Ne.symm hc]

lemma asserts (H : t.Active) (hp : P.activities.ForcedFamily P.p) (i : ℕ) (U : Config G n) (h : t.each i U≠0) : (P.activities.forced i).eligible P.p.threshold U := by
  by_contra hh
  apply h
  unfold Bands.each Bands.tagged
  have hi j : t.entries i j U=0 := not_ne_iff.mp fun H' => hh (H.keeps i j U H')
  simp_rw [hi,Poly.send_zero,tsum_zero,add_zero]
  rw [show P.activities.K i U=0 from not_ne_iff.mp (fun H' => hh (hp.permit i U H')),Complex.ofReal_zero,Poly.send_zero]

include X in
lemma silent (hw : ∀ i, 0 < w i) (ha : 0 ≤ a) (H : t.Active) (i : ℕ) (U : Config G n) :
    (t.each i U).part R.quiet=(P.activities.K i U:ℂ) := by
  rw [Bands.each,Poly.part_plus, Poly.part_send,if_pos rfl,Poly.share (X.qual hw ha i U).stock]
  have hi j : R.quiet ≠ t.marks i j := fun h => (H.occurs i j).ne_empty (congrArg Subtype.val h.symm)
  simp only [Bands.tagged,Poly.part_send,if_neg (hi _),tsum_zero,add_zero]

end Billboard
end YM.RG3.Forms
