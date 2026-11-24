import YM.RG3.Press.Voucher
import YM.Overlay.Pays

/-!
# Full density readout with caption extension

At the level of ACTUAL functions (no analytic expansion here). Use
caption when analytic output includes *field-independent* connected
rank-zero choices on ≥1 slots. A caption is still attached to a
nonempty spatial receipt and all of its mark origins, even though never
masked in evaluation. Keep any connector/test/history information inside
these support receipts too when consuming later. Stand-alone unit fire
constants (one marker, without length) already have a cheaper channel in
Bands and need no caption. Does not claim that quotienting out a constant
term from a mask is free (charge through Slip or directly keep it masked
as H). Leaving all other channels T on an actual Rep, not a normalization.
`book.Active` = structural sin, `book.Budget w` full existential price
at arbitrary fixed radii. Use separately uniform version for passive held
test data families. No direct bound on frame transforms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Forms
open Marker Finset RG Lattice Wilson Overlay Press Function Extra.Trajectories Push.Corrected
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {V : Type*} [DecidableEq V] (R : Census V) {n : Side} {G : Gauge} (v : V → Site n) (P : Rep G n)

structure Captions (R : Census V) (n : Side) where
  tag : ℕ → R.Mode
  cover : ℕ → Support n
  value : ℕ → ℂ

namespace Captions
variable {R} (j : Captions R n)

structure Paid (w : V → ℝ) (p : BudgetPoint) (a : ℝ) : Prop where
  budget i : SumBudget (fun s => if i∈ (j.tag s).val then Poly.toll w (j.tag s) * p.mass (j.cover s) ‖j.value s‖ else 0) a

structure Sound : Prop where
  card i : (j.tag i).val.Nonempty
  pins i : ∀ s∈(j.tag i).val,v s ∈ j.cover i

def chord : Poly R := ∑' i, Poly.send (j.tag i) (j.value i)

variable {v} [Fintype V]
lemma chords (h : j.Sound v) {w p a} (hp : j.Paid w p a) (hw : ∀ i,0 < w i) :
    Summable (fun i => Poly.send (j.tag i) (j.value i)) ∧ Poly.price w j.chord ≤ Fintype.card V * a := by
  let f s := Poly.toll w (j.tag s) * p.mass (j.cover s) ‖j.value s‖
  have he := per_system (f:=f) (fun s => mul_nonneg (Poly.worth hw _).le ((norm_nonneg _).trans (p.loMass _ _ (norm_nonneg _)))) h.card hp.budget
  have hy i : Poly.price w (Poly.send (j.tag i) (j.value i)) ≤ f i := by rw [Poly.solo]; exact mul_le_mul_of_nonneg_left (p.loMass _ _ (norm_nonneg _)) (Poly.worth hw _).le
  obtain ⟨H,h'⟩ := Poly.budgeted hw he.2.1 hy
  exact ⟨H,h'.trans he.2.2⟩
lemma quiet (h : j.Sound v) {w p a} (hp : j.Paid w p a) (hw : ∀ i,0 < w i) :
    j.chord.part R.quiet=0 := by
  rw [chord,Poly.share (j.chords h hp hw).1]
  have ht i (z : ℂ) : (Poly.send (j.tag i) z).part R.quiet=0 := by
    rw [Poly.part_send]; exact if_neg fun ht => (h.card i).ne_empty (congrArg Subtype.val ht.symm)
  simp_rw [ht]; exact tsum_zero
end Captions

section Extend
variable {R}

structure Deck (R : Census V) (P : Rep G n) where
  contents : Bands R P
  captions : Captions R n

namespace Deck
variable {P v} (d : Deck R P)

structure Active : Prop where
  articles : d.contents.Active
  captions : d.captions.Sound d.contents.origins

structure Budget (w : V → ℝ) (u c d' b a : ℝ) : Prop where
  radial : d.contents.Radial w u c d' b
  captions : d.captions.Paid w P.p a

variable [Fintype V]

def log (U : Config G n) := d.contents.extra U + d.captions.chord

def density (U : Config G n) : Poly R := (Real.exp (P.exponent U) : ℂ) • (Poly.pass (d.log U)*d.contents.cluster U)

lemma companion (D : d.Active) {w u c d' b a} (hb : d.Budget w u c d' b a) (U : Config G n) : (d.contents.extra U).part R.quiet=0 := by
  rw [Bands.extra,Poly.part_plus,Poly.part_sum,Poly.share (d.contents.bulkBound D.articles hb.radial U).1]
  have hi i (z:ℂ) : (Poly.send (d.contents.rays i) z).part R.quiet=0 := by
    rw [Poly.part_send]; exact if_neg fun h => (D.articles.proper i).ne_empty (congrArg Subtype.val h.symm)
  simp_rw [Poly.part_send,if_neg (R.fire_hot _).symm,Bands.ray,hi] -- rewrite order
  simp

lemma quiet (D : d.Active) {w u c d' b a} (hb : d.Budget w u c d' b a) (U : Config G n) : (d.log U).part R.quiet=0 := by
  rw [log,Poly.part_plus,d.companion D hb U,d.captions.quiet D.captions hb.captions hb.radial.pure,zero_add]

lemma attach (D : d.Active) {w u c d' b a} (hb : d.Budget w u c d' b a) (U : Config G n) : d.density U=d.contents.density U*Poly.pass d.captions.chord := by
  unfold density Bands.density log
  rw [pass_add (d.companion D hb _) (d.captions.quiet D.captions hb.captions hb.radial.pure)]
  simp [mul_assoc,mul_comm]

lemma vacuum (D : d.Active) {w u c d' b a δ k} (hb : d.Budget w u c d' b a) (hP : P.activities.Valid P.p δ k) (U : Config G n) : (d.density U).part R.quiet=(P.eval U:ℂ) := by
  rw [d.attach D hb U,Poly.quiet_mul,d.contents.same D.articles hb.radial hP U,Poly.pass_part _ (d.captions.quiet D.captions hb.captions hb.radial.pure),mul_one]

lemma log_cost (D : d.Active) {w u c d' b a} (hb : d.Budget w u c d' b a) (U : Config G n) :
    Poly.price w (d.log U) ≤ Fintype.card V * (u+c+a) := by
  unfold log
  exact (Poly.addition hb.radial.pure ..).trans ((add_le_add (d.contents.bulkBound D.articles hb.radial U).2 (d.captions.chords D.captions hb.captions hb.radial.pure).2).trans (by simp [mul_add]))

lemma density_cost (D : d.Active) {w u c d' b a δ k} (hb : d.Budget w u c d' b a) (H : P.activities.Valid P.p δ k) (U : Config G n) :
    Poly.price w (d.density U) ≤ Real.exp (P.exponent U + Fintype.card V*(u+c+a+d'*b) + Fintype.card (Site n)*k) := by
  have hw := hb.radial.pure
  rw [density,Poly.adapted, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have he : Poly.price w (Poly.pass (d.log U)) ≤ Real.exp (Fintype.card V*(u+c+a)) :=
    (Poly.pass_budget hw _).trans (Real.exp_monotone (d.log_cost D hb _))
  refine (mul_le_mul_of_nonneg_left ((Poly.multiplication hw ..).trans (mul_le_mul he (d.contents.population D.articles hb.radial H U).2 (Poly.nonnegative hw _) (Real.exp_pos _).le)) (Real.exp_pos _).le).trans_eq ?_
  rw [←Real.exp_add,←Real.exp_add]; congr 1; ring

lemma density_read (D : d.Active) {σ C Λ δ k} (HB : P.Lawful σ C Λ δ k) : Measurable d.density := by
  refine Measurable.smul (Complex.continuous_ofReal.measurable.comp (P.exponentEnv HB).exp.meas) ?_
  have he := Poly.pass_cont.measurable.comp ((d.contents.extra_meas D.articles).add (measurable_const (a:=d.captions.chord)))
  exact he.mul (d.contents.cluster_meas D.articles HB.labels)

-- not a bound surviving sharp comparison; for integrability etc at fixed n
lemma envelope (D : d.Active) {w u c d' b a} (hb : d.Budget w u c d' b a) {σ C Λ δ k} (HB : P.Lawful σ C Λ δ k) : Envelope d.density := by
  let E := P.exponentEnv HB
  obtain ⟨r,hr⟩ := E.cost
  obtain ⟨s,hs,he⟩ := Poly.equivalent_norm (R:=R) hb.radial.pure
  refine ⟨d.density_read D HB,Real.exp (r+Fintype.card V*(u+c+a+d'*b)+Fintype.card (Site n)*k)*s,fun U => ?_⟩
  exact (he _).trans (mul_le_mul_of_nonneg_right ((d.density_cost D hb HB.labels _).trans (Real.exp_monotone (by have hu := (le_abs_self (P.exponent U)).trans (show _ from hr U); linarith))) hs)
end Deck

-- Adapter for *unextended* target.
variable [Nonempty V] (T : Bands R P)

def emptyCaptions (n : Side) (R : Census V) : Captions R n :=
  ⟨fun _ => R.fire (Classical.arbitrary _), fun _ => univ, 0⟩

def binding : Deck R P := ⟨T,emptyCaptions n R⟩

lemma plain_sound (h : T.Active) : (binding P T).Active := by
  refine ⟨h, fun _ => singleton_nonempty _, fun _ _ _ => mem_univ _⟩
lemma plain_cost {w u c d b} (h : T.Radial w u c d b) : (binding P T).Budget w u c d b 0 := by
  refine ⟨h,⟨fun i => ?_⟩⟩
  simp only [binding,emptyCaptions,Pi.zero_apply,norm_zero,BudgetPoint.mass,mul_zero,ite_self]
  exact ⟨fun _ => le_rfl,summable_zero,tsum_zero.le⟩
lemma plain_density [Fintype V] : (binding P T).density=T.density := by
  funext U
  unfold Deck.density Bands.density
  simp [binding,emptyCaptions,Deck.log,Captions.chord]
end Extend
end YM.RG3.Forms
