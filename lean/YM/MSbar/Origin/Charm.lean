import YM.MSbar.Origin.Coat
import YM.MSbar.Origin.Bose

/-!
# Field and ghost alphabets, vector fields in common degree

Check Lie-representations by `β`-array germs. In these formulas J finite is the
coordinate-index list for ghost fields; M for commuting field coordinates. Distinguish
nilpotent and Haar properties; the formulas work also in gauges that don't yet have a
measure test. The sums here always over all M or J; no constant-ghost exclusion in proving
any master identity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Origin
open Function Filter Topology Super
open scoped BigOperators ContDiff
variable {α β M J : Type*} {p : β→Bool}

structure Charm (M J β : Type*) (p : β → Bool) extends Canon (M ⊕ J) β p where
  even (a : M) : p (toCanon.leaf (.inl a)) = false
  odd (a : J) : p (toCanon.leaf (.inr a)) = true
namespace Charm
variable (K : Charm M J β p)
abbrev prime (a : M) := K.toCanon.leaf (.inl a)
abbrev shade (j : J) := K.toCanon.leaf (.inr j)
abbrev antiprime (a : M) := K.toCanon.anti (.inl a)
abbrev antishade (j : J) := K.toCanon.anti (.inr j)
lemma prime_hue (a : M) : p (K.prime a)=false := K.even a
lemma shade_hue (a : J) : p (K.shade a)=true := K.odd a
lemma aprime_hue (a : M) : p (K.antiprime a)=true := by rw [antiprime, K.toCanon.flips, K.even]; rfl
lemma ashade_hue (a : J) : p (K.antishade a)=false := by rw [antishade, K.toCanon.flips, K.odd]; rfl

abbrev House (M : Type*) := M→ℝ
variable [Fintype M] [DecidableEq M]
abbrev onePiece (a : M) : House M := Pi.single a 1

def view (x : β) : House M := Sum.elim (Sum.elim onePiece (fun _ => 0)) (fun _ => 0) (K.pair.symm x)
omit [Fintype M] in
@[simp] lemma view_prime (a : M) : K.view (K.prime a)=onePiece a := by simp [view,prime,Canon.leaf]
omit [Fintype M] in
@[simp] lemma view_shade (a : J) : K.view (K.shade a)=0 := by simp [view,shade,Canon.leaf]
omit [Fintype M] in
@[simp] lemma view_anti (a : M⊕J) : K.view (K.toCanon.anti a)=0 := by simp [view,Canon.anti]
omit [Fintype M] in
lemma view_odd (a : β) (h : p a=true) : K.view a=0 := by
  rcases K.toCanon.instances a with ⟨i|i,rfl⟩|⟨i,rfl⟩
  · rw [K.even] at h; cases h
  · exact K.view_shade i
  exact K.view_anti i

abbrev send (f : House M → ℝ) := bose K.view f
abbrev pick (Q : House M→House M) (i : M) := fun x => Q x i
lemma stand_send (f : House M→ℝ) : K.toCanon.Stand (K.send f) := fun a => bose_peel_vanish _ (K.view_anti a) f
lemma grade_send (f : House M→ℝ) : Grade p false (K.send f) := bose_grade _ f K.view_odd
lemma order_send {f : House M→ℝ} (h : Eager f 0) : Ordered p (K.send f) := bose_order _ f h K.view_odd
lemma peel_send (i : M) (f : House M → ℝ) : peel (K.prime i) (K.send f)=K.send (stunt f (onePiece i)) := by rw [send,bose_step,K.view_prime]
lemma shade_send (i : J) (f : House M → ℝ) : peel (K.shade i) (K.send f)=0 := bose_peel_vanish _ (K.view_shade i) f
omit [DecidableEq M] in
lemma pick_eager {Q : House M→House M} {x} (F : Eager Q x) (i : M) : Eager (pick Q i) x := (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : M => ℝ) i).contDiff.contDiffAt.comp x F

variable [DecidableEq β]
abbrev ghost (j : J) : Term β := Super.letter (K.shade j)
abbrev duplex (i j : J) := mix p (K.ghost i) (K.ghost j)
omit [Fintype M] [DecidableEq M] in
section
lemma grade_ghost (i : J) : Grade p true (K.ghost i) := by simpa [K.shade_hue] using (grade_letter (p:=p) (K.shade i))
lemma stand_ghost (i : J) : K.toCanon.Stand (K.ghost i) := Canon.Stand.letter _
lemma order_ghost (i : J) : Ordered p (K.ghost i) := ordered_letter _
lemma grade_duplex (i j : J) : Grade p false (K.duplex i j) := (K.grade_ghost i).mix (K.grade_ghost j)
lemma stand_duplex (i j : J) : K.toCanon.Stand (K.duplex i j) := (K.stand_ghost i).mix (K.stand_ghost j)
lemma order_duplex (i j : J) : Ordered p (K.duplex i j) := (K.order_ghost i).mix (K.order_ghost j) (K.grade_ghost i)
lemma duplex_swap (i j : J) : K.duplex i j= -K.duplex j i := by simpa only [duplex,twist_true,neg_smul,one_smul] using grade_mix_comm (K.grade_ghost i) (K.grade_ghost j)
lemma prime_ghost (i : M) (j : J) : peel (K.prime i) (K.ghost j)=0 := by rw [ghost,peel_letter, if_neg ((show K.prime i ≠ K.shade j from K.pair.injective.ne (by simp)))] -- if eq
lemma shade_ghost [DecidableEq J] (i j : J) : peel (K.shade i) (K.ghost j)= if i=j then scalar 1 else 0 := by rw [ghost,peel_letter]; by_cases e : i=j <;> simp [e,shade]
end
abbrev Canal (M J : Type*) := J→ House M→ House M
abbrev Beamish (J : Type*) := J → J→J→ℝ
variable [Fintype J]

def poses (V : Canal M J) (a : M) := ∑ j : J, mix p (K.ghost j) (K.send (pick (V j) a))
def trunk (D : Beamish J) (a : J) := -(1/2:ℂ) • ∑ i:J,∑ j:J,(D a i j:ℂ) • K.duplex i j

def lift (V : Canal M J) (D : Beamish J) : M ⊕ J → Term β := Sum.elim (K.poses V) (K.trunk D)

lemma grade_lift (V : Canal M J) (D : Beamish J) : ∀ i,Grade p (p (K.toCanon.anti i)) (K.lift V D i) := by
  rintro (a|a)
  · rw [show p (K.toCanon.anti (.inl a))=true from K.aprime_hue a]; exact Grade.sum fun i _ => (K.grade_ghost i).mix (K.grade_send _)
  rw [show p (K.toCanon.anti (.inr a))=false from K.ashade_hue a]; exact (Grade.sum fun i _ => Grade.sum fun j _ => (K.grade_duplex i j).smul _).smul _
lemma stand_lift (V : Canal M J) (D : Beamish J) : ∀ i,K.toCanon.Stand (K.lift V D i) := by
  rintro (a|a); exact Canon.Stand.sum fun i _ => (K.stand_ghost i).mix (K.stand_send _)
  exact (Canon.Stand.sum fun i _ => Canon.Stand.sum fun j _ => (K.stand_duplex i j).smul _).smul _
lemma order_lift {V : Canal M J} (H : ∀ j,Eager (V j) 0) (D : Beamish J) : ∀ i,Ordered p (K.lift V D i) := by
  rintro (a|a); exact Ordered.sum fun i _ => (K.order_ghost i).mix (K.order_send (pick_eager (H i) a)) (K.grade_ghost i)
  exact (Ordered.sum fun i _ => Ordered.sum fun j _ => (K.order_duplex i j).smul _).smul _

abbrev operate (V : Canal M J) (D : Beamish J) := K.toCanon.guide (K.lift V D)
end Charm
end YM.MSBar.Origin
