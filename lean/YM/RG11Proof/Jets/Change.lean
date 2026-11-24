import YM.RG11Proof.Jets.Law
/-!
# Semidirect finite change action

If `c=(g,Z)`, the action on correlation coefficients is in every slot
`∑ A(g; w) ∏ Z v_s w_s`. Think `g = MS(t)` and `Z(t)` sends X-frame
row-vector labels into MS ones. The product `c ⊙ d` applies d-transform
first, then c-transform, to reports (so its parameter is d.g(c.g)).
No identification of the different independent schemes or actual report.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Jets
open PowerSeries YM.PertExtension.Position
open scoped BigOperators Classical

abbrev ArrayAt (J R : Type*) {P : Type*} (arity : P→ℕ) := Mark J arity → PowerSeries R

/-- The pair of formal coupling and field redefinitions; zero-constant and
leading/unit conditions imposed separately. -/
@[ext] structure Change (R J : Type*) where
  g : PowerSeries R
  Z : Square J (PowerSeries R)

namespace Change
variable {R J : Type*} [CommRing R] [Fintype J] (c d : Change R J)

def act {P : Type*} {shape : P→ℕ} (c : Change R J) (A : ArrayAt J R shape) : ArrayAt J R shape :=
  PertExtension.Position.insert J shape (fun v=> PowerSeries.subst c.g (A v)) (fun i j=> c.Z i j)

def compose : Change R J where
  g := PowerSeries.subst c.g d.g
  Z := c.Z * subs c.g d.Z

theorem act_act (h : Anchored c.g) (h' : Anchored d.g) {P : Type*} {a : P→ℕ}
    (A : ArrayAt J R a) :
    c.act (d.act A)=(compose c d).act A := by
  let Xsub : R⟦X⟧→+*R⟦X⟧ := (PowerSeries.substAlgHom (R:=R) h.permits).toRingHom
  have hf (p:R⟦X⟧): Xsub p=PowerSeries.subst c.g p := congr_fun (coe_substAlgHom h.permits) p
  have he (v) := PertExtension.Position.insert_alg Xsub (fun v:Mark J a=>PowerSeries.subst d.g (A v)) (fun i j=> d.Z i j) v
  simp_rw [hf,subst_comp_subst_apply (T:=R) h'.permits h.permits] at he
  unfold act; simp_rw [he];
  rw [PertExtension.Position.insert_twice]
  rfl

-- Compatibility in power horizon
structure EquivJet (n : ℕ) : Prop where
  ruler : Through n c.g d.g
  field : MatThrough n c.Z d.Z
namespace EquivJet
variable {c d} {e d' : Change R J} {n m : ℕ}
omit [Fintype J] in
protected theorem refl : EquivJet c c n := ⟨Through.refl _,MatThrough.refl _⟩
omit [Fintype J] in
protected theorem symm (h : EquivJet c d n) : EquivJet d c n := ⟨h.ruler.symm,h.field.symm⟩
omit [Fintype J] in
protected theorem trans (h : EquivJet c d n) (h' : EquivJet d e n) : EquivJet c e n :=
  ⟨h.ruler.trans h'.ruler, h.field.trans h'.field⟩
omit [Fintype J] in
protected theorem of_le (h : EquivJet c d n) (he : m≤n) : EquivJet c d m :=
  ⟨Through.of_le he h.ruler, MatThrough.of_le he h.field⟩
protected theorem act {P : Type*} {a : P→ℕ} {A B : ArrayAt J R a} {v : Mark J a}
    (h : EquivJet c d n) (he : Anchored c.g)
    (ha : ∀ w, Through n (A ⟨v.1,w⟩) (B ⟨v.1,w⟩)) : Through n (c.act A v) (d.act B v) :=
  Through.slots (fun _=> (ha _).compose h.ruler he) (fun _ _=>h.field _ _)
protected theorem compose (h : EquivJet c d n) (h' : EquivJet e d' n) (he : Anchored c.g) :
    EquivJet (compose c e) (compose d d') n :=
  ⟨h'.ruler.compose h.ruler he, h.field.mul (h'.field.subs h.ruler he)⟩
end EquivJet

variable [DecidableEq J] {c d}

/-- Admissible formal change; `nearId` including any constraints, not a
stability claim on actual sources. -/
structure Good (L : Constraints R J) (c : Change R J) : Prop where
  ruler : Coupling c.g
  field : L.Lawful c.Z

def one (R J : Type*) [CommRing R] [DecidableEq J] : Change R J := ⟨X,1⟩

theorem act_one {P : Type*} {a : P→ℕ} (A : ArrayAt J R a) : (one R J).act A=A := by
  ext1 v
  unfold act one
  simp only [X_subst,Matrix.one_apply]
  -- normalize the Classical decidability
  convert! insert_one A v

private theorem idGood (L : Constraints R J) : Good L (one R J) :=
  ⟨⟨Anchored.variableX, by simp [one,tangent]⟩, Constraints.Lawful.id⟩

namespace Good
variable {L : Constraints R J}
theorem id (L : Constraints R J) : Good L (one R J) := idGood L
protected theorem compose (h : Good L c) (hd : Good L d) : Good L (compose c d) :=
  ⟨hd.ruler.compose h.ruler, h.field.mul (hd.field.subs h.ruler.base)⟩
end Good

def undo {L : Constraints R J} (c : Change R J) (h : Good L c) : Change R J where
  g := reverse c.g h.ruler
  Z := squareInv (subs (reverse c.g h.ruler) c.Z)

namespace Good
variable {L : Constraints R J}
protected theorem undoes (c : Change R J) (h : Good L c) : Good L (undo c h) :=
  ⟨reverse_good _ h.ruler, (h.field.subs (reverse_good _ h.ruler).base).squareInv⟩
end Good

variable {L : Constraints R J}

@[simp] theorem compose_undo_left (c : Change R J) (h : Good L c) : compose (undo c h) c = one R J :=
  Change.ext (compose_reverse_apply c.g h.ruler) (squareInv_mul (h.field.baseline.subs (reverse_good _ h.ruler).base))

@[simp] theorem compose_undo_right (c : Change R J) (h : Good L c) : compose c (undo c h) = one R J := by
  refine Change.ext (reverse_compose_apply c.g h.ruler) ?_
  change _ * subs c.g (squareInv (subs _ c.Z)) = 1
  let p := reverse c.g h.ruler
  let D := subs p c.Z
  have H : subs c.g (D*squareInv D)=(1:Square J R⟦X⟧) := by
    rw [mul_squareInv (nearId.subs (reverse_good _ h.ruler).base h.field.baseline),subs_one h.ruler.base]
  rw [subs_mul h.ruler.base,show D=subs p c.Z from rfl,subs_subs _ (reverse_good _ h.ruler).base h.ruler.base, reverse_compose_apply,subs_X] at H
  exact H

@[simp] theorem undo_action_left {P : Type*} {a : P→ℕ} (c : Change R J) (h : Good L c)
    (A : ArrayAt J R a) : (undo c h).act (c.act A)=A := by
  rw [act_act _ _ (Good.undoes ..).ruler.base h.ruler.base,
     compose_undo_left, act_one]

@[simp] theorem undo_action_right {P : Type*} {a : P→ℕ} (c : Change R J) (h : Good L c)
    (A : ArrayAt J R a) : c.act ((undo c h).act A)=A := by
  rw [act_act _ _ h.ruler.base (Good.undoes ..).ruler.base, compose_undo_right, act_one]

theorem match_reverse {P : Type*} {a : P→ℕ} {n} {A B : ArrayAt J R a} (c : Change R J) (h : Good L c)
    (hb : ∀ v, Through n (c.act A v) (B v)) (v) : Through n (A v) ((undo c h).act B v) := by
  let V := undo c h
  have H := (EquivJet.refl (n:=n) (c:=V)).act (v:=v) (Good.undoes c h).ruler.base (A:=c.act A) (fun w => hb ⟨v.1,w⟩)
  rwa [undo_action_left] at H

theorem undo_equiv {L' : Constraints R J} {n} (c d : Change R J) (h : Good L c) (hd : Good L' d) (e : EquivJet c d n) :
    EquivJet (undo c h) (undo d hd) n := by
  have hr := e.ruler.reverse h.ruler hd.ruler
  exact ⟨hr, (e.field.subs hr (reverse_good _ h.ruler).base).squareInv (h.field.baseline.subs (reverse_good ..).base) (hd.field.baseline.subs (reverse_good ..).base)⟩
end Change
end YM.RG11.Jets
