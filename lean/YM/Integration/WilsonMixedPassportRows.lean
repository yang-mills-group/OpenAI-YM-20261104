import YM.QuadraticLocal.Fk.Offer

/-! Routing disjoint marked faces keeps the original roots, walks and supports on each face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMixedPassportRows

open Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn Push Push.AbsoluteSums
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {V α β : Type} [DecidableEq V] {C : Census V}

def passport (p : V → Passport n V) : Passport n V where
  origin v := (p v).origin v
  support v := (p v).support v
  wire v := (p v).wire v
  height v := (p v).height v
  born v := (p v).born v
  visits v := (p v).visits v
  room v := (p v).room v

variable {P : Passport n V} (p : V → Passport n V)
  (a : Row P C G α) (home : ∀ v ∈ a.mode.val, p v = P) (test : β → α)

def place : Row (passport p) C G β where
  binder := {
    mode := a.mode, front := a.binder.front, east := a.binder.east, path := a.binder.path
    span := by
      intro v hv
      change stop ((p a.binder.front).origin a.binder.front) _ = (p v).origin v
      rw [home _ a.binder.east, home _ hv]
      exact a.binder.span v hv
    extra := a.binder.extra }
  lamp := a.lamp
  atom := a.atom
  lawful := a.lawful
  clear := a.clear
  salary := a.salary
  sound := a.sound
  paint := a.paint ∘ test
  rank := a.rank

private theorem centered : (place p a home test).center = a.center := by
  change (p a.binder.front).origin a.binder.front = P.origin a.binder.front
  rw [home _ a.binder.east]

private theorem lengths : (place p a home test).length = a.length := by
  unfold Row.length Binder.length
  congr 2
  apply Finset.sum_congr rfl
  intro v hv
  change _ + (p v).height v = _ + P.height v
  rw [home v hv]
  rfl

theorem original (B : BudgetPoint) (g : ℝ) (x : β) :
    (place p a home test).center = a.center ∧ (place p a home test).length = a.length ∧
    (place p a home test).ground B = a.ground B ∧
    (place p a home test).nominal g x = a.nominal g (test x) := by
  have hc := centered p a home test
  have hl := lengths p a home test
  have leg (v : V) (hv : v ∈ a.mode.val) : (place p a home test).binder.leg v = a.binder.leg v := by
    change Paths.native (place p a home test).center (a.binder.path v ++ (p v).wire v) = _
    rw [hc, home v hv]
    rfl
  have hg : (place p a home test).binder.ground a.atom = a.binder.ground a.atom := by
    unfold Binder.ground
    change a.atom.footprint (place p a home test).center ∪ _ = _
    rw [hc]
    congr 1
    exact Finset.biUnion_congr rfl leg
  refine ⟨hc, hl, ?_, ?_⟩
  · unfold Row.ground Row.region
    rw [hl, hc]
    split <;> first | rfl | exact hg
  · unfold Row.nominal Row.grain
    rw [hc]
    rfl

variable {P Q : Passport n V} {γ ι κ : Type}
  (M : ι → Row P C G α) (Y : κ → Row Q C G γ)

abbrev Face (xs : Finset V) := {i : ι // (M i).mode.val ⊆ xs}

def owner (P Q : Passport n V) (old : Finset V) (v : V) : Passport n V :=
  if v ∈ old then P else Q

def joined (old fresh : Finset V) (separated : Disjoint old fresh) :
    Sum (Face M old) (Face Y fresh) → Row (passport (owner P Q old)) C G (α × γ)
  | .inl v => place (owner P Q old) (M v.val)
      (fun _ hv => if_pos (v.property hv)) Prod.fst
  | .inr v => place (owner P Q old) (Y v.val)
      (fun _ hv => if_neg (fun hv' => Finset.disjoint_left.mp separated hv' (v.property hv))) Prod.snd

end YM.Integration.WilsonMixedPassportRows
