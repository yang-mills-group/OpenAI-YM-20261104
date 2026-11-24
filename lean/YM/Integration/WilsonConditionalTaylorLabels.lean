import YM.RGComparison.Core16.Spool.Beacon
import YM.Next.FOUNDATIONS.Primary
import Mathlib.Logic.Encodable.Basic

/-! A countable catalogue of all finite lists (including repetition) of the
original Wilson sections, with independent actual torus placements at readout. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorLabels

open Lattice Wilson Labels Next.Foundations RGComparison.Core16.Spool
open scoped Classical BigOperators
variable {G : Gauge}

abbrev Atom (G : Gauge) := Σ h : ℕ, ((frames G).level h).Index
abbrev Roster (G : Gauge) := List (Atom G)
abbrev Entry (G : Gauge) := Σ a : Roster G, Finset (Fin a.length)

def decoded (G : Gauge) (n : ℕ) : Roster G := (Encodable.decode (α:=Roster G) n).getD []

theorem recover (a : Roster G) : decoded G (Encodable.encode a) = a := by simp [decoded]

def entry (G : Gauge) (n : ℕ) : Entry G := (Encodable.decode (α:=Entry G) n).getD ⟨[],∅⟩

theorem recover_entry (a : Entry G) : entry G (Encodable.encode a) = a := by simp [entry]

def lamps (a : Roster G) (i : Fin a.length) : Lamp G :=
  investment (sound G (a.get i).1) (valuation G (a.get i).1) (a.get i).2

def packet (a : Entry G) (i : ↥a.2) : Lamp G := lamps a.1 i.val

theorem grade (a : Roster G) (i : Fin a.length) : (lamps a i).order =
    (((frames G).level (a.get i).1).grades (a.get i).2).2 := rfl

/-- Every occupied subset is the ordinary product of independent translated
original basis insertions, evaluated on the very same link configuration. -/
theorem marked {n : Side} (a : Roster G) (s : Finset (Fin a.length))
    (o : (i : ↥s) → Site n) (U : Config G n) :
    tally (fun i : ↥s => lamps a i.val) o U =
      ∏ i : ↥s, (localSection G (a.get i.val).1).evaluate (Pi.single (a.get i.val).2 1) (expandAt (o i) U) := rfl

theorem vacuum {n : Side} (a : Roster G) (U : Config G n) :
    tally (fun i : ↥(∅ : Finset (Fin a.length)) => lamps a i.val) (fun _ => (0 : Site n)) U = 1 := by
  simp [tally]

theorem components {n : Side} (a : Roster G) (s : Finset (Fin a.length))
    (o : (i : ↥s) → Site n) (U : Config G n) :
    let z := tally (fun i : ↥s => lamps a i.val) o U
    (look false z : ℂ) + (look true z : ℂ)*Complex.I = z := by
  intro z
  change (z.re : ℂ) + (z.im : ℂ)*Complex.I = z
  exact Complex.re_add_im z

end YM.Integration.WilsonConditionalTaylorLabels
end

