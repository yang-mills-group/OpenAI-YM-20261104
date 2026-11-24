import YM.Integration.FVA1Physical.Wilson.FirstMarkedTicket

/-! Continue a complete vacuum and marked polynomial bank along any further
finite full-period descent with its supplied clocks, forests and tag history. -/
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Lattice RG YM.Wilson Tree Precision Marker FVA2.CityHistory
open FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Splice FormalOPE.RG10.OpenSlots
open FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router RGComparison.Core16
open scoped Classical

namespace Continuation
variable {n f : Side} (d : Descent n f)

def extended : {c : Side} → Descent f c → Descent n c
  | _, .nil => d
  | _, .push S F prior => .push S F (extended prior)

def tags (t : d.Tags) : {c : Side} → (p : Descent f c) → p.Tags → (extended d p).Tags
  | _, .nil, _ => t
  | _, .push _ _ prior, q => (q.1,tags t prior q.2)

theorem room {G : Gauge} (H : d.Room G) : {c : Side} → (p : Descent f c) → p.Room G → (extended d p).Room G
  | _, .nil, _ => H
  | _, .push _ _ prior, w => ⟨w.1,room H prior w.2⟩

variable {G : Gauge} (Z : ChartRatio G) (t : d.Tags) (H : d.Room G)
    (vac src : Ticket (Pins G f))

/-- Integrate the same complete inherited vacuum with and without the
insertion and divide by the resulting denominator at each successive step. -/
def readings : {c : Side} → (p : Descent f c) → p.Tags → p.Room G →
    (ℕ → PowerSeries ℝ) → Ticket (Pins G c) × Ticket (Pins G c)
  | _, .nil, _, _, _ => (vac,src)
  | _, .push S F prior, q, w, z =>
    let b := q.1
    let earlier := readings prior q.2 w.2 (parentZ z)
    let D := extended d prior
    let τ := tags d t prior q.2
    let hD := room d H prior w.2
    let Q := gateQ S F b (retained D τ hD)
    let hQ := useful S F D τ b w.1 hD
    let u := Quadratic.uptake Q (PertExtension.Chart.tangent G F.Free) hQ
    let W := fire S F b earlier.1 Z (z 1)
    (u W,u (W * boost (gate G S F) earlier.2) * Return (u W))

/-- Fubini and the full field-dependent division identify both outputs
with the simultaneous full-history integral. The seed is read on the same
clock as the initial segment. -/
theorem readings_eq (hZ : LocalRatio Z) {c : Side} (p : Descent f c) (q : p.Tags) (w : p.Room G)
    (z : ℕ → PowerSeries ℝ) (A : Ticket (Pins G n))
    (wV : vac = μLedger d Z t H (fun i => z (i+p.depth)))
    (wA : src = skyread Z d t H (fun i => z (i+p.depth)) A) :
    readings d Z t H vac src p q w z =
      (μLedger (extended d p) Z (tags d t p q) (room d H p w) z,
       skyread Z (extended d p) (tags d t p q) (room d H p w) z A) := by
  induction p generalizing z with
  | nil => exact Prod.ext wV wA
  | push S F prior ih =>
    obtain ⟨b,q⟩ := q
    have shift : (fun i => parentZ z (i+prior.depth)) =
        (fun i => z (i+(Descent.push S F prior).depth)) := by
      funext i
      change z ((i+prior.depth)+1) = z (i+(prior.depth+1))
      rw [Nat.add_assoc]
    have prev := ih q w.2 (parentZ z) (by rw [shift]; exact wV) (by rw [shift]; exact wA)
    dsimp only [readings,extended,tags,room]
    rw [prev,judgment S F (extended d prior) (tags d t prior q) b Z z w.1 (room d H prior w.2),
      atop S F (extended d prior) (tags d t prior q) b Z z hZ w.1 (room d H prior w.2)]
    rfl

end Continuation
end YM.Integration.FVA1Physical.Wilson
