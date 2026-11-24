import YM.Integration.WilsonReceivedFixedDigitHistory

/-! Cost of the independent cover history on a short, moving collar. Every step
uses the given child and the unaltered quiet at the same ultraviolet cutoff. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarShortHistory
open Function Finset Lattice RG Precision Wilson Exterior
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Mer
open WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil WilsonCoeffUV.Winding
open WilsonReceivedFixedDigitHistory
open scoped BigOperators Classical

variable {G:Gauge} {ι:Type} [Fintype ι] [DecidableEq ι] {D k:ι→ℕ} {e:ℕ}
variable (Q:Realm G (e+1) Credit.leanC)

/-- This price uses exactly one native `one_shore` per block. In particular it
retains each already formed marked component at all its incoming ranks. -/
theorem original (policy:Cloze D k Q Credit.leanC) (N:ℕ) (cell:Digits Q.draws ι)
    (Y:Outerm G D) (well:Wellness k Y) (A toll:ℝ) (hA:0≤A) (ht:1≤toll)
    (days m:ℕ) (hm:Q.anchor ≤ m) (cut:m+days≤N)
    (price:∀ j, m ≤ j → j < m+days → Q.cash (vigor G D k e Credit.leanC Credit.leanC) j ≤ toll)
    (incoming:Uniform Q Y (m+days) (by omega) A):
    Uniform Q (itinerary Q.draws Q.paid k N cell days m Y) m hm (toll^days*A):=by
  induction days generalizing m with
  | zero=>simpa [itinerary] using incoming
  | succ d ih=>
    let U:=itinerary Q.draws Q.paid k N cell d (m+1) Y
    have hw:Wellness k U:=sound Q.draws Q.paid k N cell Q.hG Q.green Y well d (m+1) (by omega)
    have mid:Uniform Q U (m+1) (by omega) (toll^d*A):=by
      apply ih (m+1) (by omega) (by omega) (fun j a h=>price j (by omega) (by omega))
      simpa only [Nat.add_assoc, Nat.add_comm 1 d] using incoming
    have ht0:=zero_le_one.trans ht
    have dose:0≤toll^d*A:=by positivity
    intro y S q hq r
    let x:=chartIn (loose Q.draws m) y (cell m)
    have hp:=one_shore policy (U x) (hw.level' x) (hw.quiet' x) m N hm (by omega)
      y (cell m) (S:=S) (A:=toll^d*A) (fun J _ o ho l=>mid x J o ho l) dose
    have h:=((hp S (by rfl) q hq r).shave (pureEl (Q.mint m hm).gear).le)
    apply h.more
    apply pow_le_pow_left₀ (mul_nonneg (zero_le_one.trans (Credit.purchase _ (Q.depth _ hm))) dose)
    rw [pow_succ]
    calc Q.cash (vigor G D k e Credit.leanC Credit.leanC) m * (toll^d*A)
          ≤ toll*(toll^d*A):=mul_le_mul_of_nonneg_right (price m le_rfl (by omega)) dose
      _ = toll^d*toll*A:=by ring

end YM.Integration.WilsonIndependentCollarShortHistory
end

