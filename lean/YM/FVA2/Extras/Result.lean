import YM.FVA2.Extras.Match
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Extras
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal O
open O.Lives MS.City MS.Rake O.Tune Flux Book Convolve O.Serve O.Pad Vane High Detect O.Ward
open MS.Local.Physical MS.Land Outlook Rough Emit
open scoped Topology ContDiff Interval BigOperators
open Job.Belt Rake.Geo O.Hue O.Fuse O.Cool
variable {G: Gauge}{A:Booked (Press.portDeck G)}{M: MS_Data G A} {d k h:ℕ}
variable {p q:T (Package ( Press.portDeck G ) d)}{X:T (localX G)}{a:ℝ}
/-! # Rigorous optional physical reduction

  in the supplied normalization after MS subtraction (parameter `a` denotes log ν convention of the **MS** mass
  unit, i.e. log ν as in that library, not the spacing in the Wilson regulator). For any additionally requested `comet` compatible with
  the **full dimensional** `Emit.Trill` closure and `Schema`, not assuming they
  are already physical combinations. This is **not comparing** evanescent
  slots separately a priori. Starting from these specifications, prove unique
  expansion supported in this exact Grade $h$ and identity on the standard choice. If at order zero
  of the extra mark its specialization in four dimensions vanishes, verify
  positivity of perturbative order of the reexpression for the `Mach.Ele` inputs as indicated (see also `empty_tune`
  in `Extras/Origin`)
  or more generally when specifying an analogous definite rank (see the `Goods` hypothesis) on the seed `U`.
  We don't compare other dimensional tensor definitions of evanescent not part of
  `YM.MS`, nor establish they do/don't actually satisfy `Schema`, nor in this file address
  the realization of exact directions via dimensional generators.
 -/
open MS.Dock MS.Motif Literal
structure Determined (h:ℕ)(U: T ( Arts.Mob G ))(M:MS_Data G A)(a:ℝ)(p:T (Package (Press.portDeck G) h)) (Y:Blue G) (Q:CostsM G) : Prop where -- rename
    okay : comet h 0 M.bulk ( gloss U ) Y Q
    equipped : Forth a M ( letIn h (logMass a) Y ) h
    usable (x:Unit→QP): Field ( Tide.frameF Unit a ) M ( x,letIn h (logMass a) Y ) 0
    involves : Says a M p ( letIn h (logMass a) Y )
    unique (q:T (Package (Press.portDeck G) h)) : Says a M q ( letIn h ( logMass a ) Y ) → q=p
    begins (r:ℕ)(hm:U 0 0=0) : Garment.Goods (r:ℤ) (U 0)→ p 0=0
variable {U:T (Arts.Mob G)}
lemma installs (hc:Trill (pulseX G) U)(hh:Schema false 0 d ( gloss U )) (Y Q) (hp:comet d 0 M.bulk (gloss U) Y Q) : ∃ p, Determined d U M a p Y Q := by
    obtain H:= appears (u:=a) hp hc; obtain ⟨p,hP,t⟩:= ambiguity (d:=d) H; exact ⟨ p,hp,H,fun _=> Estate H.2 H.1.1 _,hP,t,fun i hv hQ=> positive_entry H hP (Extras.clean_zero hp (hh 0) hQ hv a)⟩
theorem certified_reduction (hc:Trill (pulseX G) U)(hp:Schema false 0 d ( gloss U )): ∃ p Y Q, Determined d U M a p Y Q:= by obtain ⟨Y,Q,hQ⟩:= satisfyY M.bulkOK hp; obtain ⟨p,hP⟩:= installs ( a:=a ) hc hp Y Q hQ; exact ⟨p,Y,Q,hP⟩
theorem gallery (U:Box (Arts.Mob G))(p:Landau.Detect.Law G) (ht: Mach.Ele h k p U) : ∃ p Y Q, Determined h ( linear (Arts.Mob G) U ) M a p Y Q := by -- adjust
    apply certified_reduction ht.moodQ ht.grows
-- ensures no changing chosen preferred representatives.
theorem identity_rule (i:Plaid (Press.portDeck G) d) : let U:= soloV d (logMass a) M i; Says a M (Pi.single 0 ( ( Pi.single i 1 ): Package ( Press.portDeck G ) d )) U:= by
    intro U; let u:= ( Pi.single i 1 : Package (Press.portDeck G) d ); let p:= (Pi.single 0 u:T ( Package _ _ )); refine speaks (Y:=0) ?_ ⟨ Response.zero,Honest.zero ⟩; rw [map_zero, add_zero]; ext1 k; change U k=many a M p k; rw [ batch (le_refl k), Finset.sum_apply,Finset.sum_eq_single 0 ];
    · rw [ show p 0=u from Pi.single_eq_same .., choiceᵢ, Hue.hx_holder (Nat.zero_le k),Nat.sub_zero ]; simp only [Hue.seat, Complex.ofReal_one]; exact (one_smul ℂ ( U k ) ).symm
    · intro b hb he; rw [show p b=0 from Pi.single_eq_of_ne he .., choice₀, holdZ ]; rfl
    simp
end YM.FVA2.Extras
