import YM.MatchingLedger.Cooling

/-!
# Identity of the fund, including denominator, at the terminal coarsening

Do not divide by a reference (perturbative) or by the Haar-weight of a particular
orientation/tag. Do not remove supports nor change labels; use Selected as represented.
Use only genuine gauge-invariant insertions in this form of `portrait`. More generally,
`pack_top` need only be invariant at **interiors**, e.g., requests depending on the actual
forest gauge-fixed link coordinates.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Top
open Function Filter MeasureTheory Lattice RG Wilson Tree Pressure Pressure.Stores Precision
open PatchArea Push.SectorMeasure
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} (C : Family G) (k p : ℕ)

abbrev stepTor := C.path.levels.clock.op k p
def frost := Real.sqrt (C.beta (k+1) p)
-- retain exact Step push from this history; thermal weight foreground coefficient read.
local notation "S" => stepTor C k p
local notation "t" => frost C k p
local notation "β" => C.beta (k+1) p
local notation "H" => C.path.rep (k+1) p k
local notation "D" => C.path.rep (k+1) p (k+1)
variable (hm : C.Makes) (F : Forest (stepTor C k p).ratio) (V : Config G (C.side k p))
include hm
lemma frost_ok : 0<t := Real.sqrt_pos.mpr <| (lt_of_lt_of_le (a:=(0:ℝ))
  (half_pos (zero_lt_one.trans (C.path.levels.fits.delayed (k+1)))) (hm.wilson.represents (k+1) p (k+1) le_rfl).band.1)
lemma frost_beta : t^2=β := Real.sq_sqrt (Real.sqrt_pos.mp (frost_ok C k p hm)).le

-- observable real, e.g., real/imaginary words.
lemma pack_top {u : Config G (C.side (k+1) p)→ℝ} (hu : Envelope u)
    (hi : ∀ g : Site (C.side (k+1) p) → G.El, (∀ i, g ((S).ratio.embed i)=1) → ∀ U, u (Lattice.gauge g U)=u U) :
    (S).push (β) (fun U=> u U * (D).eval U) V = Action.cushion G S (t^2) *
       ∫ x, u (F.drape x) * Cooling.weight F V t x ∂F.order G := by
  have hx := hm.wilson.starts (k+1) p
  unfold StepData.push
  rw [F.pack,← integral_const_mul]; rotate_left
  · apply StepData.push_slice (C.path.levels.transition_mass ..)
    exact (hu.mul ((D).envelope (hm.wilson.represents (k+1) p (k+1) le_rfl).good)).integrable _
  · intro g h U; let w : Site (C.side k p)→ G.El := g∘ (S).ratio.embed; have hw:Lattice.gauge w V=V:= by funext i; simp [w,Lattice.gauge,h]
    dsimp only; rw [hi g h,(show (S).density (β) (Lattice.gauge g U) V = _ from hw ▸ (C.path.levels.blocks k p).gauge (β) U V g)] -- covariant exact
    rw [hx.2,bare_gauge]
  apply integral_congr_ae; filter_upwards with x
  unfold Cooling.weight; rw [frost_beta C k p hm]; change _ * _ = _
  rw [hx.2]; calc
    _ = u (F.drape x)* ((S).density β (F.drape x) V*bare β (F.drape x)):= by rw [mul_left_comm]
    _ = _:= by rw [Action.copper,mul_left_comm]

lemma denomination : (H).eval V = Action.cushion G S (t^2) * ∫ x, Cooling.weight F V t x ∂F.order G := by
  have h := pack_top C k p hm F V (Envelope.const 1) (fun _ _ _=>rfl)
  rw [(hm.wilson.steps (k+1) p k (Nat.lt_succ_self k)).1]; simp_rw [one_mul] at h; exact h

lemma portrait {u : Config G (C.side (k+1) p)→ℝ} (hu : Envelope u) (hi : GaugeInvariant u) :
    let w := Cooling.weight F V t
    Weight (F.order G) w ∧ 0 < (H).eval V ∧
      (S).push β (fun U=> u U*(D).eval U) V / (H).eval V = weigh (F.order G) w (u ∘ F.drape) := by
  intro w; have h : Weight (F.order G) w := Cooling.weight_pass F V t (C.path.levels.blocks k p).branches
  rw [pack_top C k p hm F V hu (fun i _ j=> hi i j), denomination C k p hm F V]
  have hp : 0 < Action.cushion G S (t^2) := Action.cushion_pos ..
  refine ⟨h,mul_pos hp h.nonempty,?_⟩
  simp_rw [mul_div_mul_left _ _ hp.ne']; rfl

end YM.MatchingLedger.Top
