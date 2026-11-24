import YM.Integration.FVA1Physical.Round2.SpatialFieldReserve
import YM.Integration.FVA1Physical.Round2.FormalFieldOrder
import YM.MSbar.Cypress.Vibe

/-! Absolute rooted derivative errors with the background chosen separately
for each word. The high-order interpolation and the final truncation use the
same assigned points and never interchange a supremum with a spatial sum. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Finset Lattice MSbar MSbar.Whisk MSbar.Lis MSbar.CrossH MSbar.Cacao
open MSbar.Bakery Push.Uniform
open scoped Classical Topology BigOperators ContDiff
variable {σ:Type} [Fintype σ] [DecidableEq σ] {n:Side}

def fieldCharge (loc:σ → Site n) (b:Site n) (a:ℝ) (s q:ℕ) (Z:List σ→Positions σ)
    (f:Positions σ→ℝ) : ℝ := Yarn q (fun l=>|buoy f (Z l) l| * spread loc {b} a s l)

def fieldDistance (loc:σ → Site n) (b:Site n) (a:ℝ) (s q:ℕ) (Z:List σ→Positions σ)
    (f h:Positions σ→ℝ) : ℝ := Yarn q (fun l=>|buoy f (Z l) l-buoy h (Z l) l| * spread loc {b} a s l)

theorem polynomial_charge (loc:σ → Site n) (b:Site n) {a H D:ℝ} (ha:0≤a) (hD:0≤D)
    (s d q:ℕ) (P:Pot σ) (cap:P.totalDegree ≤ d) (rows:Vault loc {b} a s d 0 P H)
    (Z:List σ→Positions σ) (inside:∀ l, ‖Z l‖≤D) :
    fieldCharge loc b a s q Z (clue P) ≤ H*(1+D)^(d+1) := by
  have phase:=field_independent_backgrounds loc {b} ha hD s d 0 P cap rows q
  have bill:=phase.2 Z (by intro l;simpa only [Metric.mem_closedBall,dist_zero_right] using inside l)
  apply le_trans (le_of_eq ?_) bill
  apply stitch
  intro l hl
  rw [value,←CrossH.budP (clue P) l q (Z l) (helm P q).contDiffAt hl.le,mul_comm]

omit [DecidableEq σ] in
theorem high_to_low_rooted (loc:σ → Site n) (b:Site n) {a ε D τ M B T:ℝ}
    (ha:0≤a) (hε:0≤ε) (hτ:0<τ) (s q:ℕ) (Z:List σ→Positions σ) (f h v:Positions σ→ℝ)
    (small:∀ l,l.length=q → |buoy f (Z l) l-buoy h (Z l) l|≤ε)
    (actual:fieldCharge loc b (((q:ℝ)+2)*a) (s+s) q Z f ≤ M)
    (formal:fieldCharge loc b (((q:ℝ)+2)*a) (s+s) q Z h ≤ B)
    (tail:fieldDistance loc b a s q Z h v ≤ T)
    (kernel:(∑ i,Real.exp (-a*separation b (loc i))) ≤ D) :
    fieldDistance loc b a s q Z f v ≤ τ*(M+B)+(ε/τ)*D^q+T := by
  let gap:=fun l=>|buoy f (Z l) l-buoy h (Z l) l|
  let A:=((q:ℝ)+2)*a
  have bank:Yarn q (fun l=>gap l*spread loc {b} A (s+s) l) ≤ M+B := by
    apply le_trans _ (add_le_add actual formal)
    unfold fieldCharge
    rw [←pockets]
    apply shiny
    intro l _
    rw [←add_mul]
    exact mul_le_mul_of_nonneg_right (abs_sub ..) (effect ..).le
  have step:=spatial_field_trade loc b ha hε hτ q s gap (fun l hl=>⟨abs_nonneg _,small l hl⟩) bank kernel
  apply le_trans _ (add_le_add step tail)
  unfold fieldDistance
  rw [←pockets]
  apply shiny
  intro l _
  rw [←add_mul]
  exact mul_le_mul_of_nonneg_right (abs_sub_le _ (buoy h (Z l) l) _) (effect ..).le

theorem polynomial_tail_charge (loc:σ → Site n) (b:Site n) {a H D:ℝ} (ha:0≤a) (hD:0≤D)
    (s d q:ℕ) (P Q:Pot σ) (cap:(P-Q).totalDegree ≤ d) (rows:Vault loc {b} a s d 0 (P-Q) H)
    (Z:List σ→Positions σ) (inside:∀ l,‖Z l‖≤D) :
    fieldDistance loc b a s q Z (clue P) (clue Q) ≤ H*(1+D)^(d+1) := by
  have bill:=polynomial_charge loc b ha hD s d q (P-Q) cap rows Z inside
  apply le_trans (le_of_eq ?_) bill
  apply stitch
  intro l hl
  have eqn:clue (P-Q)=clue P-clue Q:=funext fun z=>_root_.map_sub (MvPolynomial.eval z) P Q
  rw [eqn,Cypress.remove q l (Z l) (clue P) (clue Q) (helm P q).contDiffAt (helm Q q).contDiffAt hl.le]

end YM.Integration.FVA1Physical.Round2.Curvature
