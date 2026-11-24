import YM.Integration.FVA1Physical.Round2.CalibratedJetShells

/-! Buy one extra order on a single calibrated family and then truncate its
formal polynomial at the requested order. The removed coefficient has an
independent weighted price on a full ball, including all held directions. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Lattice Push Push.Uniform MSbar MSbar.Lis MSbar.Whisk MSbar.CrossH
open Filter RG Wilson Precision MSbar.Midpoint PhysicalNext.Repeat.Legato
open scoped BigOperators Classical Topology
variable {G : Gauge} {n : Side}

def regularRow {σ : Type} [Fintype σ] (site : σ → Site n) (a : ℝ) (s q : ℕ)
    (F : Positions σ → ℝ) (x : Positions σ) (i : σ) : ℝ :=
  Yarn q (fun l => |buoy F x (i::l)| * Measuring.swipe site a s (i::l))

theorem regularRow_add_scaled {σ : Type} [Fintype σ] (site : σ → Site n)
    (a : ℝ) (s q k : ℕ) (F H : Positions σ → ℝ) (x : Positions σ) (i : σ)
    (c : ℝ) (hk : q+1 ≤ k) (hf : ContDiffAt ℝ k F x) (hh : ContDiffAt ℝ k H x) :
    regularRow site a s q (F + fun z => c * H z) x i ≤
      regularRow site a s q F x i + |c| * regularRow site a s q H x i := by
  unfold regularRow
  rw [← sheen, ← pockets]
  apply shiny
  intro l hl
  let t := (i::l).map bolt
  have ht : t.length ≤ k := by simpa [t,hl] using hk
  have eqn : buoy (F+fun z => c*H z) x (i::l) = buoy F x (i::l) + c*buoy H x (i::l) := by
    change roc (F+fun z => c*H z) t x = roc F t x+c*roc H t x
    rw [addedL k t _ _ hf (contDiffAt_const.mul hh) ht,wed k t c H hh ht]
  rw [eqn]
  calc
    _ ≤ (|buoy F x (i::l)| + |c*buoy H x (i::l)|)*Measuring.swipe site a s (i::l) :=
      mul_le_mul_of_nonneg_right (abs_add_le ..) (effect site _ s ∅ _).le
    _ = _ := by rw [abs_mul]; ring

/-- Exact truncation on one scene, including its degree-zero component. -/
theorem film_truncate (Q : Rep G n) (A : Rolling.Nesting G n) (g : ℝ) (p : ℕ) :
    Aqua.film Q A g p =
      Aqua.film Q A g (p+1) + fun x => g^(p+1)*clue (PowerSeries.coeff (p+1) A) x := by
  funext x
  change Aqua.vine Q g x - Aqua.ore Q A g p x =
    Aqua.vine Q g x - Aqua.ore Q A g (p+1) x + g^(p+1)*_
  unfold Aqua.ore
  rw [Finset.sum_range_succ (n:=p+1)]
  change _ = _ - ((∑ j ∈ Finset.range (p+1),g^j * atlas A p j Q.path Q.clip x) +
    g^(p+1) * atlas A (p+1) (p+1) Q.path Q.clip x) + _
  rw [← Parma.pose A Q.path Q.clip (Nat.succ_pos p)]
  unfold Parma.teethT
  ring

/-- The first omitted term is paid at its full coupling power in a
complete anchored regular row. The cost is uniform over the finite torus. -/
theorem film_row_truncate (Q : Rep G n) (A : Rolling.Nesting G n) {g a b w h B Z : ℝ} {s m q p : ℕ}
    (x : Positions (Primary n G)) (i : Primary n G) (hg : 0 ≤ g)
    (ha : 0 ≤ a) (hab : a ≤ b) (hw : 0 < w) (hh : 1 ≤ h) (hq : q+1 ≤ m)
    (hx : x ∈ Metric.closedBall 0 w)
    (J : JetTab (Measuring.chart n G) a s w (Metric.closedBall 0 w) (Aqua.film Q A g (p+1)) q B)
    (sm : ContDiffAt ℝ m (Aqua.film Q A g (p+1)) x)
    (H : Tin (Measuring.chart n G) b s (p+2) h (PowerSeries.coeff (p+1) A) Z)
    (deg : (PowerSeries.coeff (p+1) A).totalDegree ≤ (p+2)+1) :
    regularRow (Measuring.chart n G) a s q (Aqua.film Q A g p) x i ≤
      B/w^(q+1) + g^(p+1)*(Z*(1+w)^((p+2)+1)) := by
  let P := PowerSeries.coeff (p+1) A
  have tok := (Tin.weightTok (zero_lt_one.trans_le hh) hh H).soft hab ha
  have B₂ := Ruby.costF x ha tok deg q (mem_closedBall_zero_iff.mp hx) i
  rw [film_truncate Q A g p]
  refine (regularRow_add_scaled _ a s q m _ (clue P) x i _ hq sm (helm P _).contDiffAt).trans ?_
  rw [abs_of_nonneg (pow_nonneg hg _)]
  exact add_le_add (J.count hw x hx i) (mul_le_mul_of_nonneg_left B₂ (pow_nonneg hg _))

end YM.Integration.FVA1Physical.Round2
