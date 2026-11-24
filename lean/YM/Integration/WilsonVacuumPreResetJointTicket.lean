import YM.Integration.WilsonVacuumPreResetJointRaw

/-! A single signed original bank, including its full sum over fine paths,
is tested on the joint chart. The age-dependent multiplier is kept outside
the derivatives, and the total Taylor remainder is paid on the same branch. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetJointTicket
open Stationary Function Filter Lattice RG Wilson Tree Pressure Gauge Precision Push Push.Uniform Push.AbsoluteSums
open ConnectedActivityE6 Coat Control Blaze
open AnalyticNext.QuarticMatch.Estimate RG01.Sounder Logfee Work.G05
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetJointField WilsonVacuumPreResetJointRaw
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

private theorem increment_link (U : Config G f) (j : ℕ) (u : Directions G f) (i : Bond f) :
    Allows j (fun x => G.mat (increment U x i)) u (WilsonRootedHeldPacketGerm.linkBill G j) := by
  let L := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Bond f => G.Color) i
  have norm : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by
    rw [one_mul]; exact norm_le_pi_norm a i
  have exp : Allows j (fun a => G.mat (G.lieExp (L a))) u (eUniversal G j) := by
    refine ⟨(G.exp_jet.comp L.contDiff).contDiffAt, fun n hn => ?_⟩
    have hc := (unitPrice G j).used
    refine (endless L u j n hn).trans (mul_le_mul_of_nonneg_left ?_ (ample_pos G).le)
    apply (pow_le_pow_left₀ (mul_nonneg (by linarith) (norm_nonneg L)) _ n).trans
      (pow_le_pow_right₀ (by linarith) hn)
    exact (mul_le_mul_of_nonneg_left norm (by linarith)).trans (by linarith)
  exact exp.times (allows_const u (unit_pay (U i)).le)

theorem graded {k : ℕ} (W : book G k) (P : Finset (Bond c)) (X : Coat T F)
    (s : Signed) (x : Site f) (j : ℕ) :
    blockTaylor j (W.slab s x ∘ field P X) =
      blockTaylor j (blockTaylor j (W.slab s x ∘ increment (field P X 0)) ∘ blockTaylor j (changes P X)) := by
  apply composition
  exact (W.slab_notes _ (increment_link (field P X 0) j) s x 0).smooth

/-- The original multiplicative coefficient can depend on both dates and on
the measured temperature. The expenditure is local to this signed bank. -/
theorem measured {k : ℕ} (W : book G k) (P : Finset (Bond c)) (X : Coat T F)
    (s : Signed) (x : Site f) (r j : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : E} {z : E → Arguments G c f} (a : ℝ) {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1)
    (read : Brush j t 1 z y) :
    let d := r+2
    let cost := W.owes * W.premium (linkFee G (j+d+1)) (j+d+1)
    let prior := blockTaylor d (W.slab s x ∘ increment (field P X 0))
    let bch := blockTaylor d (changes P X)
    Brush j (|a| * ((j.factorial*cost)*(1+((1+1)*1):ℝ)^j*t^(r+3))) 1
      (fun w => a • (W.slab s x (field P X (z w)) - blockTaylor d (prior ∘ bch) (z w))) y := by
  intro d cost prior bch
  have h (v : Arguments G c f) (_hv : ‖v‖ ≤ t) :
      Brush (j+d+1) cost 1 (W.slab s x ∘ field P X) v :=
    W.slab_notes _ (links P X (j+d+1)) s x v
  have paid := (LocalTaylorR2.Mesh.priced (d:=d) ht ht' h read).smul a
  rw [graded W P X s x d] at paid
  exact paid

/-- The complete original Gram bank. Its own signed kinetic coefficient and
exponential path budget are retained on both sides. -/
def gram {K : PathData G} {B : Clip} {σ C Λ : ℝ} (paid : K.Bounds B σ C Λ) : book G 2 :=
  ⟨tides K, σ, gramCost G C, paid.width, tides_pay paid, tones K⟩

theorem kinetic {K : PathData G} {B : Clip} {σ C Λ : ℝ} (paid : K.Bounds B σ C Λ)
    (P : Finset (Bond c)) (X : Coat T F) (s : Signed) (x : Site f) (z : Arguments G c f) :
    (gram paid).slab s x (field P X z) =
      ∑' n, (gramPath K (towers G K n)).unmasked (pull s 0 (field P X z)) x := rfl

end YM.Integration.WilsonVacuumPreResetJointTicket
