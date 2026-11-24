import YM.Integration.WilsonVacuumPreResetJointTicket
import YM.Integration.WilsonPhysicalHistoryRetainedSpringIncoming

/-! The actual signed rotation average of a complete countable field bank is
taken before its Taylor bill. The same age-dependent coefficient multiplies
the physical site and its finite coarse-plus-fine Taylor polynomial. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetJointSite
open Stationary Function Filter Finset Lattice RG Wilson Tree Pressure Gauge Precision
open Push Push.Uniform Push.AbsoluteSums ConnectedActivityE6 Coat Control Blaze
open AnalyticNext.QuarticMatch.Estimate RG01.Sounder Logfee Work.G05
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetJointField WilsonVacuumPreResetJointRaw OriginalMarkedRunAction
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def developed (P : Finset (Bond c)) (X : Coat T F) (d : ℕ) (A : Config G f → ℝ) :
    Arguments G c f → ℝ :=
  blockTaylor d (blockTaylor d (A ∘ increment (field P X 0)) ∘ blockTaylor d (changes P X))

def bill {k : ℕ} (W : book G k) (j r : ℕ) (t : ℝ) : ℝ :=
  let h := j+(r+2)+1
  j.factorial*(W.owes*W.premium (linkFee G h) h)*(1+((1+1)*1):ℝ)^j*t^(r+3)

private theorem collected {y : E} {v : ℝ} {j : ℕ} (A : Signed → E → ℝ)
    (financed : ∀ s, Brush j v 1 (A s) y) :
    Brush j v 1 (fun w => Patch.average fun s : Signed => A s w) y := by
  have pos : 0 < (Fintype.card Signed : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have all := (Brush.spree univ A (fun _ => v) zero_le_one (fun s _ => financed s)).smul
    ((Fintype.card Signed : ℝ)⁻¹)
  simpa [Patch.average, Real.norm_of_nonneg (inv_nonneg.mpr pos.le), nsmul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ pos.ne'] using all

def printed {k : ℕ} (W : book G k) (P : Finset (Bond c)) (X : Coat T F) (d : ℕ)
    (x : Site f) (v : Arguments G c f) : ℝ :=
  Patch.average fun s : Signed => developed P X d (W.slab s x) v

theorem measured {k : ℕ} (W : book G k) (P : Finset (Bond c)) (X : Coat T F)
    (x : Site f) (r j : ℕ) {y : E} {z : E → Arguments G c f} (a : ℝ)
    {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1) (read : Brush j t 1 z y) :
    Brush j (|a| *bill W j r t) 1
      (fun w => a*(sitePacket W.words x (field P X (z w)) - printed W P X (r+2) x (z w))) y := by
  have h := collected (fun s w => a*(W.slab s x (field P X (z w)) -
      developed P X (r+2) (W.slab s x) (z w)))
    (fun s => WilsonVacuumPreResetJointTicket.measured W P X s x r j a ht ht' read)
  apply h.shimmy (Filter.Eventually.of_forall fun w => ?_)
  simp only [printed, sitePacket, book.slab, Patch.average, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  ring

theorem sumSites {k : ℕ} (W : book G k) (P : Finset (Bond c)) (X : Coat T F)
    (I : Finset (Site f)) (r j : ℕ) {y : E} {z : E → Arguments G c f} (a : ℝ)
    {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1) (read : Brush j t 1 z y) :
    Brush j (I.card * (|a| *bill W j r t)) 1 (fun w => ∑ x ∈ I,
      a*(sitePacket W.words x (field P X (z w)) - printed W P X (r+2) x (z w))) y := by
  simpa [nsmul_eq_mul] using Brush.spree I _ (fun _ => |a| *bill W j r t)
    zero_le_one (fun x _ => measured W P X x r j a ht ht' read)

end YM.Integration.WilsonVacuumPreResetJointSite
