import YM.Push.ABSOLUTE_SUMS.Basic
import YM.Next.STATIONARY.Shape.ClassicalMatch
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Shellac.Proof
/-!
# Tallies on unmasked packet crops. This controls actual `blockTaylor` at the needed stage

Crop uses original paths (length on cover) at any prescribed ticket. Retains
all coefficients for repeated lengths: not discard "beyond index". Actual
masks & flags counted separately. Reuses `BareRates` trick pricing same-side
literal via forest `ratio c` used ONLY for pricing canonical path-data reads
(no one performs fictional ratio-one RG).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Plateau
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext Repeat Lapis Bid Planned.JetPort
open Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush Poll
open AbsoluteSums Fare Shellac
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G: Gauge} {n : Side} {k j W : ℕ}
def mute (A:Atom G k):Atom G k:={A with coeff:=0}
def crop (w:ℕ)(A:Atom G k) := if A.length ≤ w then A else mute A
def leaf (w:ℕ)(A:Atom G k) := if A.length ≤ w then mute A else A
@[simp] lemma mute_length (A:Atom G k): (mute A).length=A.length:=rfl
@[simp] lemma mute_poly (A:Atom G k)(v:Fin k→G.Color): (mute A).poly v=0:=by simp [RG.Atom.poly,mute]
@[simp] lemma mute_inv (A:Atom G k): (mute A).Invariant:=by simp [RG.Atom.Invariant]
@[simp] lemma mute_unc (A: Atom G k) (U:Config G n)(x:Site n): (mute A).unmasked U x=0:=by simp [Atom.unmasked]
@[simp] lemma mute_bud (A: Atom G k)(c:ℝ): (mute A).budget c=0:=by simp [Atom.budget,mute,Atom.magnitude]
lemma paid_nonneg (A:Atom G k)(t:ℝ):0≤A.budget t:= by unfold Atom.budget Atom.magnitude; positivity
lemma crop_inv (w:ℕ){A:Atom G k}(h:A.Invariant):(crop w A).Invariant:=by unfold crop; split; exact h; exact mute_inv _
variable (A:ℕ→Atom G k) {σ C Z D :ℝ} (hs:0<σ)(hb: SumBudget (fun i=>(A i).budget σ) C)
include hs hb
omit hs hb in
lemma sold (_hs:0<σ) (hb: SumBudget (fun i=>(A i).budget σ) C) (w:ℕ) : SumBudget (fun i=> (crop w (A i)).budget σ) C := budget_mono hb (fun _=> paid_nonneg ..) (fun i=> by unfold crop; split; rfl; rw [mute_bud]; exact hb.1 i)
lemma release (w:ℕ): SumBudget (fun i=> (leaf w (A i)).budget (σ/2)) (Real.exp (-(σ/2)*w)* C):= by
 refine budget_mono (budget_scale (Real.exp_pos _).le hb) (fun i=> paid_nonneg ..) (fun i=>?_); unfold leaf; split; · rw [mute_bud]; exact mul_nonneg (Real.exp_pos _).le (hb.1 i)
 rename_i h; unfold Atom.budget; rw [mul_left_comm,← Real.exp_add]; gcongr; · unfold Atom.magnitude; positivity
 have he:(w:ℝ) ≤ (A i).length:= Nat.cast_le.mpr (not_le.mp h).le; nlinarith
lemma summation (U:Config G n)(x:Site n): Summable (fun j=>(A j).unmasked U x):= Summable.of_norm_bounded (hb.2.1.mul_right (2^k:ℝ)) (fun i => ((A i).unmasked_bound ..).trans (mul_le_mul_of_nonneg_right ((A i).lower_budget _ hs) (by positivity)))
open Stationary
lemma post_bill (w:ℕ)(U :Config G n): orbitRaw A U - orbitRaw (crop w ∘ A) U= orbitRaw (leaf w ∘ A) U:= by
 have hV(W:Config G n)(x:Site n): (∑' i,(A i).unmasked W x) - (∑' i,(crop w (A i)).unmasked W x)= ∑' i,(leaf w (A i)).unmasked W x := by
    rw [← Summable.tsum_sub (summation A hs hb W x) (show Summable (fun i=> (crop w (A i)).unmasked W x) from summation (crop w ∘ A) hs (sold A hs hb w) W x)]; refine tsum_congr (fun i=>?_); unfold crop leaf; split <;> simp only [*, mute_unc,sub_self,sub_zero]
 unfold orbitRaw uncut Patch.average; rw [← mul_sub,← Finset.sum_sub_distrib]; congr 1; refine Finset.sum_congr rfl fun v _=>?_ ; rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun i _=> hV _ _)
-- copy oracle at home
variable (hZ : PaintSupply G j Z)
def amt (G:Gauge) (k j:ℕ) (σ Z :ℝ):= |atomCost G Z σ j k| * countCost ((entryWidth j (Planned.JetPort.ratio ⟨1,by decide⟩).count σ)/2)
omit hb in
lemma amt_nonneg (Z:ℝ)(k j:ℕ): 0≤amt G k j σ Z:=mul_nonneg (abs_nonneg _) (count_pos (half_pos (width_positive hs ..))).le
local notation "E"=>Positions (Primary n G)
abbrev speak (n:Side) (x:Positions (Primary n G)):= orbitRaw A (represent (tint G _ x))
include hZ
lemma signal (x:E)(hx:x∈ball 0 1) : ContDiffAt ℝ ω (speak A n) x ∧ Scatter (throat n G) (dial σ j) j (speak A n) x (C*amt G k j σ Z):= by
 let B := arbor n; let h:= feeder G n; let y:=h x; let L' := (Planned.JetPort.ratio n).count; have hy : y∈ball 0 1:= mem_ball_zero_iff.mpr ((feed_norm x).trans_lt (mem_ball_zero_iff.mp hx))
 let a := entryWidth j L' σ; let v:=weaker j a; let b := countCost (a/2); let b':= address B G; let Z₀:=atomCost G Z σ j k
 have hp : 0<a := width_positive hs j L'; let U (z : Positions (Joint B G)) := fine G B z
 let P (l:Signed) z:=pull l (0:Site n) (U z)
 let f i z:=uncut A (P i z)
 have hC := budget_nonneg hb
 have hh(s:Signed):ContDiffAt ℝ ω (f s) y ∧ Scatter b' v j (f s) y (C*amt G k j σ Z):= by
    let g i (z : Positions (Joint B G)) := ∑' k,(A k).unmasked (P s z) i
    have hf i : ContDiffAt ℝ ω (g i) y := label_analytic B A hs hb s hZ i y hy
    have hg i : Beacon b' a j (g i) (affine s 0 i) y (C*Z₀) := atom_beacon B s hs hb hZ y hy i
    have hi : Injective (affine (R:=Per n) s 0) := fun i j h => by
      unfold affine at h; have he := add_right_cancel h; simpa using congr_arg s⁻¹.act he
    refine ⟨ContDiffAt.sum (s:=Finset.univ) (fun i _ => hf i),?_⟩; have he:= scatter (Multiplicity.injective hi) (fun i=>hf i) (fun i=> (hg i).mono (mul_le_mul_of_nonneg_left (le_abs_self _) hC)) hp (mul_nonneg hC (abs_nonneg _)); rw [Nat.cast_one, mul_one, mul_assoc] at he; exact he
 let F (i:Positions (Joint B G)):= Patch.average fun s: Signed=> f s i
 rw [show speak A n= F∘ h from funext fun x'=>by unfold speak orbitRaw; simp_rw [←fed x']; rfl]; exact feed_through (symAll (fun i=> (hh i).1) (fun i=> (hh i).2)).1 (symAll (fun i=>(hh i).1) (fun i=> (hh i).2)).2
lemma speaking (hj:1≤j)(hm:1≤D)(hD:(Fintype.card (Primary n G):ℝ)≤D)(x:E)(hx:x∈ball 0 1) : Brush j (tollS D j (C*amt G k j σ Z)*2) 1 (Shellac.off (speak A n)) x:= by
 rw [show (2:ℝ)=1+1 by norm_num]; have ha:0<dial σ j:= by unfold dial weaker; exact div_pos (width_positive hs ..) (by positivity)
 exact (horizonB hm hD (mul_nonneg (budget_nonneg hb) (amt_nonneg hs Z k j)) ha zero_lt_one hj hx (fun i hh=> And.symm (signal A hs hb hZ i hh))).2
end YM.AllOrder.Plateau
