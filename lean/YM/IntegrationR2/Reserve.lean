import YM.OPE.Vitrines.Budget
import YM.FullVolume.Mark.Mint

/-!
# A stronger gate on the *full-period Run*'s actual field tools

Core of the integration of the Strobe route into that Run. The missing budget
is a +2 support-exponent reserve on the *regular* terms of the chosen `entries`,
in exactly the derivative seminorm, BEFORE throwing away the masks or supported
norm. We retain the same underlying `Coefficient` including forced channel (no
weakening of `remBound`, no change to its sqrt divisor). This file: extra budget
survives projection and capture, not just evaluating at a configuration.

Parts of proofs adapted from `OPE.Vitrines.Budget`, `FullVolume.Mark.{Carts,Mint}`.
-/

set_option autoImplicit false
noncomputable section

namespace YM.MergeProof.Matric.R2
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d} {n : Side}
   {P : Coefficient F n} {R : Rep G n} {Y : Hol G} {c w : ℝ}

/-- Additional budget; spent in parallel with (not added into) `Span/Gig.future`.
Stated after the *same* turnCost. -/
def Plus (R : Rep G n) (P : Coefficient F n) (c : ℝ) : Prop :=
   Blown P 0 R (c / turnCost R.p.order R.p.power)

lemma turn_pos : 0 < turnCost R.p.order R.p.power := by unfold turnCost; positivity

lemma Plus.exhibits (hx : Blown P 0 R w) (h : turnCost R.p.order R.p.power*w ≤ c) :
    Plus R P c := hx.enlarge ((le_div_iff₀ turn_pos).mpr ((mul_comm ..).trans_le h))

lemma Plus.more (hx : Plus R P w) (h : w ≤ c) : Plus R P c := Blown.enlarge hx (div_le_div_of_nonneg_right h turn_pos.le)

lemma Plus.joins {ι : Type*} {E : ι → Coefficient F n} {a : ι → ℝ} (e : ℕ ≃ ι × ℕ) (h : ∀ i, Plus R (E i) (a i))
    (hp : Summable a) : Plus R (Extra.Histories.merge e E) (∑' i, a i) := by
   unfold Plus; rw [← tsum_div_const]; exact Blown.joins e h (hp.div_const _)

lemma Plus.captured (K : Keeper R.p R.activities) (h : P.Format 0 Y R)
    (hx : Plus R P c) : Plus R (tell (closeK K P)) c := by
  obtain ⟨A,hA,hC⟩ := hx
  let f:=tongue P.support
  let t:=extend f A 0
  have hz i:t (f i)=A i:=f.injective.extend_apply ..
  refine ⟨t,?_,fun i=>?_⟩
  · refine Local.sumBudget_pass f _ ?_ ?_
    · change SumBudget (fun i=> reservedMass R.p (mapSeat (n:=n) (f i)) (t (f i))) _
      have he i: mapSeat (f i)=P.support i:= leased _ h i
      simp_rw [he,hz]; exact hA
    · intro i hi; rw [show t i=0 from extend_apply' _ _ _ hi,reservedMass,mul_zero]
  change R.p.supBounds 0 (mapSeat i) (liveE P i) (t i)
  by_cases he:i∈ Set.range f
  · obtain ⟨i,rfl⟩:= he; rw [hz,show mapSeat (f i)=P.support i from leased P h i,show liveE P (f i)=P.regular i from f.injective.extend_apply ..]; exact hC i
  rw [liveE,extend_apply' _ _ _ he,show t i=0 from extend_apply' _ _ _ he]; exact (regular0 ..).2

variable {B : SectionData F} {H : History G} {N p i : ℕ} {X : ℕ→Support (H.S.side i p)}
    {M: Local.Raw F (H.S.side i p)} {f:Config G (H.S.side (i+1) p)→ℂ} {lead:F.Coeff} {t r:ℝ}

/-- Gain the regular reserve even after reprinting canonical fields, retaining
all forced partners. Important that it works with the very same berths used by
`Matric` (no existential projection naming). -/
lemma projectPlus
    (S: Berths (H.rep N p i).p (H.rep N p i).activities (fun q=>joint B 0 (X q)))
    (h:Fancy B H N p i Y f X M lead w t r) (hx:H.Conv N p i)
    (he:Readable Y B (H.rep N p i).p (H.S.side i p) w):
    Plus (H.rep N p i) (mint S M Y) r := by
   obtain ⟨a,b,c,⟨h₁,-⟩,-,hv,⟨pQ,q,hq,h₃⟩,hA,-⟩:=h
   have hκ:0 < kappa H i := Real.sqrt_pos.mpr (forcedPos ..)
   have hp:Tab (mint S M Y) 0 (H.rep N p i) (kappa H i) a (b+c):= tab_mint S h₁ hx.good hκ he hv
   exact Plus.exhibits (h₃ ▸ Blown.deck S h₁ he hq) ((le_add_of_nonneg_right hp.second).trans hA)
end YM.MergeProof.Matric.R2

