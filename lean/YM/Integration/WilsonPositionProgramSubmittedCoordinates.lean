import YM.Integration.WilsonPositionProgramNormalizedMaster

/-! Each already measured numerical coordinate is submitted unchanged on
both upper cutoffs. The root has derivative order zero on the named source. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionProgramSubmittedCoordinates
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open scoped Topology BigOperators Classical
variable {G:Gauge}{a h:ℕ}

open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonPositionProgramNormalizedMaster (fee)

def plain (F:Frame G h)(i:F.Index):Alma F:=
  ⟨⟨i,⟨0,by simp⟩⟩,by simpa [rankS] using F.bound i⟩

def submitted (R:Run G)(l d:Fin (a+1)→ℕ)(fit:∀i,l i<d i)
    (x:(i:Fin (a+1)) → R.family.label (l i))(p:Fin (a+1)→ℂ →L[ℝ] ℝ):
    Herit (deck (G:=G) l d fit) :=fun i j=>
  if rankS j.val.2=0 then PowerSeries.C (p i (x i j.val.1)) else 0

theorem entry (R:Run G)(l d:Fin (a+1)→ℕ)(fit:∀i,l i<d i)(x:(i:Fin (a+1))→ R.family.label (l i))
    (p:Fin (a+1)→ℂ →L[ℝ] ℝ)(i:Fin (a+1))(v:(R.family.labels.level (l i)).Index):
    (submitted R l d fit x p i) (plain (R.family.labels.level (l i)) v)=PowerSeries.C (p i (x i v)):=by
  simp [submitted,plain,rankS]

theorem paid (R:Run G)(l d:Fin (a+1)→ℕ)(fit:∀i,l i<d i)(x:(i:Fin (a+1)) → R.family.label (l i))
    (p:Fin (a+1)→ℂ →L[ℝ] ℝ)(e:ℕ)(i:Fin (a+1)):
    fee (submitted R l d fit x p) e i ≤
      Fintype.card (Alma (R.family.labels.level (l i))) * (e+1:ℕ) *
      (‖p i‖*(R.family.labels.level (l i)).coeffSize (x i)):=by
  let F:=R.family.labels.level (l i)
  let A:=‖p i‖ * F.coeffSize (x i)
  have positive:0≤A:=mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun _ _=>norm_nonneg _)
  have each (j:Alma F)(r:Fin (e+1)):‖PowerSeries.coeff r.val ((submitted R l d fit x p i) j)‖≤A := by
    unfold submitted
    split
    · rw [PowerSeries.coeff_C]
      split
      · exact ((p i).le_opNorm _).trans (mul_le_mul_of_nonneg_left
          (single_le_sum (s:=univ) (f:=fun b:F.Index=>‖x i b‖) (fun _ _=>norm_nonneg _) (mem_univ j.val.1))
          (norm_nonneg _))
      · simpa only [norm_zero] using positive
    · simpa only [map_zero,norm_zero] using positive
  calc
    _ ≤ ∑ _j:Alma F,∑ _r:Fin (e+1),A :=
      Finset.sum_le_sum fun j _=>Finset.sum_le_sum fun r _=>each j r
    _ = _ :=by simp [A,F]; ring

end YM.Integration.WilsonPositionProgramSubmittedCoordinates
end
