import YM.Integration.WilsonVacuumPreResetPeriodField
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Rank
import YM.RG01Estimate.VacuumAcquire

/-! Spatial tails of the original finite period packets, charged at the
support exponent used by the reset. The cut is made before the period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetPeriodTail
open Function Finset Lattice RG Wilson Marker WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open PhysicalNext PhysicalNext.Repeat RG01Estimate IterationFour.Vacuum Extra.Iteration
open AnalyticBridge VerifiedReset Collection Quotes LocalComparison.Global Push.AbsoluteSums Push.AbsoluteSums.Animals
open WilsonVacuumPreResetPeriodEntries
open scoped Classical Topology BigOperators
variable {G:Gauge}{n:Side}

def short (B:BudgetPoint)(D:ℕ)(A:ℕ → RegularAddress n)(i:ℕ):Prop:=
    coverNumber B.B (A i).support≤D

theorem housed (B:BudgetPoint)(D:ℕ)(A:ℕ → RegularAddress n)(i:ℕ)(h:short B D A i):
    (A i).support⊆neighbors (D*(4*B.B+2)+2*B.B) (A i).site:=by
  intro x hx
  apply (neighbors_mem ..).2
  exact (Corona.extent _ _ (A i).anchor hx).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _)

theorem long (simple:G.Simple)(hn:20<n.val)(B:BudgetPoint){σ C:ℝ}(hs:0<σ)
    (reach:preExponent (Song.headline B) / B.B ≤ σ/4)(blocks:2 ≤ B.B)
    (Z:SeriesA G)(draw:Draw Z σ C)(k:ℕ → ℕ → ℝ)(D:ℕ):
    let A:=entries n B σ C Z k
    let Q:=quote (Z.map (FundedCorrectedPeriod.piece n (Song.headline (Song.headline B)) σ C)) k
    Meadow.Budget B A.reg (fun i=>if short B D A.reg i then 0 else A.E i)
      (Real.exp (-(3:ℝ)*(D+1))*Q):=by
  intro A Q
  have h:= (WilsonVacuumPreResetPeriodEntries.original simple hn (Song.headline B) hs reach blocks Z draw k).1
  rw [←same (n:=n) B (Song.headline B) σ C Z k] at h
  obtain ⟨f,fee,row⟩:=h
  let len (i:ℕ):=coverNumber B.B (A.reg i).support
  have boost:early B A.reg (fun i=>f i*Real.exp (3*(len i:ℝ))) Q:=by
    intro x
    convert fee x using 1
    funext i
    dsimp only
    split_ifs
    · rw [mul_assoc,←Real.exp_add]
      congr 2
      dsimp [preExponent,Song.headline,len,A]
      ring
    · rfl
  have ht:=Meadow.arch_tail (k:=D+1) (σ:=3) A.reg B len boost (by norm_num) (fun i=>(row i).2.1)
  let cost (i:ℕ):=if short B D A.reg i then 0 else f i
  refine ⟨cost,?_,?_⟩
  · have sameCost:(fun i=>if D+1≤len i then f i else 0)=cost:=by
      funext i
      dsimp [cost,short,len]
      split_ifs <;> first|rfl|omega
    rw [sameCost, Nat.cast_add, Nat.cast_one] at ht
    exact ht
  · intro i
    by_cases active:short B D A.reg i
    · simp only [active,cost,if_true]
      exact ⟨CouplingShape.reg_const _,by simpa only [abs_zero] using!
        (CouplingShape.sup_const (G:=G) (p:=B) (o:=(A.reg i).site) (X:=(A.reg i).support) 0)⟩
    · simp only [active,cost,if_false]
      obtain ⟨r,v⟩:=row i
      exact ⟨⟨r.sites,r.borel,r.symmetry,r.smooth,r.hasDerivs⟩,v⟩

end YM.Integration.WilsonVacuumPreResetPeriodTail
