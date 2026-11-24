import YM.Integration.OriginalMarkedLocalDifference
import YM.Integration.WilsonRootedInteriorSpringDiscrepancy
import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskBoard

/-! Oscillation of the full signed masked action on an arbitrary fixed exterior.
The separately filed kinetic rows require the spatial regularity of their own
invoice and may have a nonzero affine Hessian. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Function Finset Lattice Lattice.Corona RG Wilson Push.GridApprox.Attach
open RG01Estimate AnalyticBridge VerifiedReset Collection Quotes
open PhysicalNext PhysicalNext.Repeat
open scoped Classical BigOperators
variable {G:Gauge} {n:Side}

private theorem mask_local {p:BudgetPoint} {X:Support n} {f:Config G n→ℝ}
    (smooth:p.Regular X f) : LocalOn (inspected X) (masked p.threshold X f) := by
  apply UsesFinal.allReads p.threshold X (masked p.threshold X f)
  intro U V eq hflags
  have same:Healthy p.threshold X U↔Healthy p.threshold X V:=by
    simp only [Healthy,Finset.disjoint_iff_inter_eq_empty]
    rw [hflags]
  by_cases good:Healthy p.threshold X U
  · rw [masked_eq _ _ _ _ good,masked_eq _ _ _ _ (same.mp good)]
    exact smooth.sites U V eq
  · rw [masked_ne _ _ _ _ good,masked_ne _ _ _ _ (mt same.mpr good)]

private theorem row_bound {p:BudgetPoint} {X:RegularAddress n} {f:Config G n→ℝ} {b:ℝ}
    (h:p.supBounds X.site X.support f b) (U:Config G n):‖masked p.threshold X.support f U‖≤b:=by
  by_cases good:Healthy p.threshold X.support U
  · rw [masked_eq _ _ _ _ good]
    exact h.2 U good [] (Nat.zero_le _) (by simp)
  · rw [masked_ne _ _ _ _ good,norm_zero]
    exact h.1

theorem local_rows (A:Activities G n) (p:BudgetPoint) {fee:ℝ}
    (reg:∀i,p.Regular (A.reg i).support (A.E i)) (paid:A.EBound p fee)
    (r:ℕ)(hr:1≤p.supportExponent*r)(S:Support n)(U V:Config G n)
    (outside:OriginalMarkedLocalDifference.Outside S U V):
    let part i:=A.regularOccurrence p i U-A.regularOccurrence p i V
    HasSum (fun i=>if Disjoint (A.reg i).support (halo 8 S) then 0 else part i)
      (A.additive p U-A.additive p V) ∧
    |A.additive p U-A.additive p V|≤2*((S.card:ℝ)*17^4*(hitConstant ((p.B+1)*r)*fee)):=by
  intro part
  have sum:HasSum part (A.additive p U-A.additive p V):=
    (LocalComparison.PreReset.series_of_EBound paid U).hasSum.sub (LocalComparison.PreReset.series_of_EBound paid V).hasSum
  have skip (i:ℕ)(away:Disjoint (A.reg i).support (halo 8 S)):part i=0 := by
    apply sub_eq_zero.mpr
    exact mask_local (reg i) U V (OriginalMarkedLocalDifference.inspected_outside outside away)
  constructor
  · apply sum.congr_fun
    intro i
    split_ifs with away
    · exact (skip i away).symm
    · rfl
  obtain ⟨b,cap,roots⟩:=paid
  let H:=halo 8 S
  let bill (i:ℕ):=if ¬Disjoint (A.reg i).support H then b i else 0
  have price:SumBudget bill ((H.card:ℝ)*(hitConstant ((p.B+1)*r)*fee)):=
    OriginalMarkedSupportMass.carrier A p b (fun i=>(cap i).1) roots H r hr
  have point (i:ℕ):‖part i‖≤2*bill i:=by
    by_cases away:Disjoint (A.reg i).support H
    · rw [skip i away,norm_zero,show bill i=0 from if_neg (not_not_intro away),mul_zero]
    · rw [show bill i=b i from if_pos away]
      exact (norm_sub_le ..).trans ((add_le_add (row_bound (cap i) U) (row_bound (cap i) V)).trans
        (two_mul (b i)).symm.le)
  have bs:Summable (fun i=>2*bill i):=price.2.1.mul_left _
  have as:=bs.of_nonneg_of_le (fun i=>norm_nonneg (part i)) point
  have hf:0≤fee:=(tsum_nonneg (roots 0).1).trans (roots 0).2.2
  have hc:0≤hitConstant ((p.B+1)*r):=by
    unfold hitConstant
    exact mul_nonneg (by positivity) (tsum_nonneg fun i=>(polyExp_pos i).le)
  have size:(H.card:ℝ)≤(S.card:ℝ)*17^4:=by exact_mod_cast halo_size S 8
  rw [←sum.tsum_eq,←Real.norm_eq_abs]
  calc ‖∑'i,part i‖≤∑'i,‖part i‖:=norm_tsum_le_tsum_norm as
       _≤∑'i,2*bill i:=as.tsum_le_tsum point bs
       _=2*∑'i,bill i:=tsum_mul_left
       _≤_:=by exact mul_le_mul_of_nonneg_left (price.2.2.trans
          (mul_le_mul_of_nonneg_right size (mul_nonneg hc hf))) (by norm_num)

end YM.Integration.OriginalMarkedRunAction
