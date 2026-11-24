import YM.Integration.WilsonPhysicalHistoryRegisteredSplit
import YM.Integration.WilsonDegreeFourFundedTail
import YM.Push.GRID_APPROXIMATION.Canonical

/-! The entire inherited regular field, including its primary, at each
genuine previous date. The thermal frame scaling cancels in the native
specific price for the submitted section. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredRegularQuota
open Function Finset MeasureTheory Lattice RG Wilson Source Labels Push.Local MergeProof
open WilsonInheritedRegisteredField
open scoped Classical BigOperators
variable {G : Gauge} {C : Family G} (h : C.Makes) {k N per d : ℕ}

theorem original (hk : k≤N) (hr : C.ref d≤k) (w : C.label d) (o : Site (C.side k per))
    (U : Config G (C.side k per)) :
    ‖regular h hk w o U‖ ≤ 3*(C.path.levels.params k).columns*
      (((C.S.a k)^d)⁻¹*Next.UVStress.quota C d k N per w) := by
  let Z:=packet h hk w o
  let A:=C.path.rep N per k
  let S:=C.localSection d
  let L:=C.labels.level d
  let K:=(C.path.levels.params k).columns
  let θ:=A.p.threshold
  have k1 : 1≤K := (C.path.levels.params k).columns_ge
  have k0 : 0≤K := zero_le_one.trans k1
  have normal : L.coeffSize Z.x=Next.UVStress.quota C d k N per w :=
    congrArg L.coeffSize (WilsonTranslatedFactory.coordinate h hk o ((C.factory d N per).terminal.symm w))
  have core := Work.G08.size_core L Z.x
  have zero : 0≤L.coeffSize (L.core Z.x) := sum_nonneg fun _ _=>norm_nonneg _
  have size : 0≤L.coeffSize Z.x := zero.trans core
  let v:=L.scaled θ⁻¹ (L.core Z.x)
  have row : ‖masked θ (S.footprint o) (S.places v o) U‖ ≤ K*L.coeffSize (L.core Z.x) := by
    by_cases clean : Healthy θ (S.footprint o) U
    · rw [masked_eq _ _ _ _ clean]
      have bill := (Push.GridApprox.specific_price C h o hr hk v).2.2 U clean [] (Nat.zero_le _) (by simp)
      change ‖S.places v o U‖ ≤ K*L.coeffSize (L.scaled θ v) at bill
      rwa [show L.scaled θ v = L.core Z.x from L.scaled_inv A.p.threshold_pos.ne' _] at bill
    · rw [masked_ne _ _ _ _ clean,norm_zero]
      exact mul_nonneg k0 zero
  have tails : ‖∑' i,Z.maskedTerm A i U‖ ≤ K*L.coeffSize (L.core Z.x) := by
    simpa only [WilsonDegreeFourInheritedTail.tail,Nat.zero_le,ite_true,Nat.cast_zero,
      mul_zero,Real.exp_zero,one_mul] using WilsonDegreeFourInheritedTail.field h hk hr w o 0 U
  have unit : ‖Z.x 0‖ ≤ L.coeffSize Z.x :=
    Finset.single_le_sum (f:=fun i=>‖Z.x i‖) (fun i _=>norm_nonneg _) (mem_univ _)
  have upper : ‖Z.exponentialEntry o S A U‖≤3*K*L.coeffSize Z.x := by
    calc
      _ ≤ (‖Z.x 0‖+‖masked θ (S.footprint o) (S.places v o) U‖)+
          ‖∑'i,Z.maskedTerm A i U‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (K*L.coeffSize Z.x+K*L.coeffSize Z.x)+K*L.coeffSize Z.x :=
        add_le_add (add_le_add (unit.trans (le_mul_of_one_le_left size k1))
          (row.trans (mul_le_mul_of_nonneg_left core k0))) (tails.trans (mul_le_mul_of_nonneg_left core k0))
      _ = _ := by ring
  change ‖alto C.path k d*Z.exponentialEntry o S A U‖≤_
  rw [norm_mul,alto_norm,←normal]
  calc
    _ ≤ ((C.S.a k)^d)⁻¹*(3*K*L.coeffSize Z.x) := mul_le_mul_of_nonneg_left upper
      (inv_nonneg.mpr (pow_nonneg (C.S.a_pos _).le _))
    _ = _ := by dsimp only [K];ring

end YM.Integration.WilsonRegisteredRegularQuota
end
