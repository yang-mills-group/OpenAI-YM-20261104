import YM.Integration.WilsonPhysicalHistoryWalletCofactorRows

/-! The original physical terminal labels, with all complex engineering and
basis coefficients, attached to the signed two-position wallets down to an
arbitrary earlier date on that same cutoff. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryWalletPhysicalCofactor
open Function Filter Finset MeasureTheory Lattice RG RG.Supply Wilson Source Labels Next.Foundations
open OPE OPE.Therm WilsonCoeffUV PhysicalNext.Repeat.Legato
open FVA1Physical.Wilson FVA1Physical.Round2.Curvature RGComparison.Core16.Spool
open WilsonReportForwardTransfer WilsonConditionalTaylorLabels WilsonOffsetPhysicalPair
open WilsonOffsetPhysicalPairWick WilsonPhysicalHistoryWalletCofactorRows
open WilsonPhysicalHistoryWalletExperiment WilsonPhysicalHistoryWalletDeposit
open scoped BigOperators Classical
variable {G : Gauge} {d h : ℕ}

def opening (R : Run G) (d h : ℕ) : ℕ :=
  Finset.univ.sup (fun t : Index G d h=>opens R (two t.1 t.2))

def cash (R : Run G) {N per j u : ℕ} (ju : j≤u) (bz be : Site (R.family.side (u+1) per))
    (Qz Qe : Coefficient ((frames G).level 0) (R.family.side j per)) (V : Config G (R.family.side j per)) : ℂ :=
  let P:=R.family.path.rep N per j
  (Qz.exponentialEntry (anchor R ju bz) (localSection G 0) P V -
    Qe.exponentialEntry (anchor R ju be) (localSection G 0) P V) + (forcedShare Qz P V-forcedShare Qe P V)

theorem measured (R : Run G) {per j u : ℕ} (ju : j≤u) (v : R.family.label d) (w : R.family.label h)
    (x z e : Site (R.family.side (u+1) per)) :
    exterior (C:=R.family) (N:=u+1) (ju.trans u.le_succ) (fun U=>
      R.family.O (u+1) per v x U*(R.family.O (u+1) per w z U-R.family.O (u+1) per w e U)) =
    fun V=>∑t : Index G d h,coefficient R (u+1) per v w t*
      (component R (N:=u+1) ju t x z e false V+Complex.I*component R (N:=u+1) ju t x z e true V) := by
  let F := fun (t : Index G d h) U=>coefficient R (u+1) per v w t*word t x z e U
  have raw : (fun U=>R.family.O (u+1) per v x U*(R.family.O (u+1) per w z U-R.family.O (u+1) per w e U)) =
      fun U=>∑t : Index G d h,F t U := by
    funext U
    rw [WilsonOffsetPhysicalPair.relative R v w x z e U,Fintype.sum_prod_type]
    rfl
  letI : IsProbabilityMeasure (scene R.family.path (u+1) per (u+1)) := probability R.makes.wilson le_rfl
  have fare (t : Index G d h) : Integrable (F t) (scene R.family.path (u+1) per (u+1)) :=
    ((shore t x z e).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul _
  rw [raw,WilsonPhysicalHistoryWalletSum.full R (ju.trans u.le_succ) le_rfl univ F fare]
  funext V
  apply sum_congr rfl
  intro t _
  change exterior (C:=R.family) (N:=u+1) (ju.trans u.le_succ) (fun U=>coefficient R (u+1) per v w t*word t x z e U) V = _
  rw [WilsonPhysicalHistoryWalletSum.scaled R (ju.trans u.le_succ) le_rfl,
    recovered R (Nat.lt_succ_self u) ju t x z e]

/-- The complete genuine ultraviolet cofactor, against the unchanged detector
at x and the two actual receiver placements z,e, at any admitted physical j. -/
theorem original (R : Run G) (simple : G.Simple) {per j u : ℕ} (ju : j≤u)
    (v : R.family.label d) (w : R.family.label h) (x z e bz be : Site (R.family.side (u+1) per))
    (late : opening R d h ≤ j) :
    ∃Qz Qe : Index G d h → Bool → Coefficient ((frames G).level 0) (R.family.side j per),
      (∀t part, Registered R (N:=u+1) ju (two t.1 t.2) univ (seats t.1 t.2 x e) (slot t) z bz part (Qz t part) ∧
        Registered R (N:=u+1) ju (two t.1 t.2) univ (seats t.1 t.2 x e) (slot t) e be part (Qe t part)) ∧
      ∀V, exterior (C:=R.family) (N:=u+1) (ju.trans u.le_succ) (fun U=>
        R.family.O (u+1) per v x U*(R.family.O (u+1) per w z U-R.family.O (u+1) per w e U)) V =
        ∑t : Index G d h,coefficient R (u+1) per v w t*
          (cash R (N:=u+1) ju bz be (Qz t false) (Qe t false) V+
           Complex.I*cash R (N:=u+1) ju bz be (Qz t true) (Qe t true) V) := by
  have paid := fun (t : Index G d h) (part : Bool)=>
    WilsonPhysicalHistoryWalletSignedPair.original R simple (N:=u+1) (Nat.lt_succ_self u) ju (two t.1 t.2)
      univ (seats t.1 t.2 x e) (slot t) (mem_univ _) z e bz be part
      ((Finset.le_sup (f:=fun (s : Index G d h)=>opens R (two s.1 s.2)) (Finset.mem_univ t)).trans late)
  choose Qz Qe bill using paid
  refine ⟨Qz,Qe,fun t part=>⟨(bill t part).1,(bill t part).2.1⟩,?_⟩
  intro V
  rw [measured R ju v w x z e]
  apply sum_congr rfl
  intro t _
  have same (part : Bool) : component R (N:=u+1) ju t x z e part V =
      cash R (N:=u+1) ju bz be (Qz t part) (Qe t part) V := (bill t part).2.2.2 V
  rw [same false,same true]

end YM.Integration.WilsonPhysicalHistoryWalletPhysicalCofactor

