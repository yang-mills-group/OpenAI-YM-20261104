import YM.Integration.WilsonLimitConstruction.FundedMarkedSoftRows

/-! The full finite-to-cover marked correction on actual ordinary and
compulsory addresses. Only the forced cluster factors need a separate
thermal identification on fields where the ordinary masks vanish. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedMarkedFieldSplit
open Function Lattice Wilson RG Marker Overlay RG3.Forms RG3.Held RG3.Script.Picnic
open LocalComparison FullQLocal OPE.Therm FundedMarkedSoftRows
open scoped BigOperators Classical

variable {G : Gauge} {V X : Type} [Fintype V] [DecidableEq V] {Γ : Census V}
    {n : Side} {P : Rep G n} {o : V→Site n}

structure Compulsory (X : Type) (Γ : Census V) (G : Gauge) (n : Side) where
  mode : ℕ→ℕ→Γ.Mode
  value : X→ℕ→ℕ→ Config G n→ℂ

def replace (T : Taste X o P Γ) (H : Compulsory X Γ G n) : Taste X o P Γ where
  menu := { T.menu with marks := H.mode, force := H.value }
  root := T.root
  tag := T.tag
  site := T.site
  score := T.score

theorem forced_only (T : Taste X o P Γ) (H : Compulsory X Γ G n) (x : X) (U : Config G n) :
    ((replace T H).leaf x).log U=(T.leaf x).log U := rfl

theorem cluster_density (T : Taste X o P Γ) (H : Compulsory X Γ G n) (x : X) (U : Config G n)
    (h : Poly Γ) (charged : ((replace T H).leaf x).contents.cluster U =
      Poly.pass h*(T.leaf x).contents.cluster U) :
    ((replace T H).leaf x).density U=Poly.pass h*(T.leaf x).density U := by
  rw [Deck.density,Deck.density,forced_only,charged,mul_smul_comm]
  congr 1
  ring

theorem combined (T : Taste X o P Γ) (H : Compulsory X Γ G n) (L : Rows X Γ G n)
    (x : X) (U : Config G n) (s h : Poly Γ) (hs : s.part Γ.quiet=0) (hh : h.part Γ.quiet=0)
    (active : ((replace T H).leaf x).Active) (old : Summable (fun i => (T.leaf x).contents.ray i U))
    (rows : HasSum (wave L P.p x U) s) (hard : ((replace T H).leaf x).contents.cluster U =
      Poly.pass h*(T.leaf x).contents.cluster U) :
    ((append L (replace T H)).leaf x).density U=Poly.pass (s+h)*(T.leaf x).density U := by
  rw [density L (replace T H) x U old rows active hs,cluster_density T H x U h hard,
    Next.Rank.Exponential.pass_add _ _ hs hh,mul_assoc]

structure Invoice (F E : Taste X o P Γ) (D : X→ Config G n→Poly Γ) where
  soft : Rows X Γ G n
  hard : X→ Config G n→Poly Γ
  quiet (x U) : (hard x U).part Γ.quiet=0
  formalForced : Compulsory X Γ G n
  residualForced : Compulsory X Γ G n
  formal_active (x) : ((replace F formalForced).leaf x).Active
  residual_active (x) : ((replace E residualForced).leaf x).Active
  formal_sum (x U) : Summable (fun i => (F.leaf x).contents.ray i U)
  residual_sum (x U) : Summable (fun i => (E.leaf x).contents.ray i U)
  masked (x U) : HasSum (wave soft P.p x U) (D x U-hard x U)
  formal_cluster (x U) : ((replace F formalForced).leaf x).contents.cluster U =
    Poly.pass (-(hard x U))*(F.leaf x).contents.cluster U
  residual_cluster (x U) : ((replace E residualForced).leaf x).contents.cluster U =
    Poly.pass (hard x U)*(E.leaf x).contents.cluster U

structure Pair (F E : Taste X o P Γ) (D : X→ Config G n→Poly Γ) where
  formal : Taste X o P Γ
  residual : Taste X o P Γ
  ordinary : X→ Config G n→Poly Γ
  formal_density (x U) : (formal.leaf x).density U=Poly.pass (-(D x U))*(F.leaf x).density U
  residual_density (x U) : (residual.leaf x).density U=Poly.pass (D x U)*(E.leaf x).density U
  formal_log (x U) : (formal.leaf x).log U=(F.leaf x).log U-ordinary x U
  residual_log (x U) : (residual.leaf x).log U=(E.leaf x).log U+ordinary x U

variable {F E : Taste X o P Γ} {D : X→ Config G n→Poly Γ} (H : Invoice F E D)

def ordinary (x : X) (U : Config G n) : Poly Γ :=
  D x U-H.hard x U

private theorem quiet (zero : ∀ x U,(D x U).part Γ.quiet=0) (x : X) (U : Config G n) : (ordinary H x U).part Γ.quiet=0 := by
  rw [ordinary,Next.Rank.Exponential.part_sub,zero,H.quiet,sub_self]

private theorem neg (x : X) (U : Config G n) : HasSum (wave (negative H.soft) P.p x U) (-ordinary H x U) := by
  exact (H.masked x U).neg.congr_fun (fun i=>negative_wave H.soft P.p x U i)

def realize (zero : ∀ x U,(D x U).part Γ.quiet=0) : Pair F E D where
  formal := append (negative H.soft) (replace F H.formalForced)
  residual := append H.soft (replace E H.residualForced)
  ordinary := ordinary H
  formal_density x U := by
    have h := combined F H.formalForced (negative H.soft) x U
      (-ordinary H x U) (-(H.hard x U))
      (by rw [Poly.part_neg,quiet H zero,neg_zero]) (by rw [Poly.part_neg,H.quiet,neg_zero])
      (H.formal_active x) (H.formal_sum x U) (neg H x U) (H.formal_cluster x U)
    have e : -ordinary H x U + -(H.hard x U) = -(D x U) := by unfold ordinary; abel
    simpa only [e] using h
  residual_density x U := by
    have h := combined E H.residualForced H.soft x U
      (ordinary H x U) (H.hard x U) (quiet H zero x U) (H.quiet x U)
      (H.residual_active x) (H.residual_sum x U) (H.masked x U) (H.residual_cluster x U)
    simpa only [ordinary,sub_add_cancel] using h
  formal_log x U := by
    rw [log (negative H.soft) (replace F H.formalForced) x U (H.formal_sum x U) (neg H x U),
      forced_only,sub_eq_add_neg]
  residual_log x U := by
    exact log H.soft (replace E H.residualForced) x U (H.residual_sum x U) (H.masked x U)

end YM.Integration.WilsonLimitConstruction.FundedMarkedFieldSplit
end
