import YM.Integration.WilsonPhysicalHistoryWalletTape

/-! The complete original signed source at a held physical placement, with
its measured exponential, hard share, and contracting original wallet. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryWalletDeposit
open Function Filter MeasureTheory Lattice RG RG.Supply Wilson Source Labels
open Next.Foundations PhysicalNext.Repeat.Legato Pressure RGComparison.Core16.Spool
open FVA1Physical.Wilson FVA1Physical.Marked FVA1Physical.Round2.Curvature
open WilsonReportForwardTransfer WilsonConditionalTaylorLabels WilsonOffsetJointWick
open WilsonPhysicalHistoryWalletExperiment
open scoped BigOperators Classical
variable {G : Gauge}

def anchor (R : Run G) {per j u : ℕ} (ju : j ≤ u) (b : Site (R.family.side (u+1) per)) :
    Site (R.family.side j per) :=
  anchorTape R per u ((R.family.path.levels.clock.op u per).ratio.parent b) j ju

def birth (R : Run G) {N per u : ℕ} (a : Roster G) (s : Finset (Fin a.length))
    (o : Fin a.length→Site (R.family.side (u+1) per)) (i : Fin a.length)
    (y b : Site (R.family.side (u+1) per)) (part : Bool) : ℝ :=
  measuredBirth R (cover a s) N per u b (seated a s o i y) part (reach b (seated a s o i y))

def signal (R : Run G) {N per j u : ℕ} (ju : j ≤ u) (a : Roster G) (s : Finset (Fin a.length))
    (o : Fin a.length→Site (R.family.side (u+1) per)) (i : Fin a.length)
    (y : Site (R.family.side (u+1) per)) (part : Bool) : Config G (R.family.side j per)→ℂ :=
  exterior (C:=R.family) (N:=N) (ju.trans u.le_succ)
    (fun U=>(↑(look part (tally (packet ⟨a,s⟩) (seated a s o i y) U)):ℂ))

def Registered (R : Run G) {N per j u : ℕ} (ju : j ≤ u) (a : Roster G) (s : Finset (Fin a.length))
    (o : Fin a.length→Site (R.family.side (u+1) per)) (i : Fin a.length)
    (y b : Site (R.family.side (u+1) per)) (part : Bool)
    (Q : Coefficient ((frames G).level 0) (R.family.side j per)) : Prop :=
  let P:=R.family.path.rep N per j
  let z:=anchor R ju b
  Q.Format z (hol G) P ∧ Q.remBound z P (Push.Local.kappa R.family.path j)
      (fiberRate R j u * birth R (N:=N) a s o i y b part) ∧
    Q.density z (localSection G 0) P=(fun W=>(P.eval W:ℂ)*signal R (N:=N) ju a s o i y part W) ∧
    ∀W,signal R (N:=N) ju a s o i y part W=Q.exponentialEntry z (localSection G 0) P W+forcedShare Q P W

/-- The original all-config signed physical wallet, on the same normalized
posterior as the growing-window telescope, at the requested held placement. -/
theorem issued (R : Run G) (simple : G.Simple) {N per j u : ℕ} (live : u<N) (ju : j ≤ u)
    (a : Roster G) (s : Finset (Fin a.length)) (o : Fin a.length→Site (R.family.side (u+1) per))
    (i : Fin a.length) (y b : Site (R.family.side (u+1) per)) (part : Bool) (late : opens R a ≤ j) :
    ∃Q, Registered R (N:=N) ju a s o i y b part Q := by
  obtain ⟨early,start,ready⟩ := admitted R a s late ju
  obtain ⟨Q,sh,hard,dens,full⟩ := physical_wallet_tape R simple live start (cover a s) ready b
    (seated a s o i y) part (reach b (seated a s o i y)) (reaches b _) j ju early
  let φ : Config G (R.family.side (u+1) per)→ℝ := fun U=>look part (tally (freshLamps (cover a s)) (seated a s o i y) U)
  have same := WilsonPhysicalHistoryWalletTape.born R ju live φ
  refine ⟨Q,sh,hard,?_,?_⟩
  · apply dens.trans
    funext W
    exact congrArg (fun v:ℂ=>(↑((R.family.path.rep N per j).eval W):ℂ)*v) (congrFun same W)
  · intro W
    exact (congrFun same W).symm.trans (full W)

/-- The hard charge contracts at every earlier date. Its positivity is earned
from the measured coefficient's original signed remainder invoice. -/
theorem contracted (R : Run G) {N per j u : ℕ} {ju : j ≤ u} {a : Roster G} {s : Finset (Fin a.length)}
    {o : Fin a.length→Site (R.family.side (u+1) per)} {i : Fin a.length}
    {y b : Site (R.family.side (u+1) per)} {part : Bool}
    {Q : Coefficient ((frames G).level 0) (R.family.side j per)}
    (q : Registered R (N:=N) ju a s o i y b part Q) :
    0 ≤ fiberRate R j u*birth R (N:=N) a s o i y b part ∧
      fiberRate R j u*birth R (N:=N) a s o i y b part ≤ birth R (N:=N) a s o i y b part := by
  obtain ⟨x,y,hx,hy,paid,_⟩ := q.2.1
  have nonneg := (add_nonneg hx hy).trans paid
  have rate := fiberRate_bounds R j u
  exact ⟨nonneg,mul_le_of_le_one_left (nonneg_of_mul_nonneg_right nonneg rate.1) rate.2⟩

/-- The original rooted support invoice, wherever the entire observed footprint
and its authentic section extension fit the actual old regularity aperture. -/
theorem shelved (R : Run G) {N per j u : ℕ} (live : u<N) (ju : j ≤ u)
    (a : Roster G) (s : Finset (Fin a.length)) (o : Fin a.length→Site (R.family.side (u+1) per))
    (i : Fin a.length) (y b : Site (R.family.side (u+1) per)) (part : Bool) (late : opens R a ≤ j)
    (fit : reach b (seated a s o i y)+LocalLTE.Vault.terr G (ceiling a) ≤ (R.family.path.rep N per (u+1)).p.B)
    {Q : Coefficient ((frames G).level 0) (R.family.side j per)} (q : Registered R (N:=N) ju a s o i y b part Q) :
    fiberRate R j u*birth R (N:=N) a s o i y b part ≤
      fieldShelf (cover a s) (R.alloy.B.a.params (u+1)) (reach b (seated a s o i y)) :=
  (contracted R q).2.trans (purchased_signed_birth R live (admitted R a s late ju).2.1 (cover a s) b
    (seated a s o i y) part (reach b (seated a s o i y)) (reaches b _) fit)

end YM.Integration.WilsonPhysicalHistoryWalletDeposit

