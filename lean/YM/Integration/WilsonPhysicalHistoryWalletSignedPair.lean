import YM.Integration.WilsonPhysicalHistoryWalletDeposit

/-! The original two signed wallets represent the full conditional of F*(D_z-D_e)
at every physical date, each on its real footprint and the same old vacuum. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryWalletSignedPair
open MeasureTheory Function Filter Finset Lattice RG RG.Supply Wilson Source Labels Next.Foundations
open PhysicalNext.Repeat.Legato OPE OPE.Therm WilsonCoeffUV RGComparison.Core16.Spool
open FVA1Physical.Wilson FVA1Physical.Marked FVA1Physical.Round2.Curvature
open WilsonReportForwardTransfer WilsonConditionalTaylorLabels WilsonOffsetJointRoster WilsonOffsetJointWick
open WilsonPhysicalHistoryWalletExperiment WilsonPhysicalHistoryWalletDeposit
open scoped BigOperators Classical
variable {G : Gauge}

def response (R : Run G) {N per j u : ℕ} (ju : j≤u) (a : Roster G) (s : Finset (Fin a.length))
    (o : Fin a.length→Site (R.family.side (u+1) per)) (i : Fin a.length)
    (z e : Site (R.family.side (u+1) per)) (part : Bool) : Config G (R.family.side j per)→ℂ :=
  exterior (C:=R.family) (N:=N) (ju.trans u.le_succ) (fun U=>
    (↑(look part (field a (s.erase i) o U*(one a i z U-one a i e U))):ℂ))

private theorem integrable (R : Run G) {N per u : ℕ} (live : u<N) (a : Roster G)
    (s : Finset (Fin a.length)) (o : Fin a.length→Site (R.family.side (u+1) per))
    (i : Fin a.length) (z : Site (R.family.side (u+1) per)) (part : Bool) :
    Integrable (fun U=>(↑(look part (tally (packet ⟨a,s⟩) (seated a s o i z) U)):ℂ))
      (scene R.family.path N per (u+1)) := by
  letI : IsProbabilityMeasure (scene R.family.path N per (u+1)) := probability R.makes.wilson live
  have continuous := Complex.continuous_ofReal.comp ((look part).continuous.comp
    (tally_cont (packet ⟨a,s⟩) (seated a s o i z)))
  exact continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem separated (R : Run G) {N per j u : ℕ} (live : u<N) (ju : j ≤ u)
    (a : Roster G) (s : Finset (Fin a.length)) (o : Fin a.length→Site (R.family.side (u+1) per))
    (i : Fin a.length) (hi : i∈s) (z e : Site (R.family.side (u+1) per)) (part : Bool) :
    response R (N:=N) ju a s o i z e part = fun W=>
      signal R (N:=N) ju a s o i z part W - signal R (N:=N) ju a s o i e part W := by
  let X := fun U=>(↑(look part (tally (packet ⟨a,s⟩) (seated a s o i z) U)):ℂ)
  let Y := fun U=>(↑(look part (tally (packet ⟨a,s⟩) (seated a s o i e) U)):ℂ)
  have joint : (fun U=>(↑(look part (field a (s.erase i) o U*(one a i z U-one a i e U))):ℂ)) =
      fun U=>X U-Y U := by
    funext U
    rw [← literal a s i hi o z e U,map_sub,Complex.ofReal_sub]
    rfl
  unfold response
  rw [joint]
  exact WilsonPhysicalHistoryWalletReceiver.minus R (ju.trans u.le_succ) live X Y
    (integrable R live a s o i z part) (integrable R live a s o i e part)

/-- In particular the complete fine detector stays inside each original Haar
conditional. Both measured exponentials and both forced shares are retained. -/
theorem original (R : Run G) (simple : G.Simple) {N per j u : ℕ} (live : u<N) (ju : j ≤ u)
    (a : Roster G) (s : Finset (Fin a.length)) (o : Fin a.length→Site (R.family.side (u+1) per))
    (i : Fin a.length) (hi : i∈s) (z e bz be : Site (R.family.side (u+1) per)) (part : Bool)
    (late : opens R a ≤ j) :
    ∃Qz Qe, Registered R (N:=N) ju a s o i z bz part Qz ∧ Registered R (N:=N) ju a s o i e be part Qe ∧
      fiberRate R j u*(birth R (N:=N) a s o i z bz part+birth R (N:=N) a s o i e be part) ≤
        birth R (N:=N) a s o i z bz part+birth R (N:=N) a s o i e be part ∧
      ∀W, let P:=R.family.path.rep N per j
          response R (N:=N) ju a s o i z e part W =
            (Qz.exponentialEntry (anchor R ju bz) (localSection G 0) P W -
             Qe.exponentialEntry (anchor R ju be) (localSection G 0) P W) +
            (forcedShare Qz P W - forcedShare Qe P W) := by
  obtain ⟨Qz,hz⟩ := issued R simple live ju a s o i z bz part late
  obtain ⟨Qe,he⟩ := issued R simple live ju a s o i e be part late
  refine ⟨Qz,Qe,hz,he,?_,?_⟩
  · rw [mul_add]
    exact add_le_add (contracted R hz).2 (contracted R he).2
  · intro W
    rw [separated R live ju a s o i hi z e part]
    dsimp only
    rw [hz.2.2.2 W,he.2.2.2 W]
    ring

end YM.Integration.WilsonPhysicalHistoryWalletSignedPair

