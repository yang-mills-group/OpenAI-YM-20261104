import YM.Integration.WilsonRegisteredSealedReflections

/-! A reflected roster of two real adjacent-date withdrawals reaches the
original terminal single-cell invoice on the actual lifted field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredSealedRoot
open Function Filter Set MeasureTheory Lattice Wilson RG Next.Rank Push.GridApprox Cells WardBin.Wheels
open OPE.Therm OPE.Therm.ReplicaChessboard PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Accent Extra.Trajectories QLocalPhysicalPathKernel
open WilsonPositionOriginalDressedQFailedPath
open scoped ENNReal Topology BigOperators Classical
variable {G:Gauge}
theorem root (R:Run G){station i N per:ℕ}(ji:station ≤ i)(up:i ≤ N)(r:ℕ)
    (space:room R.family.path.levels station i r)(F:Config G (R.family.side i per) → ℂ)
    (loc:Interior (window 0 r) F):
    let A:=R.family.path; let M:=tilesAt R.family.S per ji
    ‖∫W,M.fullAt (fun _=>F) W ∂scene A N per i‖^(Fintype.card M.Cell:ℝ)⁻¹ =
    (center R.family.S per (ji.trans up) 0).rootTest (R.family.beta N per) (backTo A N per up F):=by
  intro A M
  let T:=center R.family.S per (ji.trans up) 0
  have e:Envelope (M.fullAt fun _=>F):=Envelope.prodC Finset.univ (fun j=>M.copy j F)
    (fun j _=>cylinder_env (copy_window A per ji j r F loc))
  have top:Interior (T.chamber 0) (backTo A N per up F):=by
    apply Interior.enlarges (backTo_local A N per ji up 0 r (F:=F) ?_)
      (room_fits per A.levels r ji up space 0)
    rw [anchor,←Ratio.root_embed,map_zero];exact loc
  have sel:A.Selected:=R.makes.wilson
  have eq:(∫W,M.fullAt (fun _=>F) W ∂scene A N per i)=moment (R.family.beta N per)
      (T.fullAt (fun _=>backTo A N per up F)):=by
    rw [←retro sel up le_rfl (M.fullAt (fun _=>F)) e,ReplicaChessboard.lift_array ji up r space (fun _=>F) (fun _=>loc),
      onstage sel _ (T.manyIntegral _ _ (fun _=>top))]
  rw [eq]
  rfl

/-- On genuine dated fields, the only terminal input is the original
charged homogeneous joint birth with all regular and forced replicas. -/
theorem original (R:Run G){station i u N per:ℕ}(ji:station ≤ i)(live:i < N)(un:u ≤ N)(r q b:ℕ)
    (roomL:room R.family.path.levels station i r)
    (Q:Config G (R.family.side (i+1) per)  →  ℂ)(L:Config G (R.family.side i per)  →  ℂ)
    (hq:Interior (window 0 q) Q)(hl:Interior (window 0 r) L)
    (roomF:room R.family.path.levels station (i+1) b):
    let C:=R.family; let A:=C.path; let S:=tilesAt C.S per ji
    let T:=tilesAt C.S per (ji.trans (Nat.le_succ i))
    let F:=fun U=>Q U-backTo A N per (Nat.le_succ i) L U
    let Y:=backTo A N per live F
    Interior (window 0 b) F  →  Continuous Y  → 
    ∀ (o:Site (C.side station per) → Site (C.side u per))
    (regular:Site (C.side station per) → Config G (C.side u per) → ℂ)
    (forced:Site (C.side station per) → Box (C.side u per) → Config G (C.side u per) → ℂ)
    {w e f x y:ℝ}, 0<w  →  0≤e  → 
    Served (A.rep N per u) regular forced
      (actualJointBirth C
        (fun j=>(center C.S per (ji.trans live.le) 0).copy j Y) un)
      o (fun _=>w) e f  →  Vault (fun _=>w) regular forced x y  → 
    ‖∫ω:ConfigurationPath R per,(∏j:S.Cell,(T.copy j Q (ω (i+1))-S.copy j L (ω i)))
       ∂path C R.makes N per‖^(Fintype.card S.Cell:ℝ)⁻¹ ≤
    Real.exp ((C.S.a station / C.S.a u)^4*Vac.treasury A.levels u+(x+y+2*f))/w:=by
  intro C A S T F Y loc cont o regular forced w e f x y hw he served vault
  rw [WilsonRegisteredSealedReflections.original R live ji r q roomL (fun _=>Q) (fun _=>L)
    (fun _=>hq) (fun _=>hl)]
  apply (root R (ji.trans (Nat.le_succ i)) live b roomF F loc).le.trans
  exact ReplicatedSignedCellBound.of_served R.makes (ji.trans live.le) un Y cont
    o regular forced hw he served vault
end YM.Integration.WilsonRegisteredSealedRoot
