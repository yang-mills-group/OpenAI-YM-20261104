import YM.Integration.WilsonIndependentPublicFreeTrain
import YM.FVAAlt2.Periodic.Primary

/-! Finite centered joint and conditional Gaussian matrices in the identical rooted tree chart. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000
namespace YM.Integration.WilsonIndependentPublicSpringKernel
open Lattice RG WilsonCoeffUV FreeResolvent Tree RegulatorIR RegulatorIR.Oracle RegulatorIR.Geometry
open RegulatorIR.Ledger RegulatorIR.Halo Precision
open scoped Matrix
variable {G:Gauge}{c f:Side}

private theorem extF {r:Ratio c f}{F T:Forest r}(h:F.up=T.up)(u:F.height=T.height):F=T:=by
  cases F
  cases T
  subst_vars
  rfl

theorem forest (S:StepData c f) : repeatF S=bios S :=by
  refine extF (F:=repeatF S) (T:=bios S) ?_ rfl
  funext x
  by_cases h:leaf S.ratio x
  · change shrinkAt (lift (S.ratio.residue x))=(if h:leaf S.ratio x then Bark.toward S.ratio x h else posDir 0)
    have active:(bad (lift (S.ratio.residue x))).Nonempty:=Bark.reserve S.ratio x h
    rw [dif_pos h,shrinkAt,dif_pos active]
    rfl
  · change shrinkAt (lift (S.ratio.residue x))=(if h:leaf S.ratio x then Bark.toward S.ratio x h else posDir 0)
    rw [dif_neg h,shrinkAt,dif_neg]
    intro available
    have hh:=not_ne_iff.mp (fun z=>h ((leaf_test S.ratio x).2 z))
    obtain ⟨i,hi⟩:=available
    have zeroCell:(lift (S.ratio.residue x))=0:= by rw [hh]; simp
    exact ((Finset.mem_filter.mp hi).2) (congrFun zeroCell i)

variable (P:Patch)(K:KernelChoices)(G:Gauge)(basis:Precision.Bed)
variable {σ α η:ℝ}{clip:Clip} (F:Hall basis σ α η clip)(Z:P.Branches K G)
variable (c:Side)(H:FaceRow)
private lemma matrix (kin:Precision.K (basis.metric.acts (c*P.L))=Precision.K (H.acts (c*P.L))) :
    fullMatrix G (avenue P K c) basis.metric=fullMatrix G (avenue P K c) H :=by
  unfold fullMatrix baseMatrix
  rw [kin]

/-- On the actual torus all massive and constrained lines are the same normalized covariance. -/
theorem heat (kin:Precision.K (basis.metric.acts (c*P.L))=Precision.K (H.acts (c*P.L)))
    (inverse:IsUnit (treeMatrix G (avenue P K c) (repeatF _) H).det) :
    ledgerRow (blockQ G P.L) (blockQ G P.L) (hearth P K G basis F Z) c=
      covariance G (avenue P K c) (repeatF _) H :=by
  classical
  let S:=avenue P K c
  let B:=stemF P c
  have ident:repeatF S=B:=forest S
  rw [show repeatF (avenue P K c)=B from ident] at inverse ⊢
  have tree : treeMatrix G S B basis.metric=treeMatrix G S B H :=
    congrArg (fun m=>m.submatrix (plant B) (plant B)) (matrix P K G basis c H kin)
  have inv:IsUnit (treeMatrix G S B basis.metric).det:=by
    rw [tree]
    exact inverse
  unfold covariance treeInverse FreeResolvent.resolve
  rw [zero_smul,add_zero,←tree]
  unfold hearth
  have hu:=savings P G
  have hv:=cafe P K G basis F Z
  have ht:=promised P K G
  rw [Ledger.lap _ _ _ _ (hu.lap hv) hu ht,Ledger.lap _ _ _ _ hu hv (effects P K G basis F Z).choose_spec.1,physicalP P K G]
  apply FVAAlt2.Primary.compress (renter P G c) (fullMatrix G S basis.metric) _ (treeMatrix G S B basis.metric) rfl inv
  have full:=(ortho_cable P K G basis F Z c).2
  rw [touches P K G basis F c] at full
  exact full

end YM.Integration.WilsonIndependentPublicSpringKernel
