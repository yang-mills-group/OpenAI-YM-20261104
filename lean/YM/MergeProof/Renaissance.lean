import YM.Frontier6.Trajectory.Transport
import YM.MergeProof.License
import YM.MergeProof.Meringue




/-!
# ONE shared linear column family step

Coarse reference coordinate isn't obtained by fitting an expectation.
Rebase using injectivity of the **previous** readout, spend the atoms on
the *complete* column, then choose once and linearly combine the entire
paid column, incl forced parts. Necessary for a cone step: bounds are in
terms of *current* primary size (and remainders), not the sum of unsubtracted
uses of possibly huge original coefficients at earlier bases. Reserve K,
roomCost and Bank for true swollen costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Lattice Wilson RG Source Function Filter Set MeasureTheory Bid Labels Extra.Histories Motion PhysicalNext.Repeat Lotus
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d}
variable (B : SectionData F) (H : History G) (N p : ℕ) (A : Hol G)

variable (W: Worth)
theorem repriseQ (m : ℕ) (V : Voice F H p (m+1)) {η C : ℝ}
    (h : H.Selected) (hm : m<N) (hq : Heard B H N p A (m+1) V) (hw : roomCost H.levels W)
    (hb : Bank W H.levels) (T : Heading F)
    (D : GaugeDoor (H.rep N p (m+1)) (H.rep N p m))(hD: SoundDoor (H.levels.clock.op m p) D)
    (Xk : Set Wing){t : ℝ}(hxt : 0 ≤ t) (ht : Stampede B H N p m A D C η t T Xk) (hk : Set.Finite Xk)
    (κk: Real.sqrt (H.levels.clock.forcedAllowance (m+1))≤1)(he : Buys H F W m C η)
    (K: Planned.GuardedAtom.Guard.Keeper (H.rep N p (m+1)).p (H.rep N p (m+1)).activities) (hkP:∀ i,Xk (.gasKey (cart K i)))(hr : Chorus H N p (m+1) V)(hT:B.Sound A)(hN:∀ U,(H.rep N p (m+1)).eval U ≠ 0):
    let L:= H.S.block m
    ∃ Q : Voice F H p m, Heard B H N p A m Q ∧ Responds B H N p W m V Q ∧ Chorus H N p m Q∧
       ∃ Y:Set Wing,Y.Finite∧∀ v,let I:= V.plays v; let R:=H.rep N p (m+1); let Z:=V.index v
       Tale Y 0 0 ((L.val:ℂ)^d) (I.exponentialEntry 0 B R) (profile R.activities I.forced) (profile (H.rep N p m).activities (Q.plays v).forced) (Z 0) ((orbitCost F*F.coeffSize Z)*(t+2*(H.levels.params (m+1)).columns)) (Q.charge v) D := by
  obtain ⟨coarse, heard, responds, coeff, chorus, tale⟩ :=
    YM.MergeProof.repriseCoeff B H N p A W m V h hm hq hw hb T D hD Xk hxt ht hk
      κk he K hkP hr hT hN
  exact ⟨coarse, heard, responds, chorus, tale⟩

end YM.MergeProof
