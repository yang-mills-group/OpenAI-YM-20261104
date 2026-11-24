import YM.Integration.WilsonThermometerOffsetPrimary
import YM.RG05Readout.Planes.Cover
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Anchors

/-! The one original inverse-calibrated microscopic column at an arbitrary
site, with its paid stored coefficient on that site's actual parent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOwnOffsetField
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Push.Local
open PhysicalNext.Repeat.Legato MergeProof Accent Trace.Physical ProjectorNext.Equivariance
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) (N p m : ℕ)

def primaryLetter (d : ℕ) : Letter d :=
  ⟨⟨0,Nat.zero_lt_succ _⟩,Classical.choice Planes.exists_letter⟩

theorem located (live : m ≤ N) (z : Site (R.family.side N p)) :
    address R N p m (digits R N p z) (N-m) (by omega) +
      anchor R.family.S p live ((R.family.S.toDepth live p).parent z) = z := by
  obtain ⟨q,rfl⟩ := Nat.exists_eq_add_of_le live
  have same (j i : ℕ) (eq : j=i) (hj : m+j ≤ m+q) (hi : m+i ≤ m+q) :
      address R (m+q) p m (digits R _ p z) j hj =
      address R (m+q) p m (digits R _ p z) i hi := by cases eq; rfl
  exact (congrArg (fun v => v + anchor R.family.S p live ((R.family.S.toDepth live p).parent z))
    (same (m+q-m) q (by omega) (by omega) le_rfl)).trans
    (WilsonThermometerOffsetResidue.original R p m q z)

theorem actual {base d : ℕ} {D : Rail R.family} {B : ℕ → ℕ → ℝ}
    {V : Sight R.family d p} {r : Emblems R.family d} (z : Site (R.family.side N p))
    (H : Enrolled R.makes D B base N p d (digits R N p z) V r)
    (entered : base ≤ m) (live : m ≤ N) (starts : ∀e≤d,R.family.ref e ≤ N)
    (y : Palette R.family d) :
    let P := R.family.path.rep N p m
    let t := primaryLetter d
    let o := (R.family.S.toDepth live p).parent z
    let x := (R.family.factory d N p).terminal (finer r live y t)
    ∃ X Q : Coefficient (R.family.labels.level d) (R.family.side m p),
      Germ.projection (R.family.labels.level d) R.family.params P.p.threshold 0 X=y t ∧
      X.Format 0 R.family.params P ∧ X.remBound 0 P (kappa R.family.path m) (B d m*size y) ∧
      Q.Format o R.family.params P ∧ Q.remBound o P (kappa R.family.path m) (B d m*size y) ∧
      Q.density o (R.family.localSection d) P=X.density 0 (R.family.localSection d) P ∘ Lattice.pull 1 o ∧
      Q.density o (R.family.localSection d) P=
        dyes R.family m N p live ((R.family.S.a m:ℂ)^d • R.family.O N p x z) := by
  intro P t o x
  let here := address R N p m (digits R N p z) (N-m) (by omega)
  obtain ⟨u,hp⟩ := (H.legal m entered live).capacity0 y
  rcases hp with @⟨X,F,fee,b,tail,cert,wallet,assembled,hx,hy,financed⟩
  have spare : fee t ≤ B d m*size y := ((Finset.single_le_sum
    (fun j _ => rem_nonneg (wallet j)) (Finset.mem_univ t)).trans
    (le_add_of_nonneg_right tail.nonneg)).trans financed
  have paid := rem_mono (wallet t) spare
  have filed : V m y (line t) = invoice (X t) 0 (R.family.localSection d) P :=
    (congrArg (fun S : Tape G (R.family.side m p) => S (line t)) assembled.symm).trans
      (together_line X F tail t)
  have read := WilsonThermometerOffsetPrimary.primary R N p m H entered live starts t rfl y
  let A := ((R.family.S.a m:ℂ)^d) • R.family.O N p x here
  have observed : (X t).density 0 (R.family.localSection d) P=dyes R.family m N p live A :=
    (congrArg Prod.fst filed.symm).trans read
  obtain ⟨δ⟩ := (R.makes.wilson.represents N p m live).good.labels.moves 1 o
  have origin : affine 1 o 0=o := by simp [affine]
  have form := shifted.format δ 0 (always_room R.family m p) (cert t)
  have quote := shifted.cap δ (cert t) paid
  have exactField := shifted.density δ (R.family.localSection d) (R.makes.sections d) (X t) 0
  let Q := shifted δ (X t)
  have hf : Q.Format o R.family.params P :=
    Eq.mp (congrArg (fun w => Q.Format w R.family.params P) origin) form
  have samePrice : permission P.p 1*(B d m*size y) = B d m*size y := by
    rw [show permission P.p 1=1 by unfold permission;rw [if_pos (by exact fun _=>rfl)],one_mul]
  have hq : Q.remBound o P (kappa R.family.path m) (B d m*size y) :=
    Eq.mp (congrArg₂ (fun w a => Q.remBound w P (kappa R.family.path m) a) origin samePrice) quote
  have moved : Q.density o (R.family.localSection d) P =
      (X t).density 0 (R.family.localSection d) P ∘ Lattice.pull 1 o :=
    (congrArg (fun w => Q.density w (R.family.localSection d) P) origin.symm).trans exactField
  refine ⟨X t,Q,(congrFun hy t).symm,cert t,paid,hf,hq,moved,?_⟩
  let a := anchor R.family.S p live o
  have place : A ∘ Lattice.pull 1 a = ((R.family.S.a m:ℂ)^d) • R.family.O N p x z := by
    funext U
    change (R.family.S.a m:ℂ)^d • R.family.O N p x here (Lattice.pull 1 a U) = _
    rw [Lattice.pull_one,R.family.translation,show here+a=z from located R N p m live z]
    rfl
  have cont : Continuous A := (R.family.continuousO ..).const_smul _
  exact moved.trans ((congrArg (fun f => f ∘ Lattice.pull 1 o) observed).trans
    ((WilsonPositionSeparatedProfileCenteredBranch.covariance R N p live o A cont).symm.trans
      (congrArg (dyes R.family m N p live) place)))

end YM.Integration.WilsonThermometerOwnOffsetField
end
