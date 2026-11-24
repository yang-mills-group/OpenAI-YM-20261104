import YM.Integration.WilsonAllDateHarvestPhysical
import YM.RG05Readout.Flatten.Joints

/-! At an intermediate scale one physical birth leg is the original signed sum
over all of its living descendants, with the exact oriented bodies and prefactor. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestDescendants
open Function Filter Finset Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Many RG05Readout.View RG05Readout.Records
open RG05Readout.Flatten Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

private theorem compose {V W I:Type} {E:Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [Fintype I] [DecidableEq I] [AddCommGroup E] [Module ℂ E]
    (π:V→W) (ρ:I→V) (l:V→ℂ) (a:I→ℂ) (f:I→E):
    Many.combine π l (Many.combine ρ a f)=Many.combine (π ∘ ρ) (fun i=>l (ρ i)*a i) f:=by
  funext w
  unfold Many.combine
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (ρ i)]
  · rw [if_pos rfl,smul_smul]
    by_cases eq:π (ρ i)=w
    · rw [if_pos eq,if_pos (show (π ∘ ρ) i=w from eq)]
    · rw [if_neg eq,if_neg (show (π ∘ ρ) i≠w from eq),zero_mul]
  · intro v _ ne;rw [if_neg (Ne.symm ne),zero_smul,smul_zero]
  · simp

variable {G:Gauge} {C:Family G} {b m p N:ℕ} {W:Type} [DecidableEq W] [Fintype W]
variable (o:W→Site (C.side b p)) (E:W→Motion) (s:W→ℕ) (q:ManyStem C o b→Body)
variable (S:(j:W)→Emblems C (s j)) (x:(j:W)→Palette C (s j))
local notation "A" => Mine.tree o E
local notation "Λ" => (A).labelY
local notation "f" => WilsonAllDateHarvestPhysical.columns o E s q S x m N
local notation "v" => Launch (m:=m) s S x

theorem original {j:ℕ} (bj:b ≤ j) (jN:j ≤ N):
    Many.combine (Λ j) (fun z=>ratioX (C.S.toDepth bj p) (s (Λ j z))) (f j)=
      fun u=>clinic C p N (s u) (v u N) b (o u) (E u) (q ((Mine.remap o E).symm u)):=by
  revert jN
  induction j,bj using Nat.le_induction with
  | base=>
    intro _
    funext u; unfold Many.combine
    let α:=Mine.remap o E
    rw [Finset.sum_eq_single (α.symm u)]; rotate_left
    · intro a _ ne
      rw [if_neg (show Λ b a≠u from fun eq=>ne (α.injective (eq.trans (α.apply_symm_apply _).symm))),zero_smul]
    · simp
    rw [if_pos (show Λ b (α.symm u)=u from rfl)]
    have initial:ratioX (C.S.toDepth (le_refl b) p) (s (Λ b (α.symm u)))=1:=by
      unfold ratioX; rw [ratio_one (C.S.toDepth (le_refl b) p)]; simp
    dsimp only
    rw [initial,one_smul]
    unfold WilsonAllDateHarvestPhysical.columns
    rw [(headlines (N:=N) o E q).1]; rfl
  | succ j bj ih=>
    intro jN
    let π:=Prod.fst ∘ (A).narrows j bj
    let a:=fun z:ManyStem C o (j+1)=>budwgt C p j (s (Λ j (π z)))
    let l:=fun z:ManyStem C o j=>ratioX (C.S.toDepth bj p) (s (Λ j z))
    have step:f j=Many.combine π a (f (j+1)):=
      Records.pillar (le_refl N) A s (fun u=>precinct C p N (s u) (v u N)) (F:=headings o E q) bj jN
        ((headlines (N:=N) o E q).2 j bj jN)
    have names:(Λ j) ∘ π=Λ (j+1):=funext fun z=>((A).loyal j bj z).symm
    have cost:(fun z=>l (π z)*a z)=fun z=>ratioX (C.S.toDepth (bj.trans j.le_succ) p) (s (Λ (j+1) z)):=by
      funext z
      unfold l a
      rw [show Λ j (π z)=Λ (j+1) z from ((A).loyal j bj z).symm,chain_price]
      exact ratioX_mul _ _ _ _
    rw [← ih (j.le_succ.trans jN),step,compose _ π l a (f (j+1)),names,cost]

end YM.Integration.WilsonAllDateHarvestDescendants
