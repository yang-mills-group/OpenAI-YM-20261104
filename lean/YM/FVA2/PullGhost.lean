import YM.FVA2.GhostLift

/-!
# The action pulled along real coordinate planes

K slot transformation uses vector coordinates too, not covectors!
Comparison is by testing each coefficient of K,c after setting b=0.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Inversion
open Function Set Finset Filter Lattice MS MS.Koszul MS.Swirl MS.Native MS.Orbit MS.Orbit.Cog
open MS.Bare MS.Cylinder MS.Cylinder.Taylor Gauge
open PertExtension PertExtension.Orb
open Matrix FVA2.Ends ArrayMap Substitute Lag
open scoped Classical Topology ContDiff
variable {G:Gauge} {n:Side}

variable {P Q A B : Type} [Fintype P][Fintype Q][Fintype A][Fintype B]
  [DecidableEq P][DecidableEq Q][DecidableEq A][DecidableEq B]
variable (R : FVA2.Ends P A)(X K: Links G Q→L[ℝ] Links G P) (C: Links G B →ₗ[ℝ] Links G A)

abbrev ghostU : Matrix (Alphabet G P A) (Alphabet G Q B) ℂ:= intoC (moveL (coordinate X.toLinearMap) (coordinate K.toLinearMap) (coordinate C) 0)
local notation "U"=> ghostU X K C
local notation "V"=> ξ[U]
local notation "k!"=> coordinate K.toLinearMap
local notation "Z!"=> Focus.stone glowGraph (R.locus (G:=G))
local notation "κ"=> Letter.k
local notation "γ"=> Letter.c
local infixr:70 " ⚘ "=> product Letter.p
local notation "ι"=> tangentVec (A:=P) (G:=G)

lemma pinnedU : TieField U Letter.p Letter.p:= by unfold ghostU; rw [alignL]; exact preserves_p _ _ _ _
lemma ghost_ink (F:Links G P→ℝ)(hp:germ F) : V (ink tangentVec F)= ink tangentVec (F ∘ X):= kin_change X F _ _ _ hp
lemma ghostC_sum (j:Z G A) : V (atLetter (γ j))=∑ i':Z G B,((coordinate C j i':ℝ):ℂ) • atLetter (γ i'):= by unfold ghostU; rw [alignL, slotC]; rfl
lemma ghostK_sum (i:Z G P) : V (atLetter (κ i)) = ∑ j:Z G Q,(k! i j:ℂ) • atLetter (κ j):= by unfold ghostU; rw [alignL, slotK]; rfl
lemma ghostB_del (i:Z G A): V (atLetter (Letter.b i))=0:= by unfold ghostU; rw [alignL,slotB,into_zero]; simp
local notation "p_i"=> coordinate C
abbrev Vv (x: Lot G A)(a:Links G Q): Links G P:= R.flow (X a) x
omit [Fintype B] [DecidableEq P] [DecidableEq Q] [DecidableEq B] in
lemma costs_vel (t: Links G B) : germ (Vv R X (C t)):= by
   have hu : Vv R X (C t)=∑ i:Z G A, (projector i (C t)) • (R.locus i ∘ X):= by
      funext e; unfold Vv; nth_rw 1 [← Native.frame (C t)]; simp only [map_sum,map_smul,Finset.sum_apply]; rfl
   rw [hu]; rw [show (∑ i:Z G A, (projector i (C t)) • (R.locus i ∘ X))= fun a=> ∑ i:Z G A,(projector i (C t)) • R.locus i (X a) from funext fun x=> Finset.sum_apply _ _ _];
   refine ContDiffAt.sum fun i _=>?_ ; exact ((show ContDiffAt ℝ ω (R.locus i) (X 0) from (by rw [map_zero]; exact smooth_locus R i)).comp 0 X.contDiff.contDiffAt).const_smul  (projector i (C t))
lemma stone_pay (i:Z G P): V (Z! i)=∑ j:Z G B, atLetter (γ j) ⚘ ink tangentVec (projector i ∘ Vv R X (C (priv j))) := by
    rw [stone_terms,map_sum]; simp_rw [pair_change U (pinnedU X K C),ghostC_sum]
    simp_rw [ghost_ink X K C _ ((projector i).contDiff.contDiffAt.comp 0 (smooth_locus R _)),map_sum,
       map_smul, LinearMap.sum_apply, LinearMap.smul_apply, ← map_smul (product Letter.p _)]
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _=> ?_; rw [← map_sum]; apply congr_arg
    let f (x:Z G A):= (projector i ∘ R.locus x) ∘ X
    have hf (x:Z G A): germ (f x) := (show ContDiffAt ℝ ω (projector i ∘ R.locus x) (X 0) from (by rw [map_zero]; exact (projector i).contDiff.contDiffAt.comp 0 (smooth_locus R x))).comp 0 X.contDiff.contDiffAt
    have hh : (projector i ∘ Vv R X (C (priv j)))= ∑ x:Z G A, coordinate C x j • f x := by
       funext b; unfold Vv; simp only [Function.comp_apply]; rw [coordinate_in C j,map_sum,map_sum,Finset.sum_apply]; apply Finset.sum_congr rfl; intro x _; rw [map_smul,map_smul]; rfl
    rw [hh, ink_sum]; · simp_rw [ink_smul _ (hf _)]; rfl
    exact fun x _=> (hf x).const_smul (coordinate C x j)

abbrev Align (i:Links G Q)(v:Lot G B) (a:Links G Q) : ℝ:= chartPair (K i) (Vv R X (C v) a)
omit [Fintype A] [Fintype B] [DecidableEq A] in
lemma align_pay (i:Z G Q)(j:Z G B) : Align R X K C (priv i) (priv j)= ∑ x:Z G P,k! x i • (projector x ∘ Vv R X (C (priv j))):= by
    funext e; unfold Align chartPair; rw [Finset.sum_apply]; apply Finset.sum_congr rfl; intro x _; rw [coordinate_apply]; rfl
lemma align_germ (i:Z G Q)(j:Z G B) : germ (Align R X K C (priv i) (priv j)):= by
    rw [align_pay, show (∑ x:Z G P, k! x i • (projector x ∘ Vv R X (C (priv j)))) = fun a=>∑ x:Z G P,k! x i • projector x (Vv R X (C (priv j)) a) from funext fun _=> Finset.sum_apply _ _ _]; exact ContDiffAt.sum fun i _=> ((projector i).contDiff.contDiffAt.comp 0 (costs_vel R X C _)).const_smul _
lemma align_ink (i: Z G Q)(j: Z G B) : ink (tangentVec (A:=Q) (P:=B)) (Align R X K C (priv i) (priv j))= ∑ x:Z G P,(k! x i:ℂ) • ink tangentVec (projector x ∘ Vv R X (C (priv j))) := by
    rw [align_pay, ink_sum]; refine Finset.sum_congr rfl fun x _=> ink_smul _ ?_ _; exact (projector x).contDiff.contDiffAt.comp 0 (costs_vel R X C _); exact fun m _=> ((projector m).contDiff.contDiffAt.comp 0 (costs_vel R X C (priv j))).const_smul (k! m i)

lemma ghost_rep : V (∑ i:Z G P, atLetter (κ i) ⚘ Z! i) = ∑ j:Z G Q, atLetter (κ j) ⚘ ∑ v:Z G B, atLetter (γ v) ⚘ ink tangentVec (Align R X K C (priv j) (priv v)):= by
    rw [map_sum]; simp_rw [ pair_change U (pinnedU X K C), ghostK_sum,stone_pay, map_sum,
      map_smul, LinearMap.sum_apply, LinearMap.smul_apply,align_ink, map_sum]
    rw [Finset.sum_comm]; conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _=> ?_
    rw [ Finset.sum_comm ]; refine Finset.sum_congr rfl fun j _=>?_; simp_rw [map_smul]

lemma scaling (i: Z G Q)(j:Z G B)(a:ℝ) : ((a:ℂ) • ink (tangentVec (A:=Q) (P:=B)) (Align R X K C (priv i) (priv j)))= ink tangentVec (a • Align R X K C (priv i) (priv j)):= (ink_smul _ (align_germ R X K C i j) a).symm
lemma pay_action (S:Links G P→ℝ) (h:germ S) (a:ℝ) : V ((a:ℂ) • R.actionBody S)=
  ink tangentVec (a • (S ∘ X)) +∑ j: Z G Q, atLetter (κ j) ⚘ ∑ v: Z G B, atLetter (γ v) ⚘ ink tangentVec (a • Align R X K C (priv j) (priv v)) := by
  rw [map_smul,action_ghost,map_add,map_sub,ghost_rep];
  simp_rw [ map_sum V, pair_change U (pinnedU X K C), ghostB_del,map_zero, LinearMap.zero_apply,Finset.sum_const_zero,sub_zero]; rw [ghost_ink X K C S h,ink_smul tangentVec ((show ContDiffAt ℝ ω S (X 0) from (by rw [map_zero]; exact h)).comp 0 X.contDiff.contDiffAt), smul_add ];
  simp_rw [ ← scaling R X K C,map_sum, Finset.smul_sum,map_smul]


end YM.FVA2.Inversion
