import YM.WilsonCoeffUV.Vacuum.Gain.DiagonalRows
import YM.Next.RANK.Coordinates

/-! Subtraction of the common ancestor of an actual fine cover site keeps
every occupied child's own digits at every intervening block. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialCellDigits
open Lattice WilsonCoeffUV.Bank
open scoped Classical
variable {I : Type*}

theorem packed (L : Side) (x : Cover) : L.val • parentC L x+lift (wrap L x)=x := by
  change (panel L Unit (parentC L x, wrap L x, ())).1=x
  rw [←patchwork (L:=L) ((x,()):Cover×Unit),Equiv.apply_symm_apply]

theorem slide (L : Side) (x v : Cover) :
    parentC L (x+L.val • v)=parentC L x+v ∧ wrap L (x+L.val • v)=wrap L x := by
  have eq : panel L Unit (parentC L x+v,wrap L x,())=(x+L.val • v,()) := by
    apply Prod.ext
    · change L.val • (parentC L x+v)+lift (wrap L x)=x+L.val • v
      rw [smul_add,add_right_comm,packed]
    · exact Subsingleton.elim _ _
  have decomp:=congrArg (panel L Unit).symm eq
  rw [Equiv.symm_apply_apply,patchwork] at decomp
  exact ⟨(congrArg Prod.fst decomp).symm,(congrArg (fun p => p.2.1) decomp).symm⟩

def ancestor (S : Schedule) {w K : ℕ} (cut : w ≤ K) (o : I → Cover) (anchor : I) : Cover :=
  parentC (S.toDepth cut 0).count (o anchor)

def residual (S : Schedule) {w K : ℕ} (cut : w ≤ K) (o : I → Cover) (anchor i : I) : Cover :=
  o i-(S.toDepth cut 0).count.val • ancestor S cut o anchor

theorem pivot (S : Schedule) {w K : ℕ} (cut : w ≤ K) (o : I → Cover) (anchor : I) :
    residual S cut o anchor anchor = lift (wrap (S.toDepth cut 0).count (o anchor)) := by
  dsimp only [residual,ancestor]
  have h:=packed (S.toDepth cut 0).count (o anchor)
  exact sub_eq_iff_eq_add.mpr (h.symm.trans (add_comm ..))

theorem relative (S : Schedule) {w K : ℕ} (cut : w ≤ K) (o : I → Cover) (anchor i j : I) :
    residual S cut o anchor i-residual S cut o anchor j = o i-o j := by
  simp only [residual,sub_sub_sub_cancel_right]

theorem original (S : Schedule) {w j K : ℕ} (lower : w ≤ j) (upper : j ≤ K)
    (o : I → Cover) (anchor i : I) :
    let l := (S.toDepth upper 0).count
    let r := (S.toDepth lower 0).count
    let o' := residual S (lower.trans upper) o anchor i
    let v := ancestor S (lower.trans upper) o anchor
    parentC l o'=parentC l (o i)-r.val • v ∧ wrap l o'=wrap l (o i) := by
  intro l r o' v
  have size : (S.toDepth (lower.trans upper) 0).count.val=l.val*r.val :=
    Next.Rank.Station.size_comp (S.toDepth lower 0) (S.toDepth upper 0) _
  have eq : o'=o i+l.val • (-(r.val • v)) := by
    dsimp only [o',residual,v]
    rw [size,mul_smul,smul_neg,sub_eq_add_neg]
  rw [eq]
  exact slide l (o i) (-(r.val • v))

theorem finite (S : Schedule) {w j K : ℕ} (lower : w ≤ j) (upper : j ≤ K)
    (per : ℕ) (o : I → Cover) (anchor i : I) :
    let g := S.toDepth upper per
    g.residue (wrap (S.side K per) (residual S (lower.trans upper) o anchor i)) =
      g.residue (wrap (S.side K per) (o i)) := by
  intro g
  rw [Ratio.residue_wrap,Ratio.residue_wrap]
  exact (original S lower upper o anchor i).2

end YM.Integration.WilsonPositionProgramTrialCellDigits
