import YM.FVAAlt2.Germ
import YM.FVAAlt2.Embedding

/-! Restrict individual super kernels to the actual Landau coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2
open Lattice Finset Pert.Orb SchemeRG11.Sway Function
open MS MS.Koszul MS.Native MS.Plane MS.Landau MS.Cylinder MS.Cylinder.Taylor MS.Book
open MS.Bare.Focus
open scoped ContDiff
set_option linter.unusedSectionVars false

section
variable {I J : Type}[Fintype I][Fintype J](L:Matrix J I ℂ)
lemma letters_matrix (i:I): pull L (atLetter i)=∑ j:J,L j i • atLetter j:=by
  classical
  funext w; cases w with
  | nil=> simp [atLetter]
  | cons a w=> cases w with
    | nil=>
      rw [pull_atLetter,Finset.sum_apply,sum_eq_single a]
      simp [speaks]
      exact fun j _ h=> by rw [Pi.smul_apply,notNamed j h.symm,smul_zero]
      simp
    | cons v w=>
      let f := atLetter (R:=ℂ) i
      have he: Book.rank 1 (pull L f):= (rank_hat 1).mpr (by rw [← pull_mask, (rank_hat 1).mp (Rails.letter i (v:=fun _=>1))])
      rw [Finset.sum_apply,sum_eq_zero]; swap; · exact fun _ _=>mul_zero _
      exact he _ (by rw [mod_int]; simp; omega)
end

variable {G:Gauge}{n:Side}
local notation "X" => Land G n
local notation "U" => ScalarGhost G n
variable {ι κ:Type} [Fintype ι][DecidableEq ι][Fintype κ][DecidableEq κ]
variable (A:Module.Basis ι ℝ (Land G n))(b:Module.Basis κ ℝ (ScalarGhost G n))

local notation "r" => Site n
local notation "L" => embeddingM A b
local notation "L'" => embeddingℝ A b
local notation "C" => Paper G (Site n)
local notation "K" => panel G (Site n)
local notation "D₀" => glow G (Site n)

abbrev dirA4 (A:Module.Basis ι ℝ (Land G n)) : Alpha ι κ→Land G n | avec i=>A i | .inr _=>0

lemma embedding_ink {f: Chart.City G (Site n) → ℝ}(hf: germ f):
    pull L (ink direction f)=ink (dirA4 A) (f ∘ spread G n):= by
  rw [ink_ctrl_one (dirA4 A) (spread G n) hf]
  have h(u:Chart.City G r): (∑ (i:Axis), ∑ j:G.ColorIndex, ∑ x:Site n, u (x,i) j • (priv ((x,i),j)))= u:= by
    have he := Native.frame u
    simp_rw [Fintype.sum_prod_type,projector_k] at he; 
    conv_lhs=> arg 2; intro i; rw [Finset.sum_comm]
    exact Finset.sum_comm.trans he
  have hu (i:Alpha ι κ): spread G n (dirA4 A i)=∑ x:Mode G n,L' i x • direction x:=by
    rcases i with a|c|c
    · rw [embAℝ A b a]; simp_rw [Fintype.sum_prod_type,Fintype.sum_option,Fintype.sum_bool]; simp [fields,direction, dirA4]; exact (h _).symm
    · rw [embGℝ A b c]; simp_rw [Fintype.sum_prod_type,Fintype.sum_option,Fintype.sum_bool]; simp [fields,direction, dirA4]
    rw [embKℝ A b c]; simp_rw [Fintype.sum_prod_type,Fintype.sum_option,Fintype.sum_bool]; simp [fields,direction, dirA4]
  rw [scale_pos direction ((⇑(spread G n)) ∘ dirA4 (κ:=κ) A) L' hu hf]; exact Eq.symm (eq_pull L _)

lemma pull_ghostPi (i:Eyes G (Site n)): pull L (MS.Bare.Focus.spark (panel G (Site n)) i)=∑ j:κ,(↑((b j).val i.1 i.2):ℂ) • atLetter (gh j):= by
  rw [MS.Bare.Focus.spark,letters_matrix,Fintype.sum_sum_type,Fintype.sum_sum_type]
  rw [show (C).plain ((K).KId i)=(((none,false),i.2),i.1) from rfl]
  simp_rw [show ∀ j, Sum.inl j=avec (κ:=κ) (j:ι) from fun _=>rfl,show ∀ j, Sum.inr (Sum.inl j)=gh (ι:=ι) (j:κ) from fun _=>rfl,show ∀ j, Sum.inr (Sum.inr j)=antigh (ι:=ι) (j:κ) from fun _=>rfl, embA,embG,embK]
  simp [fields]

lemma pull_KPi (i:Mind G (Site n)) :
    pull L (atLetter ((C).dual ((K).AId i)))=∑ j:κ, (↑((gM (barBasis b j)).val i.1 i.2):ℂ) • atLetter (antigh j):= by
  --
  rw [letters_matrix, Fintype.sum_sum_type, Fintype.sum_sum_type]
  rw [show (C).dual ((K).AId i)=(((some i.1.2,true),i.2),i.1.1) from rfl]
  simp_rw [show ∀ j, Sum.inl j=avec (κ:=κ) (j:ι) from fun _=>rfl,show ∀ j, Sum.inr (Sum.inl j)=gh (ι:=ι) (j:κ) from fun _=>rfl,show ∀ j, Sum.inr (Sum.inr j)=antigh (ι:=ι) (j:κ) from fun _=>rfl, embA,embG,embK]
  simp [fields]
lemma pull_BPi (i:Eyes G (Site n)): pull L (atLetter ((C).dual ((K).KId i)))=0:=by
  rw [letters_matrix,Fintype.sum_sum_type,Fintype.sum_sum_type]
  rw [show (C).dual ((K).KId i)=(((none,true),i.2),i.1) from rfl]
  simp_rw [show ∀ j, Sum.inl j=avec (κ:=κ) (j:ι) from fun _=>rfl,show ∀ j, Sum.inr (Sum.inl j)=gh (ι:=ι) (j:κ) from fun _=>rfl,show ∀ j, Sum.inr (Sum.inr j)=antigh (ι:=ι) (j:κ) from fun _=>rfl, embA,embG,embK]
  simp [fields]
end YM.FVAAlt2
