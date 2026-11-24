import YangMills.WilsonProof.NativeSupport.YM.MS.Heat.Mutual
import YM.MS.Book.Chants
/-!
# Typed derivation for Witt convolution (mark and unmarked) yielding effective source

Endomorphisms may be extended (on a sufficiently careful subspace) but this
 theorem uses only individual piece values on specified inputs. No D construction assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Heat.Signal
open Function Filter Set Finset Plane Koszul Flux MeasureTheory Book Convolve
open scoped Topology ContDiff
variable {E E': Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'][Module ℂ E']
abbrev LM (E F:Type*) [AddCommMonoid E][Module ℂ E][AddCommMonoid F][Module ℂ F]:= E→ₗ[ℂ] F
abbrev MH (E:Type*)[AddCommGroup E][Module ℂ E]:=LM E E
abbrev Pair (E:Type*)[AddCommGroup E][Module ℂ E]:= LM E (MH E)

structure GridR (E:Type*)[AddCommGroup E][Module ℂ E] where
   J : MH E -- Q+ Lap
   P : MH E -- dot-ordinary cycle
   L : MH E -- dot-Lap
   X : Pair E -- dot-ordinary tree
   C : Pair E -- Lap tree
   D : Pair E -- dot-Lap tree
namespace GridR
variable (K : GridR E)
-- encode algebra conditions on input vectors. no structure of E. Prove rising formulas.
def matCont (K : GridR E)(F : T E) := promote K.J F + (2:ℂ)⁻¹ • pairW K.C F F
def grow (K:GridR E)(F:T E):= promote K.P F + (2:ℂ)⁻¹ • pairW K.X F F
def res (K:GridR E)(F H:T E):= promote K.J H + pairW K.C F H
def lives (K:GridR E)(F H:T E):= promote K.P H + pairW K.X F H

variable (κ: LM E E')
-- require equalities not on full function.
def Tint (κ:LM E E')(f g:E): Prop := κ f=κ g
lemma Tint.smul {κ:LM E E'} {f g:E}(h:Tint κ f g)(u:ℂ): Tint κ (u • f) (u • g):= by simp only [Tint,map_smul,show κ f=κ g from h] -- h maybe not unfold
structure Elements (κ:LM E E')(K:GridR E)(F H:T E): Prop where
    linear (i:ℕ): κ (K.J (K.P (H i))+ K.L (H i))=κ (K.P (K.J (H i)))
    quad (i j: ℕ): κ (K.J (K.X (F i) (H j))+ K.D (F i) (H j)+K.C (K.P (F i)) (H j)+ K.C (F i) (K.P (H j)))=κ (K.P (K.C (F i) (H j))+K.X (K.J (F i)) (H j)+ K.X (F i) (K.J (H j)))
    press (i j k:ℕ): κ (K.C (K.X (F i) (F j)) (H k)+K.C (F i) (K.X (F j) (H k))+K.C (F j) (K.X (F i) (H k)))=κ (K.X (K.C (F i) (F j)) (H k)+ K.X (F i) (K.C (F j) (H k))+K.X (F j) (K.C (F i) (H k)))
variable {K κ}
local notation "L" => promote K.L
local notation "P" => promote K.P
local notation "J" => promote K.J
local notation "D" => pairW K.D
local notation "C" => pairW K.C
local notation "X" => pairW K.X
local notation "pb" => (2:ℂ)⁻¹
local notation "Z"=> promote κ
variable {F H:T E}
namespace Elements
variable (h:Elements κ K F H)
include h
lemma L0 : Z (J (P H)+ L H)=Z (P (J H)):= funext fun i=> h.linear i
lemma L1 : Z (J (X F H)+D F H+C (P F) H+C F (P H))=Z (P (C F H)+X (J F) H+X F (J H)) := by
   funext n; simp only [paired,promised,Pi.add_apply,map_sum,← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun i _=>h.quad i.1 i.2) -- map κ occurs outside
omit h in
private lemma crossing (Kx Ky:Pair E)(κ:LM E E')(F H:T E)(n:ℕ) : (2:ℕ) • promote κ (pairW Kx F (pairW Ky F H)) n=∑ i∈antidiagonal n,∑ j∈antidiagonal i.1, κ (Kx (F j.1) (Ky (F j.2) (H i.2))+ Kx (F j.2) (Ky (F j.1) (H i.2))):= by
    let D0 x y z:= κ (Kx (F x) (Ky (F y) (H z))); simp only [promised, paired,map_sum]; rw [Convolve.associate (fun x y z=> D0 x y z)];
    simp only [two_nsmul,map_add,Finset.sum_add_distrib]; congr 1; refine Finset.sum_congr rfl (fun i _=> ?_); exact (Finset.Nat.sum_antidiagonal_swap (n:=i.1) (f:=fun j=>D0 j.1 j.2 i.2)).symm
lemma L2 : Z (C (X F F) H+ (2:ℂ) • C F (X F H))=Z (X (C F F) H+(2:ℂ) • X F (C F H)) := by
    funext n; simp_rw [map_add,map_smul,Pi.add_apply]; rw [show (2:ℂ) • Z (C F (X F H))= (2:ℕ) • Z (C F (X F H)) by exact Nat.cast_smul_eq_nsmul .., show (2:ℂ) • Z (X F (C F H))= (2:ℕ) • Z (X F (C F H)) by exact Nat.cast_smul_eq_nsmul .., Pi.smul_apply, Pi.smul_apply]; rw [crossing,crossing]; -- plan
    simp only [paired,promised,map_sum,LinearMap.sum_apply,← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun i _=> Finset.sum_congr rfl (fun j _=> ?_)); simpa only [map_add,add_assoc] using h.press j.1 j.2 i.2

lemma lights : Z (res K F (lives K F H)+L H+D F H+C (grow K F) H)= Z (lives K F (res K F H)+X (matCont K F) H) := by
    have hz := h.L0; have hw := h.L1; have hu := congr_arg (pb • ·) h.L2
    unfold res grow lives matCont; simp only [map_smul,map_add,LinearMap.smul_apply, LinearMap.add_apply] at hu hw hz ⊢
    simp only [smul_add,smul_smul, inv_mul_cancel₀ (two_ne_zero (α:=ℂ)),one_smul] at hu; linear_combination (norm:=abel) hz + hw + hu
end Elements
-- bulk: last step 3×Θ.
variable (h:Elements κ K F F)
include h
lemma bright_mat
   (hx : Z (X F (J F))=Z (X (J F) F))
   (hy : Z (C F (X F F)) = Z (C (X F F) F))
   (ht : Z (X F (C F F))=Z (X (C F F) F)) :
    Z (J (grow K F) + L F + pb • (D F F+C F (grow K F)+C (grow K F) F)) = Z (lives K F (matCont K F)):= by
   have hm:= h.L0; have hL:= congr_arg (pb • ·) h.L1; have hX:=h.L2
   rw [map_add,map_add,map_smul,map_smul,← hy,← ht] at hX; replace hX : Z (C F (X F F))= Z (X F (C F F)):= by
       rw [show ∀ z:T E',z+(2:ℂ) • z=(3:ℂ) • z from fun z=> by nth_rw 1 [← one_smul ℂ z]; rw [← add_smul]; norm_num] at hX; rw [show ∀ z:T E',z+(2:ℂ) • z=(3:ℂ) • z from fun z=> by nth_rw 1 [← one_smul ℂ z]; rw [← add_smul]; norm_num] at hX; exact smul_right_injective (M:=T E') (by norm_num : (3:ℂ)≠0) hX -- possible API
   unfold matCont lives grow; simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_add, ← hx,←hy,hX] at hm hL ⊢;
   have hh (z:T E'): pb • z+pb • z=z:= by rw [← add_smul]; norm_num
   have hg:= congr_arg (pb • ·) (hh (Z (X F (C F F)))); simp only [smul_add] at hg; linear_combination (norm:=abel) hm + hL + hg + hh (Z (X F (J F))) -- sign
end GridR
end YM.MS.Heat.Signal
