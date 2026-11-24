import YM.MS.Local.Coh
import YM.MS.Local.Diagonal
/-!
# Rank-r homogeneous cohomology in the kernel comparison

Local $Q$ on marks, **no total derivative removal**, at degree zero. Gives
span of ordered tensors of individually closed A-one-stars (with total
symmetry preserved on the projection data), differing only by a local
exact primitive in this comparison. Needed to use just the physical lifts.
Color/reality when desired handled separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Local.BV
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor Submodule MatrixLet
open Landau Detect
open Complex (I)
open scoped Topology ContDiff
open Woven
variable {G: Gauge} {f : Grade G} {F : Law G} {h q k : ℤ} {r d : ℕ}

namespace Woven
-- degree zero survivors

variable {V : Mover G} (X : Calib (MatrixLet.one V) k)
include X in
lemma split_carry (ht:h≤k) (hp : SplitS V h 0 r 0 F): F∈Carry G h r:= by
   obtain ⟨p,a,b,v,H,H1,H2,H3,rfl⟩ :=hp; by_cases hz:line r p=0; rw [hz]; exact zero_mem _
   have hv i: v i=0:= by have hp : v i ≤ _:= Finset.single_le_sum (f:=v) (s:=Finset.univ) (fun _ _=> Nat.zero_le _) (mem_univ i); omega
   have hx i: a i ≤ k:= (Finset.single_le_sum (fun j _=> (H j).1) (mem_univ i)).trans (by rwa [H1])
   have ht i : Count V (p i)=0:= ((H i).2.2.2).trans (by simp [hv i])
   have he i:0 ≤ b i:= by
       by_contra! h'; exact compose_line hz i (((X.annul (H i).2.1 (hx i) h').symm).trans (ht i))
   refine subset_span (mem_setOf.mpr ⟨p,a,fun i=>?_, H1,rfl⟩)
   have hw i: b i=0:= by have ht : b i ≤0:= H2 ▸ Finset.single_le_sum (s:=Finset.univ) (f:=b) (fun j _=> he j) (mem_univ i); exact le_antisymm ht (he i)
   exact ⟨hw i ▸ (H i).2.1,(X.exact_q (hx i) (H i).2.1).symm.trans (by rw [ht]; simp)⟩
-- Euler recursion projects N eigenvalues ≤r.
variable (V)
def filterOut : ℕ→ Module.End ℂ (Law G)
   | 0=> LinearMap.id
   | n+1=> ((LinearMap.id-((n+1:ℕ):ℂ)⁻¹ • Nop V).comp (filterOut n))
lemma filter_zero (F:Law G): filterOut V 0 F=F:=rfl
lemma filter_eq (n) (F:Law G): filterOut V (n+1) F = filterOut V n F- ((n+1:ℕ):ℂ)⁻¹ • Nop V (filterOut V n F):=rfl
variable {V} {n:ℕ}
lemma project_zero (hN : Nop V F=0): filterOut V n F= F:=by
    induction n with
    | zero=>rfl
    | succ n ih=> rw [filter_eq,ih,hN]; simp
lemma scalar_limb (hN : Nop V F=(d:ℂ) • F) (i:ℕ) : ∃ c:ℂ, filterOut V i F=c • F:= by
   induction i with
   | zero=>exact ⟨1,(one_smul ℂ F).symm⟩
   | succ i ih=> obtain ⟨c,hc⟩:=ih; rw [filter_eq,hc,map_smul,hN,smul_smul,smul_smul,← sub_smul]; exact ⟨_,rfl⟩
lemma project_n (hN : Nop V F=(d:ℂ) • F) (hd: 0<d) (hp : d ≤ n): filterOut V n F=0:= by
   induction n, hp using Nat.le_induction with
   | base=> cases d with
     | zero=> omega
     | succ d=>
        obtain ⟨c,h⟩:= scalar_limb hN d; have hm : ((d+1:ℕ):ℂ)≠0:= Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d)
        rw [filter_eq,h,map_smul,hN,← smul_assoc c,smul_eq_mul,mul_comm c,mul_smul,inv_smul_smul₀ hm]; simp
   | succ i h IH=> rw [filter_eq, IH]; simp
lemma all_kept (X : Calib (MatrixLet.one V) h) : Bed G h 0 r ≤ Submodule.comap (filterOut V r) (Carry G h r):= by
   rw [Canvas V X le_rfl,frieze,span_le]; rintro F ⟨d,hd⟩; have hm:= Woven.rate X le_rfl hd; rw [SetLike.mem_coe, Submodule.mem_comap]; cases d
   · rw [project_zero (by simpa only [Nat.cast_zero,zero_smul] using hm)]; exact split_carry X le_rfl hd
   rw [project_n hm (Nat.succ_pos _) (cap_occu hd)]; exact zero_mem _

lemma N_comm (X : Calib (MatrixLet.one V) h) (hf:F∈ Bed G h q r): Nop V (natQ F)=natQ (Nop V F) := by
   simp only [Nop_at,q_zero hf, map_zero,map_add]; have hv : V.Q F∈ Bed G h (q+(-1)) r:= enters (V:=V) (H:=h) (fun k hk m g hg=> X.price k m g hk hg) le_rfl hf
   rw [q_zero hv]; simp

lemma cut_mem (X: Calib (MatrixLet.one V) h) (hf:F∈Bed G h q r) : filterOut V n F∈ Bed G h q r:=by
    induction n with
    | zero=> exact hf
    | succ n IH=> rw [filter_eq]; exact sub_mem IH (smul_mem _ _ (N_price X le_rfl IH))

variable (p : Sector (Lane4 G)) -- use base
lemma frieze_Q (X: Calib (MatrixLet.one V) h) (hp:F∈ Bed G h q r) (hq:natQ F=0): natQ (filterOut V n F)=0:= by
   induction n with
   | zero=> exact hq
   | succ n IH=> rw [filter_eq,map_sub,map_smul,← N_comm X (cut_mem X hp), IH]; simp
lemma filter_sym (hx:sym F): sym (filterOut V n F):= by
   induction n with
   | zero=> exact hx
   | succ n IH=> rw [filter_eq,Nop_at]; exact IH.sub (((show sym (natQ _) from Gof.sym (V.sym IH)).add (V.sym (Gof.sym IH))).smul _)
lemma missed (X:Calib (MatrixLet.one V) h) (hp:F∈Bed G h q r) (hq:natQ F=0) (hx:sym F): ∃ G'∈Bed G h (q-1) r, sym G' ∧ F= filterOut V n F+natQ G' := by
   induction n with
   | zero=> exact ⟨0,zero_mem _,Koszul.Symm.zero,by rw [filter_zero,map_zero,add_zero]⟩
   | succ n IH=>
       obtain ⟨T,ht,hu,hh⟩:= IH; let g:= filterOut V n F; let c := ((n+1:ℕ):ℂ)⁻¹
       have hB : g∈Bed G h q r:= cut_mem X hp; have hS : sym g:= filter_sym hx
       have h' : V.Q g∈Bed G h (q+(-1)) r:= enters (V:=V) (H:=h) (fun k hk m g hg=> X.price k m g hk hg) le_rfl hB
       refine ⟨T+c • V.Q g, add_mem ht (smul_mem _ _ (show V.Q g ∈ Bed G h (q-1) r from h')),hu.add ((V.sym hS).smul _),?_⟩
       rw [filter_eq,Nop_at,frieze_Q X hp hq,map_zero,map_add,map_smul]; change F= g- c • (natQ (V.Q g)+0)+(natQ T+c • natQ (V.Q g)); exact hh.trans (by unfold g; abel)
end Woven

open Woven
theorem class_free (hF:F∈Bed G h 0 r) (he:natQ F=0) (ht:sym F):∃ f∈ Carry G h r, ∃ H∈ Bed G h (-1) r, sym f ∧ sym H ∧ F=f+natQ H:= by
    obtain ⟨X,hX⟩:= walk G h; obtain ⟨p,hp,h,H⟩:= missed (n:=r) hX hF he ht
    exact ⟨filterOut X r F, all_kept hX hF,p,hp,filter_sym ht,h,H⟩
end YM.MS.Local.BV
