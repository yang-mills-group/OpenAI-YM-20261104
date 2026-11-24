import YM.MS.Local.Occupation
import YangMills.WilsonProof.NativeSupport.YM.MS.Local.Recovery
/-!
# Shift homotopy at ordered products. No tensor algebra independence needed.

Use linear $Q$ (derivation), all elements in a tile of effective weight h.
`S` = N counts slots in split monomials. Inversion for integers immediate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Local.BV
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor Submodule MatrixLet
open Landau Detect
open Complex (I)
open scoped Topology ContDiff
variable {G: Gauge} {f : Grade G} {F : Law G} {h q H x y a b c : ℤ} {V A : Mover G}
    {r : ℕ}

namespace Woven

-- Enough to restrict product lines (can check only nonnegative weights).

lemma enters (hp : ∀ h≤H, ∀ q f, f ∈ yields h q → MatrixLet.one V f ∈ yields h (q+c)) (he:h≤ H) : Bed G h q r≤comap V.Q (Bed G h (q+c) r):= by
    induction r generalizing h q with
    | zero=>
       refine bed_le _ fun f x y hy hq hx he=> ?_; rw [Submodule.mem_comap,line_zero,no]; exact zero_mem _
    | succ r ih=>
       apply bed_le; intro f x y hF hx hy hc
       subst h q; rw [Fin.sum_univ_succ] at he; rw [Submodule.mem_comap,Fin.sum_univ_succ,Fin.sum_univ_succ,line_bud,parity_bud (hF 0)]; have hp' : (∑ i : Fin r,x i.succ)≤ H:= le_trans (le_add_of_nonneg_left (hc 0)) he
       have hb : line r (f∘ Fin.succ)∈ Bed G (∑ i : Fin r,x i.succ) (∑ i:Fin r,y i.succ) r:= tileCub.mpr (line_in mslug ghostNo (fun i=> seedStar.mp (hF i.succ)))
       have ht : V.Q (line r (f∘Fin.succ)) ∈ Bed G (∑ i : Fin r,x i.succ) ((∑ i:Fin r,y i.succ)+c) r:= ih hp' hb
       refine add_mem ?_ (smul_mem _ _ ?_); convert! planting (hp _ (le_trans (le_add_of_nonneg_right (Finset.sum_nonneg (f:=fun i:Fin r=>x i.succ) fun j _=> hc j.succ)) he) _ _ (hF 0)) hb using 2; omega
       convert! planting (hF 0) ht using 2; omega

lemma qPrice (hp:F∈Bed G x y r): natQ F∈Bed G x (y+1) r:= enters (V:=Gof) (fun h _ q f hf=> stays f h q hf) le_rfl hp

variable {he : ℤ}
-- keep capital N on ordered tensors
abbrev Count (A : Mover G):= joint (MatrixLet.one A)
def Nop (A : Mover G) : Module.End ℂ (Law G) := Gof.Q.comp A.Q + A.Q.comp Gof.Q
@[simp] lemma Nop_at (F) : Nop A F=natQ (A.Q F)+ A.Q (natQ F):=rfl
lemma N_price (X:Calib (MatrixLet.one A) he) (hq:h≤ he) (hp:F∈ Bed G h q r): Nop A F∈ Bed G h q r:= by
   have hx k (hk:k≤he) m f hf:=X.price k m f hk hf
   have hm k (hk:k≤he) m f (hf:f∈yields k m): MatrixLet.one A f∈ yields k (m+(-1)):= hx k hk m f hf
   have hb : A.Q F∈ Bed G h (q+(-1)) r:= enters hm hq hp
   rw [Nop_at]
   exact add_mem (by simpa using qPrice hb) (by simpa using (show A.Q (natQ F)∈ Bed G h (q+1+(-1)) r from enters hm hq (qPrice hp)))

lemma lift_sum (X Y: Mover G) (hv : f∈ yields x a) (hp: MatrixLet.one X f∈ yields x (a+b)) (ht: MatrixLet.one Y f∈yields x (a+c)) (he: Local.parity b=true) (hz : Local.parity c=true):
   X.Q (Y.Q (bud f F))+Y.Q (X.Q (bud f F))=bud ((MatrixLet.one X) (MatrixLet.one Y f)+(MatrixLet.one Y) (MatrixLet.one X f)) F+bud f (X.Q (Y.Q F)+Y.Q (X.Q F)):= by
   rw [parity_bud hv, parity_bud (V:=X) hv]; simp only [map_add,map_smul,parity_bud ht,parity_bud hp,parity_bud hv]; simp only [← place_at,map_add,LinearMap.add_apply,par_add,he,hz]
   cases Local.parity a <;> (simp; abel)
lemma anticom (X:Calib (MatrixLet.one A) h) (hf : f∈yields x a) (hq:x≤h) : Nop A (bud f F)= bud (Count A f) F+bud f (Nop A F):=
    lift_sum Gof A hf (stays _ _ _ hf) (show MatrixLet.one A f∈yields x (a+(-1)) from X.price x a f hq hf) rfl rfl
lemma q_zero (hF:F∈ Bed G h q r) : natQ (natQ F)=0:= by
   suffices hp: Bed G h q r ≤ LinearMap.ker ((Gof.Q).comp Gof.Q) from hp hF
   clear hF; induction r generalizing h q with
   | zero=> apply bed_le; intro f x y hf hx hy hp; rw [LinearMap.mem_ker,LinearMap.comp_apply,line_zero,no,map_zero]
   | succ r ih=>
      apply bed_le; intro f x y hf hx hy hp
      let F:=line r (f∘Fin.succ); have ht : natQ (natQ F)=0:= ih (tileCub.mpr (line_in (n:=r) mslug ghostNo (fun i=> seedStar.mp (hf i.succ)))) -- arg n not r
      have he:= lift_sum (F:=F) Gof Gof (hf 0) (stays _ _ _ (hf 0)) (stays _ _ _ (hf 0)) rfl rfl
      simp_rw [show MatrixLet.one Gof (MatrixLet.one Gof (f 0))=0 from Q_zero _, (show Gof.Q (Gof.Q F)=0 from ht),add_zero, ← place_at,map_zero] at he
      simp only [LinearMap.zero_apply,add_zero] at he; rw [LinearMap.mem_ker,line_bud]; ext l; let k:=Gof.Q (Gof.Q (bud (f 0) F)); change k l=0; have hp:k l+k l=0:= congr_fun he l; linear_combination hp / 2
end Woven
end YM.MS.Local.BV
