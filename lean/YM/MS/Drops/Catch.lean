import YM.MS.Drops.Fox
import YM.MS.Drops.Reeds
import YangMills.WilsonProof.NativeSupport.YM.MS.Rake.Sequence
/-! Radian to MS chart.
Dimension fixed=4. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Drops
open Set Function Filter Finset Metric MeasureTheory Real
open Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Woven Color Physical Menus
open Analysis Labels Maxwell Theater Next Next.Rank Next.Rank.Beamer Tone High Rake Osc Snap
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
open City Latch
open Next.Rank.Radian
open Breeze Next Next.Rank Next.Rank.Beamer Asymptotics
variable {G:Gauge}{h k r:ℕ}
local notation "P"=> Hoop G
variable (i j:Key G){l:Filter ℝ}
abbrev tare (a:P i.1)(b:P j.1):ℂ:=petal i a* (petal j b:ℂ)
def pastK (x:E4)(s:ℝ):= ∑ a:P i.1,∑ b:P j.1,tare i j a b * γX (Ep a) (Ep b) x s
lemma dataP (x:E4)(hp:x≠0): ( legKernel (slope i) (slope j) x:ℂ)=∑ a:P i.1,∑ b:P j.1,tare i j a b*(Prayer.gleam (Ep a) ( Ep b ) x:ℂ):= by
    simp_rw [scope_val _ _ x hp]; let M:= Maxwell.pairing ( G:=G ) (show x∈ Maxwell.away from hp) ( j:=i.1 ) ( l:=j.1 ); change ( M (slope i) (slope j):ℂ )=_; rw [ slope_p i,slope_p j, map_sum M, LinearMap.sum_apply,Complex.ofReal_sum ]; apply Finset.sum_congr rfl; intro a ha; rw [ map_sum ( M _ ),Complex.ofReal_sum ]; apply Finset.sum_congr rfl; intro b hb; rw [map_smul ( M _ ),map_smul M,LinearMap.smul_apply]; unfold tare; simp only [smul_eq_mul,Complex.ofReal_mul,mul_assoc]; rw [mul_left_comm]; rfl -- result association
lemma heavenK (q:QP)(s:ℝ)(i:Key G): chair G q (mono ( Theater.lamp i ))∈ Roof G:= chair_p q (show Koszul.mono _∈_ from ⟨ Wallet.faith (shadow_ω i),lying ( shadow_ω i ).1 ⟩ ) -- $s$
lemma high_k (a b:E4)(t:ℝ): linkD G t ( chair G ( out a ) ( singer ( Theater.lamp i ) ) ) ( chair G ( out b ) ( singer ( Theater.lamp j ) ) ) = ∑ u:P i.1,∑ v:P j.1,tare i j u v • coin ( pair_slope (fax (Ep u)) (fax (Ep v)) ( out (a-b) ) t ):= by
   rw [ singer_g i, singer_g j, map_sum ( linkD G t ), LinearMap.sum_apply ]; refine Finset.sum_congr rfl fun u _=>?_ ; rw [map_sum]; refine Finset.sum_congr rfl fun v _=>?_ ; rw [map_smul (linkD G t _),map_smul (linkD G t),LinearMap.smul_apply, smallK _ _ (wholeℓ _) (wholeℓ _),map_sub, smul_comm, smul_smul]
lemma datum (a:P i.1)(b:P j.1): sizeL i+sizeL j=hgt (Ep a) (Ep b):= by change i.1+2+(j.1+2)=i.1+j.1+2+2; omega
lemma cost_k (x:E4): Outlay l (pastK i j x) (-((( sizeL i+sizeL j ):ℕ):ℤ)):= IsBigO.sum (fun a _=> IsBigO.sum (fun b _=> Eq.subst ( congr_arg ( fun i:ℕ=> pale (-(i:ℤ)) ) ( datum i j a b |>.symm ) ) ( ( width (l:=l) (Ep a) (Ep b) x ).const_mul_left (tare i j a b ) ) ) ) -- Eq dependent motive inferred?
lemma star_k (x:E4)(s:ℝ): (pastK j i (-x) s)=pastK i j x s:= by
   unfold pastK; rw [ Finset.sum_comm ]; refine Finset.sum_congr rfl fun a _=> Finset.sum_congr rfl (fun b _=> by rw [ parityX (Ep a) ( Ep b ) x ]; unfold tare; rw [mul_comm ((petal j b:ℝ):ℂ)] )
lemma ClockCert : FieldCert (pastK i j) i j where
   tall t x := by
       unfold pastK; simp_rw [ Finset.smul_sum ]; exact Finset.sum_congr rfl fun a _=> Finset.sum_congr rfl fun b _=> by rw [Year _ _ t, datum i j a b,← mul_smul_comm]; -- association
   wind := cost_k i j
   up x:= ⟨_, cost_k i j x ⟩
   speak a b x := by
       unfold pastK; let A:= a-b; have hp (p:P i.1) (q:P j.1):= ( receipt ( Ep p ) ( Ep q ) x A ).const_mul (tare i j p q); rw [ high_k i j a b x ]; simp_rw [Finset.sum_apply,Pi.smul_apply,smul_eq_mul, ← Finset.sum_neg_distrib,← mul_neg ]; exact HasDerivAt.fun_sum (fun _ _=> HasDerivAt.fun_sum fun j _=> hp _ j )
   fees x hp:= by intro k; simp_rw [pastK, dataP i j x hp, ← Finset.sum_sub_distrib, ← mul_sub ]; exact IsBigO.sum fun _ _=> IsBigO.sum fun _ _=> ( whisper_s _ _ x hp k ).const_mul_left _
end YM.MS.Drops
