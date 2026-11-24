import YM.OPE.Compatible.Hull.Broc
import YM.OPE.Compatible.LevelX.Fond
import YM.OPE.Compatible.Hull.Nook
import YM.OPE.Compatible.Hull.Spoon
import YM.OPE.Compatible.Hull.Bud
import YM.OPE.Compatible.Sward.Lucent
/-!
# Build fixed-height real analytic×smooth LP mark extraction. Uniform Scrape.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n:Side}(o:Site n){b i k r m:ℕ}{C:KernelChoices}
open Finset
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin Module
open Source Labels Source.Drops
section
open Beamer
variable {d:ℕ} (W:Snap G d)
variable {η:ℝ}
noncomputable def TongV {r:ℕ}(V:Fin r→fieldX (Shade G))(x:Fin r→ℕ)(hx:Glob V x)(hp:∑ i,x i ≤ m) (k:ℕ): Seat k m (Shade G)→L[ℝ] ℝ:=by
     let X(y:Seat k m (Shade G)):=lilies m k (Shade G) y; let f:Seat k m (Shade G)→ₗ[ℝ] ℝ:={ toFun y:=wholeX (X y r) V,map_add' y z:=by rw [show X (y+z) r=X y r+X z r from congr_fun (map_add ..) r]; exact manyX ((sproutV m k y).2 _) ((sproutV m k z).2 _) hx hp,map_smul' c y:= by rw[show X (c • y) r=c • X y r from congr_fun (map_smul ..) r]; exact scaleX .. }; choose a ha H using fun i=> hx i; let D:=∏ i,a i; refine f.mkContinuous D fun p=>?_
     let P(i):=X p r i; let y:=wordX V; let u(i):=figure m i * ‖P i‖; let B:= (sproutV m k p).2 r; refine (norm_tsum_le_tsum_norm (wordSum B hx hp|>.norm)).trans ?_; have hz(i:Page (Shade G) r):‖P i*y i‖≤ D * u i:=by rw [norm_mul]; apply (mul_le_mul_of_nonneg_left (wordXbill ha H hp i) (norm_nonneg _)).trans_eq; unfold D u;ring
     have ht : (∑' i,‖P i*y i‖) ≤ D*∑' i,u i:= ((wordSum B hx hp|>.norm).tsum_le_tsum hz (B.2.1.mul_left D)).trans_eq (tsum_mul_left ..); exact ht.trans (mul_le_mul_of_nonneg_left B.2.2 (Finset.prod_nonneg (fun i _=>ha i)))
lemma rayLen (P:OrderedFinpartition i): ∑ j,(P.partSize j-1)=i-P.length:=by
        have hz:∑ j,P.partSize j=i := by simpa using P.sum_sigma_eq_sum (fun _=> (1:ℕ))
        have hp: (∑ j,(P.partSize j-1))+(∑ _j:Fin P.length,1)=i:=by rw[← sum_add_distrib]; apply Eq.trans _ hz; exact sum_congr rfl fun j _=>Nat.sub_add_cancel (P.partSize_pos j)
        simp only[sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,mul_one] at hp; omega
abbrev ArcX (W:Snap G d)(B: OrderedFinpartition i) := fun j => Sie (iteratedDeriv (B.partSize j) (Spindle.flash W) 0)
noncomputable def θShelf (W:Snap G d)(B:OrderedFinpartition i)(k m:ℕ)(hi:i ≤ m):Seat k m (Shade G)→L[ℝ]ℝ:= ((B.length.factorial:ℝ)) • (TongV (m:=m) (ArcX W B) (fun j=>B.partSize j-1) (fun j=> low_quiet (Sea W _)) ((rayLen B).trans_le (by omega)) k)
lemma θShelf_eq (W:Snap G d)(B:OrderedFinpartition i)(p:Seat k m (Shade G))(hi:i ≤ m): θShelf W B k m hi p=(B.length.factorial:ℝ)* wholeX (lilies m k _ p B.length) (fun j=> Sie (iteratedDeriv (B.partSize j) (Spindle.flash W) 0)):= rfl
lemma ΘCoin (W:Snap G d)(B:OrderedFinpartition i)(x:bed G k m)(he:i ≤ d)(hp:d ≤ m)(h:x∈fillet G k m (d+1) (by omega)): θShelf W B k m (by omega) x.val=0:=by
        rw[θShelf_eq]; apply mul_eq_zero_of_right; let n:= B.length; let v:=ArcX W B; let f(j):=B.partSize j-1; have hx:= B.length_le; exact hail ((sproutV m k x.val).2 n) (show ∀ i,Low (v i) (f i) from fun j=>Sea W _) ((rayLen B).trans_le (by omega)) ((rayLen B).trans_lt (show _< d+1-n from by omega)) ((decrement x).1 h n)
noncomputable def θFoil (W:Snap G d)(t:ℝ)(U:BudgetPoint)(k m i:ℕ)(ht:i ≤ m):Seat k m (Shade G)→L[ℝ] ℝ:= ∑ B:OrderedFinpartition i, (θh t U)⁻¹ ^ B.length • θShelf W B k m ht
variable {H:Hol G}{θ:ℝ}(P:Pad G)(f:Config G n→ℂ)(t:ℝ) (U:BudgetPoint)(h:2*(b+1)<n.val)(Q:Acceptance o U (k+6) f b θ)(A:ℂ→L[ℝ]ℝ)
variable (R:KernelChoices)(z:Train r)(hr:4 ≤ r)
noncomputable def priceArc (η:ℝ)(P:Pad G)(A:ℂ→L[ℝ]ℝ)(k b:ℕ)(a:ℝ) (U:BudgetPoint) (t c:ℝ):= ∑ B:OrderedFinpartition k,(θW P b B.length a A * B.length*η^(B.length-1)*η*U.threshold+θW P b (B.length+1) a A * θh t U * η ^ B.length *c)
lemma chartSignal (hx:i < k+6)(hS:i ≤ m)(hV:KiteB H W U.threshold i b η)(hp:2*(4*b+1)<n.val) (ht:0<t):
       let s:= Recon o P h U f A R z hr t Q; let q:= boostS (rentV G z hr R n) (1/2) m (k+6) (Locket s m).val
       ‖iteratedDeriv i (fun j=> A (f (south H o W U.threshold j))) 0-θFoil W t U (k+6) m i hS q‖ ≤ priceArc η P A i b θ U t (nubK G b z R hr n):=by
            intro s q; let v:= JargonR t U H W b; let F:= Artifact o P h U f A t; have hv : ContDiffAt ℝ i v 0:= hV.smooth.const_smul ((θh t U)⁻¹); have he: v 0=0:=by unfold v JargonR;rw [Pi.smul_apply,hV.zeroP,smul_zero]
            rw [(Sol o P f t U h Q A W ht.ne' hp).iteratedDeriv_eq, iteratedDeriv_vcomp_eq_sum_orderedFinpartition (g:=F) (f:=v) (he ▸ ((filip o P h U f A _ Q.ready).contDiffAt.of_le (Nat.cast_le.mpr (hx.le.trans Q.guard)))) hv le_rfl,he,θFoil]; rw [_root_.sum_apply,← sum_sub_distrib]; refine (norm_sum_le ..).trans (sum_le_sum (fun i _=>?_)); exact taxStory o P f t U h Q A W R z hr hx ht hV i hp m
end
end YM.OPE.Spells
