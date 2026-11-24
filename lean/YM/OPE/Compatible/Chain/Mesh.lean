import YM.OPE.Compatible.Chain.Halo
/-!
# Feynman cylinder bilinear Gaussian
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Terp
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Matrix Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Flume.Script Finset
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent Further.FreeCovariance.KP GaussianScore
local notation "M" => TypeFace 1
variable {C:KernelChoices}{r:ℕ}
lemma basin_nonneg (h:4 ≤ r)(v:Train r)(x: form 1 n): 0 ≤ x ⬝ᵥ (major (ShellRow C v) n*ᵥ x):= by
      unfold major; rw [show (ShellRow C v).acts n=_ from Op_stays h v n]; unfold Precision.K; let H:= (pink C.penalty v).acts n
      obtain ⟨a,b,ha,hb,hQ⟩ := (heart_heats C.penalty C.penalty_pos h (fun i: Train r => i)).1.funds; let D:= d 1 n; let P:= grad n; rw [add_mulVec,dotProduct_add]; apply add_nonneg
      · have he := (obey_band _ ((heart_heats C.penalty C.penalty_pos h (fun i: Train r=>i)).1.stock.whole v) (hQ v) n).2 (D*ᵥx); change 0≤ x ⬝ᵥ ((Dᵀ * H * D)*ᵥ x); rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,dotProduct_mulVec, vecMul_transpose]; apply le_trans (mul_nonneg ha.le _) he.1; simpa only [star_trivial] using dotProduct_star_self_nonneg (D*ᵥx)
      rw [← Matrix.mulVec_mulVec,dotProduct_mulVec,show x ᵥ* grad n=(grad n)ᵀ*ᵥx from (mulVec_transpose ..).symm]; simpa only [star_trivial] using dotProduct_star_self_nonneg (Pᵀ*ᵥx)
lemma pondT (h:4 ≤ r)(v:Train r)(n:Side) : (major (ShellRow C v) n).IsHermitian:=by
     unfold major; rw [show (ShellRow C v).acts n=_ from Op_stays h v n]; apply Matrix.IsHermitian.add; swap;· exact show IsHermitian (grad n * (grad n)ᵀ) from by unfold IsHermitian; simp
     unfold Precision.K
     obtain ⟨a,b,_,_,H⟩:= (heart_heats C.penalty C.penalty_pos h (fun i: Train r=>i)).1.funds; have hh:= (obey_band _ ((heart_heats C.penalty C.penalty_pos h (fun i: Train r=>i)).1.stock.whole v) (H v) n).1; unfold Matrix.IsSymm at hh; unfold IsHermitian; simp [hh, Matrix.mul_assoc]
variable (H:Even n.val)
include H
lemma onwater (h:4 ≤ r)(v:Train r)(x:form 1 n)(hx:∀ i,stem i x=x)(he:x ⬝ᵥ(major (ShellRow C v) n*ᵥ x)=0):x=0:=by
     let B:=major (ShellRow C v) n; have hv:B*ᵥx=0:= by
       have hi:B.PosSemidef := Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (pondT h v n) (fun y=>by simpa only [star_trivial] using basin_nonneg (C:=C) h v y)
       exact (hi.dotProduct_mulVec_zero_iff x).mp (by rw [star_trivial]; exact he)
     have hl:= (neutralize (C:=C) n h v).2; have ht:= congr_arg (fun A:Matrix (Body 1 n) _ ℝ=> A*ᵥx) hl; rw [← Matrix.mulVec_mulVec,hv,mulVec_zero,Matrix.sub_mulVec,Matrix.one_mulVec,blind _ (h_storm H _ ((StemClip x).mp ?_)),sub_zero] at ht -- dir error
     exact ht.symm
     exact hx
-- leading weighted boost
local notation "TK" => Libra.Keys G (Limb H)
def flag (K:Row M M)(u v:TK):ℝ:= let B:= major K n; let x:= cloak H u; let y:=cloak H v; (∑ i:G.ColorIndex, parts G 1 x i ⬝ᵥ (B*ᵥparts G 1 y i))/4
lemma flag_sym (h:4 ≤ r)(v:Train r)(x y:TK): flag H (ShellRow C v) x y=flag H (ShellRow C v) y x:= by
     unfold flag; dsimp only; congr 1; apply Finset.sum_congr rfl; intro i _; let A:=major (ShellRow C v) n; have ha: A=Aᵀ:=(by have he:= (pondT h v n (C:=C)).symm; simpa using he); let u:= parts G _ (cloak H x) i; let t:=parts G _ (cloak H y) i; change u ⬝ᵥ (A*ᵥt)=t ⬝ᵥ (A*ᵥu); rw [dotProduct_mulVec, dotProduct_comm]; rw [ha,vecMul_transpose,← ha]
lemma flag_pos (h:4 ≤ r)(v:Train r)(x:TK)(hx:x≠0): 0<flag H (ShellRow C v) x x:=by
     by_contra! ht; apply hx; ext i j
     have he : parts G 1 (cloak H x) j=0:= by
       apply onwater H h v _ _ (C:=C); swap; · exact (StemClip _).mpr (EllK H j x)
       unfold flag at ht; simp only at ht; have hi:= Finset.single_le_sum (fun k _=> basin_nonneg (C:=C) h v (parts G _ (cloak H x) k)) (mem_univ j); apply le_antisymm _ (basin_nonneg h v _); linarith only [ht,hi]
     have hu : (x i) j=(parts G _ (cloak H x) j) (addressR i.val):=by unfold parts; rw [show addressR i.val=(i.val.1,coord i.val.2) from rfl,cloak_at,Prod.mk.eta,hover_reap]
     exact hu.trans (congr_fun he _)
end YM.OPE.Cascade.Terp
