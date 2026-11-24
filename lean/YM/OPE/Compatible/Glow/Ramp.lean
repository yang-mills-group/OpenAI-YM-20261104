import YM.OPE.Compatible.Glow.Mellow
/-! # Accumulative Chant tax. Raw terms polynomial ray cost arbitrary bounded slot before sums. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}{b s U D:ℝ}
namespace Script
open Page
lemma coinReads (p:Chant G n)(v: Fin r→ fieldX (Shade G)): wholeX (coff p r) v=Tensor.coeff (permit p) r 0 (fun i=> collectQ p (v i)):=by
    let A:=Tensor.coeff (permit p) r 0; unfold wholeX; let s:=mold p; let x(i)(j):= v i j • collectQ p (Pi.single j 1); have he : (fun i=> collectQ p (v i))=(fun i=>∑ j∈s,x i j):=by
       ext i j; change _= (∑ k∈s,x i k) j; rw [Finset.sum_apply,Finset.sum_eq_single j.val]; simp only [x]; change v _ _= v _ _ * (Pi.single (M:=fun _=>ℝ) _ 1 _); rw [Pi.single_eq_same,mul_one]; intro k _ hk; change _ * (Pi.single (M:=fun _=>ℝ) k 1 j.val)=_; rw [Pi.single_eq_of_ne hk.symm, mul_zero]; intro h; exact False.elim (h j.property)
    rw [tsum_eq_sum (s:=rim p r) (fun i hi=>by rw [stair p hi,zero_mul]),he]; change _=A.toMultilinearMap _; rw [MultilinearMap.map_sum_finset]; refine Finset.sum_congr rfl fun i _=>?_ ; unfold x; rw [A.toMultilinearMap.map_smul_univ]; exact mul_comm ..
lemma coinTurns (p: Chant G n)(j:ℕ): sorted (coff p j) :=by
     intro q; unfold swing coff; funext i; exact Tensor.coeff_symm ((permitS p).contDiffAt.of_le le_top) (fun j=>collectQ p (Pi.single (i j) 1)) q
lemma coinShots (p:Chant G n)(k:ℕ)(v:fieldX (Shade G)): WardBin.leading k (fun t:ℝ=> verseX p (lotU (t • v)))=wholeX (coff p k) fun _=> v:=by
    rw [coinReads,show (fun t:ℝ=> verseX p (lotU (t • v)))=(fun t=> permit p (t • collectQ p v)) from funext fun i=>by rw [← map_smul,permit_atom]]; exact WardBin.leading_tensor _ _ ((permitS p).contDiffAt.of_le le_top)
-- cofrequency
abbrev saturate (P:I→ Chant G n)(x:I→ℝ)(s U:ℝ):Prop:=SumBudget (fun i=>‖x i‖*Real.exp (s*lawn (P i))) U
def timbre (P:I→ Chant G n)(x:I→ℝ)(r:ℕ):Script (Shade G) r:=fun i=>∑' y,x y * coff (P y) r i
section tally
variable {P:I→ Chant G n}{x:I→ℝ}
lemma totalP (h:saturate P x s U)(he:∀ i,moderateX (P i) D) (hs:0<s)(hg:0≤ D) (r m:ℕ) :∃ C:ℝ,Sack (fun i:I×Page (Shade G) r=>figure m i.2) (uncurry (fun j i=> x j*coff (P j) r i)) C:=by
   obtain ⟨B,H,hb⟩:=coff_price G n r s _ m hs hg
   have ht(i): soot m (x i • coff (P i) r) (B*(‖x i‖*Real.exp (s*lawn (P i)))):= (Sack.scale_line (hb _ (he i)) (x i)).tips (by apply le_of_eq; ring)
   exact ⟨_,Sack.barrel ht (show SumBudget (fun i=> _) (B*U) from ⟨fun i=>mul_nonneg H (h.1 i),h.2.1.mul_left _,by rw [tsum_mul_left];exact mul_le_mul_of_nonneg_left h.2.2 H⟩)⟩
lemma totalBudget (G:Gauge)(m r k:ℕ)(s D:ℝ)(hs:0<s)(hd:0≤D):∃ B:ℝ,0≤B∧ ∀ (P:I→ Chant G k)(x:I→ℝ) U, saturate P x s U→ (∀ i, moderateX (P i) D)→ soot m (timbre P x r) (B*U):=by
   obtain ⟨B,H,hb⟩:=coff_price G k r s _ m hs hd; refine ⟨B,H,fun P x U h hg=>?_⟩
   have ht(i): soot m (x i • coff (P i) r) (B*(‖x i‖*Real.exp (s*lawn (P i)))):= (Sack.scale_line (hb _ (hg i)) (x i)).tips (by apply le_of_eq; ring)
   exact Sack.draws ht (show SumBudget (fun i=> _) (B*U) from ⟨fun i=>mul_nonneg H (h.1 i),h.2.1.mul_left _,by rw [tsum_mul_left];exact mul_le_mul_of_nonneg_left h.2.2 H⟩) (payer m)
lemma timbreT {G:Gauge}(P:I→Chant G n)(x:I→ℝ)(r:ℕ): sorted (timbre P x r):= fun q=>funext fun i=> tsum_congr fun j=> congr_arg (fun p=>x j*p) (congr_fun (coinTurns _ _ q) i)
lemma everyone (h:saturate P x s U)(he:∀ i,moderateX (P i) D)(hs:0<s)(hg:0≤D)(v: Fin r→fieldX (Shade G))(k: Fin r→ℕ)(hk:Glob v k):
    HasSum (fun j=> x j * wholeX (coff (P j) r) v) (wholeX (timbre P x r) v):=by
       let S:= fun j i=> x j*coff (P j) r i*wordX v i; let m:= ∑ i,k i
       choose b hb H using hk; obtain ⟨C,hC⟩:=totalP h he hs hg r m
       have hS: Summable (uncurry S):=by
          apply (hC.2.1.mul_left (∏ i,b i)).of_norm_bounded; rintro ⟨j,i⟩; unfold S; simp only [uncurry_apply_pair]; rw [norm_mul]; exact (mul_le_mul_of_nonneg_left (wordXbill hb H le_rfl i) (norm_nonneg _)).trans_eq (by ring)
       have hx j: (∑' i,S j i)= x j * wholeX (coff (P j) r) v :=by unfold S wholeX; simp only [_root_.mul_assoc,tsum_mul_left]
       have ht : Summable fun i=>∑' j,S i j:= hS.prod; simp_rw [← hx]; unfold wholeX timbre; rw [show (∑' i:Page _ _, (∑' j,x j*coff (P j) r i)*wordX v i)=(∑' i,∑' j, S j i) from tsum_congr fun i=>by unfold S; rw [tsum_mul_right],hS.tsum_comm]; exact ht.hasSum
end tally
end Script
end YM.OPE.Flume
