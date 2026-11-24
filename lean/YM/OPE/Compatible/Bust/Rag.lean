import YM.OPE.Compatible.Bust.Juror
/-!
# Lap on seats. quantitative. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Float
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08
open scoped Topology BigOperators Classical
variable {I K E F X:Type}{m r i j n k:ℕ}{C D:ℝ}
noncomputable def lapD (A:RowB I)(m k:ℕ): Seat k m I→L[ℝ] Seat k m I := ContinuousLinearMap.pi fun i:Fin (k+1)=> wind i.val • ((stirC I m i.val ∘L vibeC I m i.val A) ∘L moduleAt m k (i.val+2) I)
lemma pinch (x:Seat k m I)(v:RowB I)(i:Fin (k+1)):
     (lapD v m k x i)= wind i.val • (stirC I m i.val (vibeC I m i.val v (moduleAt m k (i.val+2) I x))) :=by simp [lapD]
lemma pulse_i (x:Seat k m I)(v:RowB I)(i:ℕ): lilies m k I (lapD v m k x) i= wind i • pad v.val (lilies m k I x (i+2)):=by
     rw [soup,moduleAt]; split
     next he=> change seed m _ I (lapD v m k x ⟨i,by omega⟩) = _; erw [pinch]; rw [map_smul, vibe_eq,stirLeg]; rfl
     next he=> rw [_root_.zero_apply,map_zero,soup,moduleAt,dif_neg (by omega),_root_.zero_apply,map_zero]; ext1 x; simp [pad,tunnel,Sack.rope]
lemma stir_norm (I:Type)(m r:ℕ): ‖stirC I m r‖≤1:=by
     let A:= stirC I m r; refine A.opNorm_le_bound zero_le_one (fun i=> (kept_stalk (meltDown (m:=m) i)).trans_eq (one_mul _).symm)
lemma lapE (v:RowB I) : ‖lapD v m k‖≤ (wind k)*v.fare:=by
     let t:= lapD v m k; let c:=v.fare; have h:0 ≤ wind k:=by unfold wind; positivity
     apply t.opNorm_le_bound (mul_nonneg h v.positive); intro w; apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg h v.positive) (norm_nonneg w))).mpr; intro i; let V:= moduleAt m k (i.val+2) I w; let D:=vibeC I m i.val v; let f:= D V; have hf:‖f‖≤ c*‖w‖:= (D.le_opNorm _).trans (mul_le_mul (vibe_n _) (lemon _ _) (norm_nonneg _) v.positive); have hd:‖stirC I m i.val f‖≤ c*‖w‖:= ((stirC I m i.val).le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) (stir_norm ..)).trans hf)
     have ht:i.val ≤k:= Nat.le_of_lt_succ i.isLt; have hz:0 ≤ wind i.val:=by unfold wind; positivity
     rw [pinch,norm_smul,Real.norm_of_nonneg hz, mul_assoc (wind k) v.fare]; exact mul_le_mul (by unfold wind; gcongr) hd (norm_nonneg _) h
lemma loreLap {f:Filter X}{A:X→RowB I}{p:RowB I}(h:Dull f A p): Robust f (fun i=> lapD (A i) m k) (lapD p m k):=by
     let l:=wind k; obtain ⟨c,hc,H⟩:= h.born; have hl:0 ≤ l:=by unfold l wind; positivity
     refine ⟨⟨l*c,mul_nonneg hl hc,H.mono fun i hi=> (lapE (A i)).trans (mul_le_mul_of_nonneg_left hi hl)⟩,fun x=>?_⟩; apply tendsto_pi_nhds.mpr; intro i; simp_rw [pinch]; refine tendsto_const_nhds.smul ?_; exact ((stirC I m i.val).continuous.tendsto _).comp ((vibing h).p2 _)
-- map ticket frame finite
variable [Fintype I] (m k)
end YM.OPE.Silt.Float
