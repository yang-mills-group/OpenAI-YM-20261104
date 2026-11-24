import YM.OPE.Compatible.Glow.Loon
/-! # Chant supports and costs -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}{b:ℝ}
namespace Script
open Page
abbrev Chant (G:Gauge)(n:ℕ):= Fin n → Beam G
abbrev verseX (p:Chant G n)(u:CoverConfig G):=∏ i,(p i).account u
abbrev lawn (p:Chant G n):=∑ i,(p i).leg.length
def cashX (p:Chant G n):=univ.biUnion fun i=> dirt 0 (p i).leg
lemma cashCard (p:Chant G n) : (cashX p).card ≤ lawn p:= Finset.card_biUnion_le.trans (sum_le_sum fun _ _=>dirt_shape ..)
lemma cashSize (p:Chant G n)(i:Edge Cover)(h:i∈cashX p): size i.1 ≤ lawn p:=by
   obtain ⟨j,h,hj⟩:=mem_biUnion.mp h; have hu : size i.1 ≤ (p j).leg.length:= by simpa [size] using dirtRange (p j).leg 0 hj
   exact hu.trans (single_le_sum (f:=fun i=>(p i).leg.length) (fun _ _=>Nat.zero_le _) (mem_univ j))
lemma cashSafe (p:Chant G n){U V:CoverConfig G}(h:Set.EqOn U V (cashX p)): verseX p U=verseX p V:= by apply Finset.prod_congr rfl; intro j hj; unfold Beam.account; rw [dirt_uses _ _ _ _ (h.mono fun i hi=>mem_biUnion.mpr ⟨j,hj,hi⟩)]
abbrev moderateX (p:Chant G n)(D:ℝ):Prop:=∀ i,∀ x:G.Mat, ‖(p i).f x‖ ≤ D * ‖x‖
lemma cash_smooth (B:Chant G n)(u:fieldX (Shade G)): ContDiff ℝ ⊤ (fun t:ℝ=> verseX B (lotU (t • u))):=by
    unfold verseX; apply contDiff_prod; intro i _; let W: ℝ→ G.Mat:=fun t=> G.mat (travel (lotU (t • u)) 0 (B i).leg); let F:G.Mat→L[ℝ]ℝ:=(B i).f; exact F.contDiff.comp ((fluted _ 0 _).sub (g:=fun t=>1) contDiff_const)
lemma cashBill (G:Gauge)(n:ℕ)(s c D:ℝ)(hs:0<s)(hc:0≤c)(hd:0≤D)(k:ℕ):∃ A:ℝ, 0≤A ∧ ∀ (p:Chant G n)(U:fieldX (Shade G)), moderateX p D → (∀ i∈ cashX p, ‖indexS i U‖ ≤ c) → ∀ t, ‖iteratedDeriv k (fun t:ℝ=>verseX p (lotU (t • U))) t‖ ≤ A*Real.exp (s*lawn p):=by
    induction n generalizing k with
    | zero=>
       refine ⟨1,zero_le_one,fun p U h H t=>?_⟩; simp only [lawn,verseX,Fin.prod_univ_zero,Fin.sum_univ_zero,Nat.cast_zero,mul_zero,Real.exp_zero, mul_one]; by_cases hk:k=0
       · subst k; simp
       unfold iteratedDeriv; rw [iteratedFDeriv_const_of_ne hk]; simp
    | succ n ih=>
       choose A ha HA using fun i=>ih i; choose F hf H using fun i=> beam_bounds G _ _ hs hc i
       let Y(j:ℕ):ℝ:= (k.choose j:ℝ)*(F j*D)*A (k-j); have hy(j):0 ≤ Y j:=by unfold Y; have hv:= hf j; have ht:=ha (k-j); positivity
       refine ⟨∑ i∈range (k+1),Y i, sum_nonneg fun i _=>hy i,fun p u h hh t=>?_⟩
       let R:=p 0; let v(i:Fin n):=p i.succ; let f(x:ℝ):=R.account (lotU (x • u)); let w(x:ℝ):=verseX v (lotU (x • u)); let I:=Real.exp (s*R.leg.length); let J:=Real.exp (s*lawn v)
       have ht(i): ‖iteratedDeriv i f t‖≤F i * D*I:= H i R u _ hd (h _) (fun j hj=> hh j (mem_biUnion.mpr ⟨0,mem_univ _,hj⟩)) t
       have hb(i): ‖iteratedDeriv i w t‖≤ A i*J:=HA _ _ u (fun j=> h j.succ) (fun j h'=>hh j (by obtain ⟨a,-,hA⟩:=mem_biUnion.mp h'; exact mem_biUnion.mpr ⟨a.succ,mem_univ _,hA⟩)) t
       have hT: ContDiff ℝ ⊤ f:=by
          let y: Fin 1→Beam G:= fun _=>R; have he := cash_smooth y u; rwa [show (fun t:ℝ=>verseX y (lotU (t • u)))=f from funext fun i=>by unfold verseX; rw [Fin.prod_univ_one]] at he
       have he : (fun t:ℝ=>verseX p (lotU (t • u)))=f*w:=funext fun i=>Fin.prod_univ_succ _
       rw [he,iteratedDeriv_mul (hT.of_le le_top|>.contDiffAt) ((cash_smooth v u).of_le le_top|>.contDiffAt), show Real.exp (s*lawn p)=I*J from by unfold lawn; rw [Fin.sum_univ_succ,Nat.cast_add,mul_add,Real.exp_add]]; apply (norm_sum_le ..).trans; rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro i _; rw [norm_mul,norm_mul, Real.norm_natCast]; apply (mul_le_mul (mul_le_mul_of_nonneg_left (ht _) (Nat.cast_nonneg _)) (hb _) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg _).trans (ht i)))).trans_eq; unfold Y; ring
end Script
end YM.OPE.Flume
