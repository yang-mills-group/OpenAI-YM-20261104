import YM.OPE.Samples.Layout
import YM.Extraction.Round

/-! A pair of actual rounded fine Wilson links tested after their centered block.
Compare their fine cover displacement before reducing it on the torus. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryGridGap
open Function Filter Set MeasureTheory Lattice Wilson RG Extraction
open scoped Classical BigOperators
variable {G:Gauge} (C:Family G) {k N p:ℕ}

private theorem axes {x y:E4} {s:ℝ} (hs:0 ≤ s) (bound:∀j,|x j-y j| ≤ s) :
    dist x y ≤ 4*s := by
  rw [dist_eq_norm,←sq_le_sq₀ (norm_nonneg _) (by positivity),EuclideanSpace.real_norm_sq_eq]
  calc _ ≤ ∑ _ : Axis, s^2 := Finset.sum_le_sum fun j _=>sq_le_sq.mpr (by rw [abs_of_nonneg hs];exact bound j)
       _ ≤ _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat];nlinarith [sq_nonneg s]

theorem translated (offset:Site (C.side N p)) (live:k ≤ N) (r:ℝ) (hr:0<r) (x:Points 2) (D:ℕ)
    (spaced:(32+4*D)*(C.S.a k/r) < dist (x 0) (x 1))
    (within:2*(dist (x 0) (x 1)+32*(C.S.a k/r)) < ((C.side k p).val:ℝ)*(C.S.a k/r)) :
    let g:=C.S.toDepth live p
    let u:=fun i:Fin 2=>wrap (C.side N p) (address (C.S.a N) (r • x) i)-offset
    D < separation (g.parent (u 0)) (g.parent (u 1)) := by
  let b:=address (C.S.a N) (r • x)
  let n:=C.side N p
  let g:=C.S.toDepth live p
  let a:=C.S.a N/r
  let c:=C.S.a k/r
  let y:=r⁻¹ • tag (C.S.a N) b
  have ap:0<a:=div_pos (C.S.a_pos N) hr
  have cp:0<c:=div_pos (C.S.a_pos k) hr
  have order:a ≤ c:=div_le_div_of_nonneg_right (C.S.strictAnti.antitone live) hr.le
  have sc:a*(g.count.val:ℝ)=c:= by
    dsimp [a,c,g]; rw [div_mul_eq_mul_div, C.S.embeds_scale]
  change (32+4*D)*c < _ at spaced
  change 2*(dist (x 0) (x 1)+32*c) < ((C.side k p).val:ℝ)*c at within
  have span:((C.side k p).val:ℝ)*c=(n.val:ℝ)*a := by
    dsimp [a,c,n];rw [mul_div_assoc',mul_div_assoc',mul_comm ((C.side k p).val:ℝ),mul_comm ((C.side N p).val:ℝ),
      C.S.span_side,C.S.span_side]
  have near : dist y x ≤ 8*a := by
    have erased : r⁻¹ • (tag (C.S.a N) b-r • x)=y-x := by
      rw [smul_sub,smul_smul,inv_mul_cancel₀ hr.ne',one_smul]
    rw [dist_eq_norm,←erased,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hr).le,←dist_eq_norm]
    calc _ ≤ r⁻¹*((4*(2:ℕ):ℝ)*C.S.a N) :=
           mul_le_mul_of_nonneg_left (Extraction.approximate (C.S.a_pos N) (r • x)) (inv_pos.mpr hr).le
         _ = 8*a := by simp only [a,div_eq_mul_inv,Nat.cast_ofNat];ring
  have moved (i:Fin 2) : dist (y i) (x i) ≤ 8*c :=
    (PiLp.dist_apply_le y x i).trans (near.trans (by linarith only [order]))
  have rev (i:Fin 2) : dist (x i) (y i) ≤ 8*c := by rw [dist_comm];exact moved i
  have above:dist (y 0) (y 1) ≤ dist (x 0) (x 1)+16*c := by
    linarith only [dist_triangle (y 0) (x 0) (y 1),dist_triangle (x 0) (x 1) (y 1),moved 0,rev 1]
  have below:dist (x 0) (x 1) ≤ dist (y 0) (y 1)+16*c := by
    linarith only [dist_triangle (x 0) (y 0) (x 1),dist_triangle (y 0) (y 1) (x 1),rev 0,moved 1]
  have counts (j:Axis) : |y 0 j-y 1 j|=a*|(((b 0-b 1) j:ℤ):ℝ)| := by
    change |r⁻¹*(C.S.a N*(b 0 j:ℝ))-r⁻¹*(C.S.a N*(b 1 j:ℝ))|=a*|((b 0 j-b 1 j:ℤ):ℝ)|
    rw [←abs_of_pos ap,←abs_mul];push_cast;congr 1;dsimp [a];ring
  have unwrap : lift (wrap n (b 0-b 1))=b 0-b 1 := by
    apply lift_eq_iff.mpr
    refine ⟨rfl,?_⟩
    intro j
    have small:2*|(((b 0-b 1) j:ℤ):ℝ)| < (n.val:ℝ) := by
      apply (mul_lt_mul_iff_right₀ ap).mp
      have coord:|y 0 j-y 1 j| ≤ dist (y 0) (y 1) := by simpa only [Real.dist_eq] using PiLp.dist_apply_le (y 0) (y 1) j
      linarith only [coord,counts j,above,within,span,cp]
    have lim:2*|(b 0-b 1) j| < (n.val:ℤ) :=by exact_mod_cast small
    have upper:=le_abs_self ((b 0-b 1) j)
    have lower:=neg_le_abs ((b 0-b 1) j)
    omega
  dsimp only
  by_contra! small
  change separation (g.parent (wrap n (b 0)-offset)) (g.parent (wrap n (b 1)-offset)) ≤ D at small
  have grown:= (OPE.Log.Trunk.Canvas.expands (C:=C) (wrap n (b 0)-offset) (wrap n (b 1)-offset) live).2
  have fine : separation (wrap n (b 0)) (wrap n (b 1)) ≤ g.count.val*(D+1) :=by
    have step:=Nat.mul_le_mul_left g.count.val small
    change separation _ _ < g.count.val*separation (g.parent _) (g.parent _)+g.count.val at grown
    rw [show separation (wrap n (b 0)-offset) (wrap n (b 1)-offset)=separation (wrap n (b 0)) (wrap n (b 1)) by simp only [sub_eq_add_neg,separation_translate]] at grown
    change separation (wrap n (b 0)) (wrap n (b 1)) < g.count.val*separation (g.parent (wrap n (b 0)-offset)) (g.parent (wrap n (b 1)-offset))+g.count.val at grown
    rw [Nat.mul_succ];omega
  have close(j:Axis): |y 0 j-y 1 j| ≤ c*((D:ℝ)+1) :=by
    rw [counts,←sc,mul_assoc]
    apply mul_le_mul_of_nonneg_left _ ap.le
    have bound:=component_le (wrap n (b 0-b 1)) j
    rw [unwrap] at bound
    have abs : ((b 0-b 1) j).natAbs ≤ g.count.val*(D+1) := bound.trans (by
      simpa only [separation,←map_sub] using fine)
    have int : |(b 0-b 1) j| ≤ ((g.count.val*(D+1):ℕ):ℤ) :=by
      exact_mod_cast (Int.natCast_natAbs _ ▸ (show (((b 0-b 1) j).natAbs:ℤ) ≤ ((g.count.val*(D+1):ℕ):ℤ) from by exact_mod_cast abs))
    exact_mod_cast int
  have metric:=axes (mul_nonneg cp.le (by positivity)) close
  nlinarith only [below,spaced,metric,cp]

theorem original (live:k ≤ N) (r:ℝ) (hr:0<r) (x:Points 2) (D:ℕ)
    (spaced:(32+4*D)*(C.S.a k/r) < dist (x 0) (x 1))
    (within:2*(dist (x 0) (x 1)+32*(C.S.a k/r)) < ((C.side k p).val:ℝ)*(C.S.a k/r)) :
    let g:=C.S.toDepth live p
    let u:=fun i:Fin 2=>wrap (C.side N p) (address (C.S.a N) (r • x) i)
    D < separation (g.parent (u 0)) (g.parent (u 1)) := by
  simpa only [sub_zero] using translated C 0 live r hr x D spaced within

end YM.Integration.WilsonCapturedPrimaryGridGap
