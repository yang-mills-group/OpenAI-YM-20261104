import YM.XSpace.Prana
/-!
# Limits of the three bulk margin readings
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Finale
open Function Set Filter Trace Gauge Relief Sail Tide MeasureTheory Mu Graph3 Chart2 Asymptotics Gland Season Octave Lattice Chiral MvPolynomial Player
open scoped Topology BigOperators Classical
variable {G:Gauge}{W:Initialize G}{ι:Type} {a:ι→ℝ}{L:Filter ι} {x y z:ι→Cover} {u v b:E4} {c:Shade.Cut}
variable (P Q R:Player W)(g:G.Simple) (σ: Bool)(k:Name G)
def air (c:Shade.Cut)(u v b:E4):ℂ:=↑(heel P Q R k*∑ i:Axis,∑ j:Axis,q σ k.1 i j * parts c σ P.σ k.1 P.row (Q.gCost i) (R.gCost j) u v b)
private abbrev lefts (x y z:Cover):=∑' w:Cover,margin P Q R g x y z w σ k
variable (T:Captain c L a x y z u v b)
include T in
lemma aired [L.IsCountablyGenerated][NeBot L]: Named L a 6 (fun i=>∑' w: Cover,margin P Q R g (x i) (y i) (z i) w σ k) (air P Q R σ k c u v b):=by
  unfold air margin; simp_rw [revenue P Q R g σ k _ _ _ (origin₄ P g σ k.1)]
  apply Named.coe; let X(i j:Axis):= off_field T P Q R g σ k.1 i j; let Y := heel P Q R k; unfold Payout τ; simp_rw [show ∀ (x:ℝ), heel P Q R k * x=Y*x from fun _=>rfl] -- cost promo
  apply Tendsto.congr _ ((tendsto_finsetSum (f:=fun i:Axis=> fun t:ι=>∑ j:Axis,q σ k.1 i j*((a t)⁻¹^6*Trail (x t) (y t) (z t) (mio P g σ k) (Q.M g i) (R.M g j))) _ (fun i hi=> tendsto_finsetSum _ fun j (_:j∈Finset.univ)=> (X i j).const_mul (q σ k.1 i j))).const_mul Y); intro w; simp_rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; ring
include T in
lemma aired₀ (h:P.σ=σ): Named L a 6 (fun i=>∑' w:Cover,margin P Q R g (x i) (y i) (z i) w σ k) (if k=P.elem then kernel Q R σ u v b k else 0) := by
  let D:= traceLag k.1 P.row cover; have hh:D∈Terrain 4:= by
    have hx: O P g σ k.1-D∈ Surface 4:= h ▸ sleeved g P.size P.hr P.σ k.1 P.row; rw [← sub_sub_self (O P g σ k.1) D]; exact Submodule.sub_mem _ (origin₄ P g σ k.1) (light_hill 4 (by norm_num) (surfaces hx))
  let f(x y z w:Cover):= margin0 P Q R g x y z w σ k D; have ht(x y z:Cover): (∑' w:Cover, f x y z w) = if k=P.elem then pair Q R g x y z (stance σ k) else 0:=by
    rw [tsum_eq_single x]; unfold f; change (↑(χ P.color k.2* traceLag _ _ _ (x-x)):ℂ)*_= _; by_cases hk:k=P.elem; rw [if_pos hk]; unfold row color; simp [hk,trace_at]; rw [trace_at,if_neg hk]; split
    · rename_i hw; rw [show χ P.color k.2=0 from if_neg (fun e=> hk (Prod.ext hw.1 e)),zero_mul]; simp
    simp
    intro w hw; change (↑(χ P.color k.2* traceLag _ _ _ (w-x)):ℂ)*_= _; rw [trace_at, if_neg (show ¬(_∧ _) from fun H=> sub_ne_zero.mpr hw H.2)]; simp
  let Y i:=∑' w:Cover,f (x i) (y i) (z i) w
  refine Named.wallet (g:=Y) ?_ ?_
  · unfold Y; simp_rw [ht]; by_cases hk:k=P.elem; simpa only [hk,↓reduceIte] using ask_pair Q R g T σ P.elem; simp only [if_neg hk,Named,mul_zero]; exact tendsto_const_nhds
  unfold Y f margin; simp_rw [revenue _ _ _ _ _ _ _ _ _ (origin₄ P g σ k.1),revenue P Q R g σ k _ _ _ hh, ← Complex.ofReal_sub]; refine (Complex.ofReal_zero ▸ Named.coe ?_); apply Payout.big _ T.led; simp_rw [← mul_sub (heel ..),τ,← Finset.sum_sub_distrib, ← mul_sub]; apply IsLittleO.const_mul_left; refine IsLittleO.sum (fun i (_:i∈Finset.univ)=> IsLittleO.sum (fun j (_:j∈Finset.univ)=>?_)); exact (lost_game T P Q R g σ k.1 i j h).const_mul_left _
end YM.XSpace.Finale
