import YangMills.WilsonProof.NativeSupport.YM.MS.Pearl.Broach
/-!
# Euler coast and contour subtraction
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Pearl
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell
open scoped Topology ContDiff Interval
variable {I E:Type} {G:Gauge} {W X F: Mob G} {x:ℂ} {b:Bool} {n ℓ m:ℕ} {h:ℕ}{s:ℝ}
variable {f g: ℂ→ Mob G}(hp:altitude m f)(hv:∀ᶠ i in dotty,Mell.Trail (f i) (g i) (vamp i h ℓ))
-- scalar derivative

def sparkle (k:ℕ)(u:ℕ)(y:ℝ): ℂ:= if u=0 then 0 else (gNat k:ℂ)*ley k (u-1) y
@[simp] lemma spark0 (k:ℕ)(y:ℝ): sparkle k 0 y=0:= by simp [sparkle]
lemma spark_tick (y:ℝ)(n t:ℕ) : HasDerivAt (fun z:ℝ=> ley t n (y+z)) (sparkle t n (y+s)) s:= by
   unfold ley; cases n with| zero=> simp [Nat.factorial_zero]; exact hasDerivAt_const s 1| succ n=>
       let x:= gNat t; have ht:= ((hasDerivAt_id' s).const_add y).mul_const x; have he := (ht.ofReal_comp.pow (n+1)).div_const ((n+1).factorial:ℂ); convert! he using 1; unfold sparkle ley; simp [x] ; field_simp [Nat.factorial_succ,Nat.factorial_ne_zero n]; rw [Nat.factorial_succ]; push_cast; ring
-- ∑ identities
private def pShift (v:ℂ→ Mob G)(n k m:ℕ): Mob G:= if n=0 then 0 else (gNat k:ℂ) • ruby (paid m v) (n-1)
include hp hv
lemma vivo (n:ℕ): ruby (paid m g) n= burn (-(h:ℂ)) (ruby (paid m f) n)+pShift f n ℓ m := by
   cases n with| zero=> simp only [pShift, ↓reduceIte,add_zero]; exact (chosen (R_prev0 hp hv)).symm | succ n=> simpa [pShift] using (chosen (R_prev hp hv n)).symm -- Lean bullet
omit hp hv in
private lemma moods (n h:ℕ)(f:ℂ→Mob G)(y s:ℝ): (∑ i∈ Finset.range (n+1), sparkle ℓ i y • plower (-(h:ℂ)) s (ruby (paid m f) (n-i)))=(∑ i∈ Finset.range (n+1), ley ℓ i y • plower (-(h:ℂ)) s (pShift f (n-i) ℓ m)):= by
   -- convert i+1
   rw [Finset.sum_range_succ',spark0,zero_smul,add_zero, Finset.sum_range_succ, Nat.sub_self, pShift,if_pos rfl,map_zero,smul_zero,add_zero]; refine Finset.sum_congr rfl fun i hi=>?_ ; rw [sparkle,if_neg (by omega:i+1≠0), Nat.add_sub_cancel, pShift,if_neg (by simp at hi;omega:n-i≠0), map_smul, mul_smul, smul_comm (gNat ℓ:ℂ),show n-(i+1)=n-i-1 by omega] -- need exact orientation.
lemma Blink (n:ℕ)(s y:ℝ): speed (fun t=> plow (-(h:ℂ)) t (priceY n m ℓ f (y+t))) (plow (-(h:ℂ)) s (priceY n m ℓ g (y+s))) s:= by
   let H(t:ℝ):= plower (G:=G) (-(h:ℂ)) t; let U := ruby (paid m f); let B := fun i=> burn (-(h:ℂ)) (U i); let L (n:ℕ)(t:ℝ):= ley ℓ n (y+t); let D i:= sparkle ℓ i (y+s); unfold priceY; simp_rw [← cert,map_sum,map_smul, vivo hp hv]; simp only [map_add, smul_add,Finset.sum_add_distrib]; rw [← moods]
   have ht (i:ℕ): speed (fun t=> L i t • H t (U (n-i))) (L i s • H s (B (n-i)) + D i • H s (U (n-i))) s := by
       intro m l; obtain hz:= ( spark_tick (s:=s) y i ℓ).mul ((burn_s (x:= (-(h:ℂ))) (Rub hp (n-i)|>.price)).derive s m l); convert! hz using 1;
       unfold D L H; -- simplify price
       simp only [cert,Pi.add_apply,Pi.smul_apply,smul_eq_mul, U,B]; ring
   rw [← Finset.sum_add_distrib]; exact speed_sum _ (fun i _=> ht i)
end YM.MS.Pearl
