import YM.OPE.Compatible.Birch.Cord
/-! # Budget where loops wind. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical
variable {I J W:Type*}{i j n r d m:ℕ}{G:Gauge}{s b U D:ℝ}{N:Side}
namespace Script
open Page
-- input pol toll W, strip via hx. loose constants enough
lemma gapless {a b:Cover}(h: a≠b)(hv:wrap N a=wrap N b): N.val ≤ size (b-a):=by
   obtain ⟨u,hp⟩:=cover_of_eq b a hv.symm -- b? inspect
   have hu: u≠0:=by intro hx; rw [hx] at hp; simp at hp; exact h hp
   obtain ⟨i,hi⟩:=not_forall.mp (fun q:∀ i,u i=0 => hu (funext q)); have hz:= congr_fun hp i; have he: N.val ≤ (b i - a i).natAbs:=by
       change a i=b i+(N.val) • (u i) at hz; rw [hz]; simp only [sub_add_eq_sub_sub,sub_self,zero_sub,Int.natAbs_neg,nsmul_eq_mul,Int.natAbs_mul,Int.natAbs_natCast]; exact Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr hi)

   apply he.trans; exact single_le_sum (f:=fun i=> ((b-a) i).natAbs) (fun _ _=>Nat.zero_le _) (mem_univ i)
lemma coefWind (A:Row I J)(h:A.strip s U)(hs:0<s)(x:I)(y:J)(i:Cover)(m:ℕ):
   (N.val:ℝ)^m * ‖(A.acts N) (0,x) (wrap N i,y)- A x y i‖ ≤ (2:ℝ)^m * poise m i *widthCost s m * U :=by
    let f(j:Cover):= if i≠j∧wrap N j=wrap N i then A x y j else 0; let C:=(N.val:ℝ); let v(j:Cover):= if i=j then A x y i else 0
    have hh: Summable (fun j=>poise m j*‖A x y j‖):=by simp_rw [liftCostSame,mul_comm (liftCost ..)]; exact (width_income hs (h x y) m).2.1
    have hf: Summable f:= ((show Summable (A x y) from ((h x y).unweighted hs.le).2.1.of_norm).indicator {j| i≠j∧wrap N j=wrap N i}).congr (fun j=> by by_cases h:i≠j∧wrap N j=wrap N i<;>simp_all only [Set.indicator,Set.mem_setOf_eq,f,if_false])
    have hx: Summable v:=(summable_of_ne_finset_zero (s:={i}) fun j hj=>by simp at hj; simp only [v,if_neg (Ne.symm hj)]); have hz : A.acts N (0,x) (wrap N i,y)=(∑' j,f j)+A x y i:=by
       unfold Row.acts; rw [← show ∑' j,v j=A x y i by unfold v;simp,← Summable.tsum_add hf hx]; apply tsum_congr; intro j; unfold f v; simp only [zero_add]; by_cases he:i=j; · rw [← he]; simp
       by_cases h :wrap N j=wrap N i<;> simp [*,eq_comm]
    rw [hz,add_sub_cancel_right]; change C^m * _ ≤ _; apply (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hf.norm) (show 0 ≤ C^m from by unfold C; positivity)).trans; rw [← tsum_mul_left]; let u:=liftCost; have he(j:Cover): C^m*‖f j‖ ≤ 2^m*poise m i*(poise m j*‖A x y j‖):=by
       unfold f; have hb : 0 ≤ poise m i:=zero_le_one.trans (poise_one m _); split
       next h=>
         obtain ⟨hx,hz⟩:= h; have hp:= gapless hx hz.symm; rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); unfold poise; rw [← mul_pow, ← mul_pow]; apply pow_le_pow_left₀ (show 0≤C from Nat.cast_nonneg _) ; have he: N.val ≤ 2 * notch i * notch j:=by
             have ht : size (j-i) ≤ size i+size j:=by rw [sub_eq_add_neg,add_comm (size i)]; exact (size_add ..).trans (le_of_eq (by rw [size_neg])) -- add_comm where?
             apply (hp.trans ht).trans; unfold notch; nlinarith only [Nat.zero_le (size i), Nat.zero_le (size j),Nat.zero_le (size i*size j)]
         unfold C; exact_mod_cast he
       next h=>rw [norm_zero,mul_zero]; have ht:=zero_le_one.trans (show 1≤ poise m j from poise_one m _); positivity
    apply ((hf.norm.mul_left _).tsum_le_tsum he (hh.mul_left _)).trans; rw [tsum_mul_left,mul_assoc (2^m*_ :ℝ)]; apply mul_le_mul_of_nonneg_left; swap; · unfold poise; positivity
    simp_rw [liftCostSame,mul_comm (liftCost ..)]; exact (width_income hs (h x y) _).2.2
end Script
end YM.OPE.Flume
