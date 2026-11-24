import YM.RegulatorIR.Halo.Mica
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Data.PNat.Order

/-! Marked reading passes W1 by limits of all absolute local moments. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Halo
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Step Matrix StopB Ward Uniform Finset Sight
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff
variable {G:Gauge}{X I J Z:Type}{f:Side}{P:ℝ}{p m i a r s:ℕ}
section Lobe
variable {F:Deck P I J}
def chord (F:Deck P I J)(t:J→ℝ⟦X⟧)(x:I) := PowerSeries.C (F.orient x)*t (F.orbit x)
lemma chord_p (t:J→ℝ⟦X⟧)(x:Tuple I r):pip (chord F t) x=PowerSeries.C (F.polish x)*pip t (F.project x):=by unfold pip chord; simp_rw [Finset.prod_mul_distrib,← map_prod]; rfl
lemma chord_k (t:J→ℝ⟦X⟧)(i:ℕ)(x:I): ‖coeff i (chord F t x)‖ₑ= ‖coeff i (t (F.orbit x))‖ₑ:=by rw [chord,coeff_C_mul,enorm_mul,F.over_sign,one_mul]
lemma chord_port (F:Deck P I J)[Fintype J](t:J→ℝ⟦X⟧){T:Packet I r}(h:quota T 1≠⊤) : rhyme t (F.scroll T) i= rhyme (chord F t) T i:=by
 let ψ:=chord F t;let g(z:Tuple I r):= T z*coeff i (pip ψ z)
 have hx(z): g z=F.dyed T z*coeff i (pip t (F.project z)):= by unfold g ψ; rw [chord_p,PowerSeries.coeff_C_mul]; unfold dyed; ring
 let s:=Finset.univ.sup fun j:J=>‖coeff i (t j)‖ₑ
 have hg(e): Full (fun _:Unit=> chord F t) e :=by intro i h; exact ⟨Finset.univ.sup fun j:J=> ‖coeff i (t j)‖ₑ, ne_of_lt (Finset.sup_lt_iff (by simp)|>.mpr fun i _=>enorm_lt_top), fun _ j=> (chord_k (F:=F) t i j).trans_le (Finset.le_sup (f:=fun j:J=> ‖coeff i (t j)‖ₑ) (Finset.mem_univ _))⟩
 have hs:Summable g:=by obtain ⟨c,hc,H⟩:= (hg i).pipes r i le_rfl;exact quota_summable (fun _=>le_rfl) (rhyme_abs _ T _ h hc (H ()))
 change _=∑'z,g z; rw [← Stalk.collected_sum F.project hs]; apply tsum_congr;intro p; unfold scroll Stalk.collect;rw [← tsum_mul_right];apply tsum_congr;intro z; rw [hx,z.property]
variable {N:Filter Z}
-- scripts along varying paths; uniform up to k

def Learn (v: I→ℝ⟦X⟧)(X:Z→ I→ℝ⟦X⟧)(N:Filter Z)(k:ℕ):Prop:=∀ i ≤ k,∀ x,Tendsto (fun t=>coeff i (X t x)) N (𝓝 (coeff i (v x)))
lemma Learn.pip {v : I→ℝ⟦X⟧}{X: Z→I→ℝ⟦X⟧}{N:Filter Z}(H:Learn v X N p)(r:ℕ): Learn (Halo.pip v (r:=r)) (fun t x=> Halo.pip (X t) x) N p:=by
 induction r with
 | zero=> intro i hi z; simp [Halo.pip,tendsto_const_nhds]
 | succ r ih=>
    intro i hi z
    have he (U:I→ℝ⟦X⟧): coeff i (Halo.pip U z)=∑ j∈Finset.antidiagonal i,coeff j.1 (U (z 0))*coeff j.2 (Halo.pip U (Fin.tail z)):=by rw [show Halo.pip U z=U (z 0)*Halo.pip U (Fin.tail z) from Fin.prod_univ_succ _,coeff_mul] -- fix
    simp_rw [he];refine tendsto_finsetSum _ (fun j hj=>?_);have hv:=Finset.mem_antidiagonal.mp hj; exact (H j.1 (by omega) _).mul (ih j.2 (by omega) _)
lemma Learn.price {v : I→ℝ⟦X⟧}{X: Z→I→ℝ⟦X⟧}{N:Filter Z}(H:Learn v X N p)(ht:i ≤ p)(U:Packet I r)(h:quota U 1≠⊤)(hb:Full X p): Tendsto (fun t=>rhyme (X t) U i) N (𝓝 (rhyme v U i)):=by
 obtain ⟨c,hc,hq⟩:=hb.pipes r _ ht; let f(t:Z) (z:Tuple I r):=U z * coeff i (Halo.pip (X t) z);let g(z:Tuple I r):= U z*coeff i (Halo.pip v z)
 rw [quota_base] at h
 have he t z : ‖f t z‖ ≤ ‖U z‖*c.toReal :=by rw [show f t z= _ from rfl]; unfold f; rw [norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); apply (ENNReal.ofReal_le_iff_le_toReal hc).mp; rw [ofReal_norm]; exact hq t z
 exact tendsto_tsum_of_dominated_convergence ((tsum_enorm_ne_top_iff_summable_norm.mp h).mul_right c.toReal) (g:=g) (fun z=>(H.pip r i ht z).const_mul _) (Eventually.of_forall he)
lemma debt_vanish {x:Side→ℝ}(h : Carry Aug.light Aug.debt fun w=> ‖x w‖ₑ): Tendsto x atTop (𝓝 0):=by
 obtain ⟨Q,⟨C,p,hC,hs⟩,h⟩:=h
 have he(w): ‖x w‖ ≤ C.toReal*(w.val:ℝ)⁻¹:=by
    have hh: ‖x w‖ₑ ≤ C*ENNReal.ofReal (w.val:ℝ)⁻¹:= (h w).trans (mul_le_mul_left ((hs w).trans_eq (show C *(Aug.light.val w)^p=C by unfold Aug.light; simp)) _)
    convert (ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top)).mp ((ofReal_norm _).trans_le hh) using 1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
 have hp: Tendsto (fun w:Side=>(w.val:ℝ)) atTop atTop:= by apply tendsto_natCast_atTop_atTop.comp; refine tendsto_atTop_atTop.mpr fun x=>⟨⟨x+1,by omega⟩,fun u (hu:x+1≤ u.val)=> hu.trans' (by change x≤x+1;omega)⟩
 apply squeeze_zero_norm he; simpa using (tendsto_inv_atTop_zero.comp hp).const_mul C.toReal
end Lobe
end YM.RegulatorIR.Halo
