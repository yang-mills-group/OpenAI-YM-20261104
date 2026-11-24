import YM.FormalBulk08.Shore.Sum
import YM.FormalBulk08.Reef.Safe

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Shore
open Lava Gorge Lattice Laurent Bloch Filter Set Function Reef Wilson Stationary
open Wick Lotus Orb Series PowerSeries Jets
open scoped BigOperators Classical ENNReal Topology ContDiff Matrix.Norms.Frobenius
variable {I J : Type*} {G : Gauge} {r : ℕ} (n : Side)

lemma robust (p : Side→Pap I) (t : Pap I) [Fintype I] (Q : Side→ℝ) (N : ℕ→ℕ) (a b : I→Pap J)
    (he : ∀ j,∀ᶠ n in atTop, ∀ l,N j<l→ marble l (coeff j (p n))=0)
    (h : ∀ j r,0<r → ∀ v,Tendsto (fun n=>Q n*marble r (coeff j (p n)) v) atTop (𝓝 (marble r (coeff j t) v)))
    (hp : ∀ᶠ n in atTop, roam ℝ a (p n)=roam ℝ b (p n)) : roam ℝ a t=roam ℝ b t := by
   have hT (j l) (hl : N j<l): marble l (coeff j t)=0 := funext fun v=> tendsto_nhds_unique (h _ _ (by omega) v) (tendsto_const_nhds.congr' (by filter_upwards [he j] with n hn; simp [hn _ hl]))
   ext1 m; apply sub_eq_zero.mp; rw [slime]; ext1 d; simp only [MvPolynomial.coeff_sum,MvPolynomial.coeff_zero]
   let f (j _n : ℕ):= insertAt ℝ a (coeff j t)-insertAt ℝ b (coeff j t)
   let g j n := insertAt ℝ a (coeff j (p n))-insertAt ℝ b (coeff j (p n)); let H:=tendsto_finsetSum (Finset.range (m+1)) (f:=fun j n=> Q n*MvPolynomial.coeff d (coeff m (g j n*X^j))) (a:=fun j=> MvPolynomial.coeff d (coeff m (f j m*X^j))) (fun j _=>lab m j _ _ _ p t Q (N j) (he j) (hT j) (h j));
   exact tendsto_nhds_unique H (tendsto_const_nhds.congr' (by filter_upwards [hp] with n hn; rw [←Finset.mul_sum,←MvPolynomial.coeff_sum]; unfold g; rw [←slime,hn,sub_self,MvPolynomial.coeff_zero,mul_zero]))

lemma civic_up (p : Pap (wire G n)) (h : Civic p) (j r) : Up (rancho p j r) := by
   intro x
   let f : (wire G n)≃(wire G n):= tint x
   let a:=fun z:Jets.Rays (wire G n)=> z ∘ (id: wire G n→wire G n);
   let b:= fun z:Jets.Rays (wire G n)=> z ∘ f
   have he : ∀ z:Jets.Rays (wire G n), input G n (b z)= pull (1:Signed) x (input G n (a z)) := by
       intro z; funext i; rw [pull_one]; unfold input; -- represent natural
       unfold Lattice.translate;        simp_rw [Work.F03.represent_link]; congr
   have hh:=h 1 x (wire G n) a b (fun _ _=>1) rfl rfl (contDiffAt_pi.mpr fun _=>contDiffAt_apply ..) (contDiffAt_pi.mpr fun _=>contDiffAt_apply ..) (fun _=>contDiffAt_const) ⟨1,rfl⟩ (.of_forall fun z=>by rw [he]; ext i; simp [Lattice.gauge])
   unfold a b at hh; rw [fit_translate,fit_translate] at hh
   have hk:= congr_arg (coeff j) hh; simp only [coeff_map] at hk
   have hx := congr_arg (marble r) hk; -- ensure pebble form
   intro v; let w:=f ∘ v
   have ht : rancho p j r = jetty f.symm (rancho p j r) := by
      change marble r (MvPolynomial.rename (R:=ℝ) id _) = marble r (MvPolynomial.rename (R:=ℝ) f _) at hx
      rw [MvPolynomial.rename_id_apply,pebble,cores_once] at hx; exact hx
   have hg:=congr_fun ht w; apply hg.trans; unfold jetty; congr 1; exact funext fun i=>f.symm_apply_apply _
end YM.FormalBulk08.Shore
