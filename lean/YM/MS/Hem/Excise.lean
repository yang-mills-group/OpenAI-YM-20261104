import YangMills.WilsonProof.NativeSupport.YM.MS.Hem.Aryl
/-!
# Taylor decomposition of Mellin kernels ensures all derivatives integrate

Weight engineering axis h. Uniform z horizon not m height.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Hem
open Set Filter Function Finset MeasureTheory Metric Arc
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine
open scoped Topology ContDiff
variable {I:Type}{G:Gauge}{j m n k:ℕ}{x:ℂ}{R:ℝ}{F H:Mob G}
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
def haze (n:ℕ)(F:Mob G): Mob G := ∑ j∈Finset.range n,Tad F j
def clear (n:ℕ)(F:Mob G) : Mob G:= F - haze n F
@[simp] lemma haze_zero (F:Mob G): haze 0 F=0:=by simp [haze]
@[simp] lemma haze_step (n:ℕ)(F:Mob G): haze (n+1) F=haze n F+Tad F n := Finset.sum_range_succ ..
lemma haze_hol (f:ℂ→ Mob G)(h:Hol (disc R) f)(n:ℕ): Hol (disc R) (fun i=> haze n (f i)):= by
    induction n with| zero=> simp_rw [haze_zero]; exact Hol.zero| succ n ih=> simp_rw [haze_step]; exact ih.add (tad_hol f h n)
lemma clear_hol {f:ℂ→Mob G}(h:Hol (disc R) f)(n:ℕ) : Hol (disc R) (fun i=> Hem.clear n (f i)):= h.sub (haze_hol f h n)
lemma haze_price (hp:kPrice F)(n:ℕ): kPrice (haze n F):= fall_sum (Finset.range n) (f:=fun i (_:Unit)=> Tad F i) (fun i _=> tad_price hp i) (fun _=>zero_le_one)
lemma clear_p (hp:kPrice F)(n:ℕ): kPrice (Hem.clear n F):= fall_sub hp (haze_price hp n)
lemma erase_j (hp:kPrice F) (hm:m<n): Tad (haze n F) m=Tad F m:= by
    induction n with
    | zero=> omega
    | succ n ih=>
       rw [haze_step,t_plus (haze_price hp n) (tad_price hp n),t_already n hp m]
       split <;> rename_i h
       · subst m; suffices h : ∀ i≤n,Tad (haze i F) n=0 by rw [h n le_rfl,zero_add]
         intro j; induction j with| zero=> intro; rw [haze_zero,tad0]| succ j ih=> intro h; rw [haze_step,t_plus (haze_price hp j) (tad_price hp j),ih (by omega),t_already j hp n,if_neg (by omega:j≠n), zero_add]
       rw [ih (by omega),add_zero]
lemma flat (hp:kPrice F)(hm:m<n): Tad (Hem.clear n F) m=0:= by rw [Hem.clear,t_minus hp (haze_price hp n),erase_j hp hm, sub_self]
lemma tack (s:ℝ) : Alps.amount (m:ℂ) s = ↑(Real.exp s ^ m) := by rw [← Complex.ofReal_natCast,amount_mint, mul_comm]; exact congr_arg (Complex.ofReal) (by rw [mul_comm,Real.exp_nat_mul])
lemma move_tad (h:kPrice F)(n:ℕ)(c:ℂ)(t:ℝ): plow c t (Tad F n)=Alps.amount (c+n) t • Tad F n:= by
    funext m l; rcases lt_or_ge (n:ℤ) (mass l) with h1|h1; · simp only [plow,t_exc h1,t_exc (show (n:ℤ)<mass (sr t l) by rwa [price_sr]),mul_zero,smul_zero,Pi.smul_apply]
    let j:= ((n:ℤ)-mass l).toNat -- ray name
    let X(z:Mob G):=fieldVal (z m) (ray l) 1; change _= Alps.amount (c+n) t • Tad F n m l; obtain hv:= s_p_vector (Tad F n) (ray l) 1 t c; have hz:mass (ray l)+j=n:= by rw [mass,ray_dim]; change mass l+_=n; unfold j; omega
    rw [film ((h m ℝ (ray l)).smooth ()) hz,show stage j (fieldVal (F m) (ray l)) (Real.exp t • 1)= (Real.exp t ^ (j:ℤ)) • stage j ( fieldVal (F m) (ray l)) 1 from (form_diag _ _ rfl).scale ..] at hv -- LHS rewrites under stage maybe
    rw [← ray_sail l]; -- danger rewrites both l incl mass j etc intentional
    change (fieldVal (plow c t (Tad F n) m) (ray l) 1) =_ ; rw [hv]; have he : (mass (ray l):ℂ) + j=n:= by exact_mod_cast hz
    rw [show Tad F n m (sail (ray l) (1:ℝ))= _ from congr_fun (film (n:=n) ((h m ℝ (ray l)).smooth ()) hz) 1, ← he,zpow_natCast, Complex.real_smul,smul_eq_mul]; rw [← add_assoc,amount_add _ (j:ℂ), tack]; ring -- fold coercion
-- Taylor vanishing gives full jets shrinking
lemma fire (h:kPrice F)(n:ℕ)(w:Touch G m E){j:ℕ}(he:mass w+j<n): iteratedFDeriv ℝ j ( fieldVal (Hem.clear n F m) w) 0=0:= by
   let Q:= Hem.clear n F; let U:=fieldVal (Q m) w; have hs:ContDiff ℝ ∞ U:= ((clear_p h n) m E w).smooth ()
   let k':=(mass w + j).toNat; have ht: mass w+j=k':= (by have he:=dm w; unfold k'; omega)
   have hv : stage j U=0:=by rw [← film (F:=Q) hs ht,flat h (by omega)]; rfl
   refine Tensor.ext_diag _ _ (Analysis.sym_Jet (hs.contDiffAt.of_le (by exact_mod_cast le_top))) (fun _ _=>rfl) ?_; funext p; exact (smul_eq_zero.mp (congr_fun hv p)).resolve_left (by positivity)
lemma clear_pose (n:ℕ)(F:Mob G)(q:ℂ): Hem.clear n (q • F)=q • Hem.clear n F:= by simp only [Hem.clear,haze,t_pose,smul_sub,Finset.smul_sum]
end YM.MS.Hem
