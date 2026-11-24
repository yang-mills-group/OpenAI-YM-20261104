import YM.MSbar.Alto.Siege
/-! Polynomial budgets.Survive explicit split top same slope.C constant independent.L brand. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Alto
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Parma Tin Bronze Asymptotics Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {X:Type*} {F G: X→ℝ} {r i j p q:ℕ}
noncomputable def Tuition (g:ℝ→ℝ)(p:ℕ) := Asymptotics.IsBigO atTop g (fun x=>x^p)
namespace Tuition
variable {f g :ℝ→ℝ} {B:ℝ}
lemma constant (a:ℝ) : Tuition (fun _=>a) 0:=by
   apply Asymptotics.isBigO_iff.mpr; exact ⟨‖a‖,Eventually.of_forall fun i=> by simp⟩
lemma front (q:ℕ): Tuition (fun x=>x^q) q:= isBigO_refl ..
lemma strong (h:Tuition f p)(hv:p≤q): Tuition f q:=by
   refine h.trans (Asymptotics.isBigO_iff.mpr ⟨1,?_⟩); filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx; have hp:0 ≤ x:=zero_le_one.trans hx; rw [one_mul,Real.norm_of_nonneg (pow_nonneg hp p),Real.norm_of_nonneg (pow_nonneg hp q)]; exact pow_le_pow_right₀ hx hv
lemma act (a:ℝ)(p:ℕ): Tuition (fun _=>a) p:= strong (constant a) (by omega)
lemma unionT(h: Tuition f p)(hh:Tuition g q): Tuition (fun x=>f x+g x) (max p q):= IsBigO.add (strong h (le_max_left ..)) (strong hh (le_max_right ..))
lemma same (h:Tuition f p)(hh: Tuition g p): Tuition (fun x=> f x+g x) p:= IsBigO.add h hh
lemma scaled (r:ℝ)(h:Tuition f p): Tuition (fun x=>r*f x) p:= h.const_mul_left r
lemma solder (h: Tuition f p)(hg:Tuition g q) : Tuition (fun x=> f x*g x) (p+q):=by
    have he:= h.mul hg; show _ =O[_] _; simp_rw [pow_add]; exact he
lemma powered (h:Tuition f p)(k:ℕ): Tuition (fun x=>f x^k) (p*k):=by
   induction k with
   | zero=> simpa using! constant 1
   | succ i ih=> rw [Nat.mul_succ]; simp_rw [pow_succ]; exact solder ih h
section
variable {σ:Type}
lemma items (s:Finset σ)(F:σ→ℝ→ℝ)(h:∀ i∈s,Tuition (F i) p) : Tuition (fun x=>∑ i∈s,F i x) p:=by induction s using Finset.induction with |empty=> simpa using! act 0 p | insert i s he ih=>simp_rw [Finset.sum_insert he]; exact same (h _ (mem_insert_self ..)) (ih fun j hj=>h _ (mem_insert_of_mem hj))
end
lemma down (h:Tuition f p)(he:p<q): Tendsto (fun x:ℝ=> f x/x^q) atTop (𝓝 0):=by
    obtain ⟨C,hC⟩:= isBigO_iff.mp h
    have ht:= (tendsto_pow_atTop (α:=ℝ) (show q-p≠0 from by omega)); let v:ℝ→ℝ:= fun x=> C/x^(q-p)
    refine tendsto_zero_iff_norm_tendsto_zero|>.mpr ((squeeze_zero' (Eventually.of_forall (fun x:ℝ=> norm_nonneg (f x/x^q))) (?_:∀ᶠ x in atTop, ‖f x/x^q‖ ≤ v x) (show Tendsto v atTop _ from tendsto_const_nhds.div_atTop ht)))
    filter_upwards [eventually_gt_atTop (0:ℝ), hC] with x hx hh; unfold v; rw [norm_div]; refine (div_le_div_of_nonneg_right hh (norm_nonneg _)).trans_eq ?_; show _/(‖x^q‖) = _; rw [Real.norm_of_nonneg (pow_nonneg hx.le p),Real.norm_of_nonneg (pow_nonneg hx.le q),show x^q=x^p*x^(q-p) from ?_]; field_simp; rw [←pow_add]; congr; omega
end Tuition
-- drivers;
def steps (q p m:ℕ): ℕ:=q+p+m -- no
noncomputable def dyadicGrowthDegree (i r:ℕ):=2^i*r
open Tuition
lemma fareK (r j p m q:ℕ)(s C:ℝ)(f:ℝ→ℝ)(h:Tuition f r) (i:ℕ) : Tuition (fun t=>Whisk.rail j p m s (f t) i) (dyadicGrowthDegree i r):=by
   induction i with
   | zero=> have hp':dyadicGrowthDegree 0 r=r:=by simp [dyadicGrowthDegree]
            rw [hp']; exact h
   | succ i ih=>
       let f(t:ℝ):=Whisk.rail j p m s (f t) i -- capture; engine stair
       let k:=dyadicGrowthDegree i r; let p':=dyadicGrowthDegree (i+1) r; have hp:p'=k*2:=by unfold p' k dyadicGrowthDegree; ring
       have hF:Tuition f k:= ih; have hx:Tuition f p':=strong ih (by omega)
       have he:Tuition (fun x=> f x ^ 2) p':= hp.symm ▸ powered hF 2
       simp only [Whisk.rail,Whisk.stair]; apply same hx; exact same (same hx (scaled s hx)) (scaled _ (scaled _ (same he (scaled s he)))) -- orientation multiplication parentheses
lemma river (r p m q:ℕ)(a:ℝ)(f:ℝ→ℝ)(h: Tuition f p): Tuition (fun t=> driver r q m a (f t)) (dyadicGrowthDegree (Whisk.ribbon r q) p):= scaled _ (fareK p m _ q 0 a 0 f h _)
-- term n.Etc.
def jewel (n d i j:ℕ):= d*i+n*d*j
lemma termB (n d i j:ℕ) : Tuition (fun x=> term n i j (x^d)) (jewel n d i j):=by
    let B:= ((n+1:ℕ):ℝ)
    unfold term jewel; apply scaled; refine solder (powered (scaled B (front d)) _) ?_; rw [Nat.mul_comm n d]; apply powered; exact scaled B (powered (same (act ..) (scaled B (front d))) n)
lemma salvo (n d:ℕ): Tuition (fun x=> Bronze.salary n (x^d) (x^d)) (jewel n d (n+3) n+d):=by
    let f(x:ℝ) := Finset.range n; unfold Bronze.salary; refine solder (items _ _ fun i hi=> ?_) (front d); let s : ℕ := n+3
    have hv : i < n:= mem_range.mp hi
    apply items (Finset.range (i+2+1)) (fun j x=> term n j i (x^d)); intro i he; apply strong (termB ..); unfold jewel; gcongr; have h:= mem_range.mp he; omega
end YM.MSbar.Alto
