import YM.FVA2.Generator.Circuits
/-!
# Test for $-4$ residue vanishing by polynomial recovery along scaling

Evaluate same formal bulk first-order Wilson coefficient as in the X-space price
work (infinitesimal frame effect from changing the cutoff). At one vertex only the
cut of the Taylor weights at and below d survives in the admissible finite frame.
`Icon` here combines power law reading along scaled marks $a x$, not across RG
runs, and true limiting Euclidean ordinary polynomial in auxiliary $t$ through the
full small-spacing limit at fixed exterior projection. Proving it for actual
pieces in next files. Need continuum *moment* at degree d of that polynomial. This criterion
isn't a consumer of any first-order pricing law or limit of deployment.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Generator.Circuits
open Function Filter Set MeasureTheory XSpace
open XSpace.Lows XSpace.Mu XSpace.Tide XSpace.Playpen XSpace.Drama XSpace.Sail Lattice Further.FreeCovariance.KP
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}
local notation "PolyC"=>Polynomial ℂ
-- solely finite-dimensional coefficient recovery
private def song (m:ℕ)(s:ℝ):(Polynomial.degreeLT ℂ (m+1)) →ₗ[ℂ] ℂ where
    toFun p:=p.val.eval (s:ℂ)
    map_add' _ _:=Polynomial.eval_add
    map_smul' _ _:=Polynomial.eval_smul ..
private abbrev lowP (m:ℕ):=Polynomial.degreeLT ℂ (m+1)
private lemma meets (m:ℕ): FiniteDimensional ℂ (lowP m):=( Polynomial.degreeLTEquiv ℂ (m+1) ).symm.finiteDimensional
variable {ι: Type} {a:ι→ℝ}{L:Filter ι}{P:PolyC}{u:ι→PolyC} {n d k:ℕ}
private theorem once (h:PolyC): (∀ t:ℝ,h.eval (t:ℂ)=0)→ h=0:= fun he=> Polynomial.eq_zero_of_infinite_isRoot _ ( ( infinite_range_of_injective Complex.ofReal_injective ).mono (by rintro x ⟨t,ht⟩; subst x; exact he t ))
lemma extract (m:ℕ)(hb:P.natDegree≤m)(hu:∀ i,(u i).natDegree≤m) (H:∀ t:ℝ, Tendsto (fun i=> (u i).eval (t:ℂ)) L (𝓝 (P.eval (t:ℂ)))) (k:ℕ) : Tendsto (fun i=> (u i).coeff k) L (𝓝 (P.coeff k)):= by
    letI:= meets m; let g (p:PolyC)(h:p.natDegree≤m): lowP m:= (⟨p,by rw [lowP, Polynomial.degreeLT_succ_eq_degreeLE, Polynomial.mem_degreeLE, ← Polynomial.natDegree_le_iff_degree_le]; exact h⟩)
    have hs:= XSpace.Future.redeemBy (song m) (fun p hp=> ( Subtype.ext ( once p.val hp ) )) (A:= fun i=> g _ (hu i)) (x:= g _ hb) H; exact hs ((( Polynomial.lcoeff ℂ k ) ∘ₗ (Polynomial.degreeLT ℂ (m+1)).subtype ))
local notation "AA"=> E4→ Polynomial ℂ
-- one-sided ∞ pressure here; pricing along a→0⁺ at arbitrary y may require $NeBot$. For now specialize norm for this call
abbrev bins (p:PolyC)(h:ℝ):= p.eval (h:ℂ)
structure Icon (a:ι→ℝ)(L:Filter ι) (d n:ℕ)(p:Tile G)(v: Hat G d)(Q:E4→Polynomial ℂ): Prop where
    reach (h:ℝ)(x:E4)(hx:x≠0): Tendsto (fun i=> (a i:ℂ)⁻¹^n * view (XSpace.Scale.orchestra d (h*a i) v) (overture d (p (mark (a i) x)))) L (𝓝 (bins (Q x) h))
open Polynomial
variable (Q:Tile G)(v:Hat G d)
def weigh (c:ℕ): Module.Dual ℂ (Stamp G):= (view v).toLinearMap ∘ₗ Lows.Cut coin c ∘ₗ (overture d).toLinearMap
-- coeff extraction.Weight fixed d. Note uniform decay across the covering lattice in the `Book` part, no n times claims.
private def track (d n:ℕ){G:Gauge}(Q:Tile G)(v:Hat G d)(h:ℝ)(x:Cover) : Polynomial ℂ:= ∑ i∈ Finset.range (n*(1+d)+1), Polynomial.monomial i ( (h:ℂ)⁻¹^n*(h:ℂ)^i * weigh v i (Q x))
lemma returns (hb:Book G n Q)(t:ℝ)(s:ℝ)(x:Cover) : bins (track d n Q v t x) s= (t:ℂ)⁻¹^n * view (XSpace.Scale.orchestra d (s*t) v) (overture d (Q x)) := by
    unfold track bins; rw [uncut _ _ (recorder d hb x),eval_finsetSum,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [ eval_monomial,Complex.ofReal_mul, mul_pow ]; unfold weigh; dsimp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply]; ring
lemma pays (t:ℝ)(x:Cover): (track d n Q v t x).natDegree≤n*(1+d):= by
    unfold track; apply Polynomial.natDegree_sum_le_of_forall_le; intro i hi; exact (natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) -- verify
lemma part (t:ℝ)(x:Cover)(i:ℕ)(h:i≤n*(1+d)): (track d n Q v t x).coeff i=(t:ℂ)⁻¹^n * (t:ℂ)^i * weigh v i (Q x):= by
    rw [track,finsetSum_coeff]; simp only [coeff_monomial,Finset.sum_ite_eq',if_pos,Finset.mem_range,h,Nat.lt_succ_iff] -- maybe
section go
variable {P:E4→ Polynomial ℂ}(h:Tendsto a L (𝓝 0))(he:∀ᶠ i in L,0<a i)
variable (hQ:Book G n Q)(H:Icon a L d n Q v P)(ht:d+4≤n)(hy:k≤d)
include he hQ H ht hy
set_option quotPrecheck false
local notation:max "c!"=> if n=d+4 ∧ k=d then (fun x:E4=> (P x).coeff k) else (0:E4→ℂ)
include h in
lemma ranked : arrived L a (fun x=> weigh v k (Q x)) (if n=d+4 ∧ k=d then (fun x:E4=> (P x).coeff k) else 0) 4 := by
    intro x hx; let d':= n*(1+d); have hv : k ≤ d':= le_trans ( Nat.le_trans hy (Nat.le_trans (Nat.le_add_right d 4) ht) ) (show n≤ n*(1+d) from Nat.le_mul_of_pos_right n (by omega)); have hk:= extract (u:=fun i=> track d n Q v (a i) (mark (a i) x)) (L:=L) (max (P x).natDegree d') (le_max_left ..) (fun i=> (pays _ _ _ _).trans (le_max_right ..)) (fun t=> (H.reach t x hx).congr ( fun i=> ( returns _ _ hQ _ _ _ ).symm )) k
    simp_rw [part Q v _ _ k hv] at hk
    have hm(n':ℕ){i}(ha:0<a i) : ( (a i:ℂ)^(n-(k+4)) ) * ( (a i:ℂ)⁻¹^n * (a i:ℂ)^k*weigh v k (Q (mark (a i) x)))= (a i:ℂ)⁻¹^4*weigh v k (Q (mark (a i) x)) := by
       let z:=(a i:ℂ); have hz:z ≠ 0:=by unfold z; exact_mod_cast ha.ne'
       have ht(z:ℂ)(hz:z≠0) (y:ℂ): z^(n-(k+4)) * (z⁻¹^n*z^k*y)= z⁻¹^4*y := by
           rw [inv_pow,inv_pow,show z^n=z^(n-(k+4)) * (z^k*z^4) from ( by rw [← pow_add,← pow_add]; congr 1; omega )]; field_simp
       exact ht _ hz _
    have hk':= ( Complex.continuous_ofReal.continuousAt (x:=0) |>.tendsto.comp h ).pow (n-(k+4)) |>.mul hk; rw [ Complex.ofReal_zero, show (0:ℂ)^(n-(k+4)) * _=c! x from ?_ ] at hk'; exact hk'.congr' (he.mono fun i hi=> hm n hi)
    by_cases ht': n=d+4 ∧ k=d; · rw [ht'.1,ht'.2]; simp
    rw [ if_neg ht',zero_pow ( by omega ),zero_mul ]; rfl
variable (χ:Shade.Cut)(t:ℝ)(h':0<t) [L.IsCountablyGenerated]
include h h'
theorem priced : Tendsto (fun i=> weigh v k (Shade.measure χ (t*a i) Q - Shade.measure χ (a i) Q)) L (𝓝 (∫ x:E4, tilt χ t x * (if n=d+4 ∧ k=d then (P x).coeff k else 0))) := by
    obtain ⟨C,hC,hz⟩:=steam_row Q hQ v k; let f(x:Cover):= weigh v k (Q x); have he':= ranked Q v h he hQ H ht hy; have hp(x): c! x= if n=d+4 ∧ k=d then ( P x ).coeff k else 0:= by by_cases h:n=d+4∧k=d <;> simp only [↓reduceIte,h] <;> simp_all
    have hv : ∀ x:Cover, ‖f x‖ ≤ C * (area x ^4)⁻¹ := by
       intro x; have hg:= ( show 1≤ area x from room _ ); refine (hz x).trans ?_; rw [mul_assoc,carry_cost]; gcongr C* ?_; rw [show area x^n= area x^(n-4)* area x^4 from (by rw [ ← pow_add ]; congr 1; omega )]; field_simp; gcongr; omega
    obtain HH:= perimeter χ t h' h he f c! hC hv he'; simp_rw [ hp ] at HH; refine HH.congr fun i=>?_ ; rw [map_sub]; simp_rw [Shade.quick_sum,map_sum,map_smul ]; rfl
end go
end YM.FVA2.Generator.Circuits
