import YM.FVA2.Generator.Cry
/-!
# Null resonant stencil: K0 (just unit patterns), K1, K3

For K1 we can hold every leg axis fixed. In fact tally exactly this cost on the full hoop at
both ends of the harvest, not only the directional infinitesimal increment. Clamping to
radial $\chi$ here only INSIDE the Euclidean integral, on the *total* charge-homogeneous product.
See Solve2 for K2 (after axis summation). Use the supplied `shave1`
(with weights as in `k1` below) for the K1 calculation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Generator.Seals
open Function Set Filter XSpace Pages Center XSpace.Litter XSpace.Scale XSpace.Trace XSpace.Lows XSpace.Mu RG12.Strike Lattice MeasureTheory
open Exterior Hygro Prices Circuits Polynomial
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{n k d:ℕ}
-- Diagonal occupancy. Other heights are cheaper: all null at once via vanishHigher.
-- Keep arbitrary Λ orientation. Clear submodule for stream linearity.
variable {ι:Type}{L: Filter ι} [L.IsCountablyGenerated]{a:ι→ℝ} (S:Tendsto a L (𝓝 0))(ha:∀ᶠ i in L, 0<a i)
variable (χ:Shade.Cut)(s:ℝ)(hs:0<s) (B:Hat G d)
abbrev μLand (χ: Shade.Cut)(s:ℝ)(f:E4→ℂ):= RG12.Strike.toll (rcast χ) f s
abbrev weight (χ:Shade.Cut)(s:ℝ)(P: Prices.Glow)(d:ℕ):= μLand χ s (fun x=> (P x).coeff d)
def run (L:Filter ι)(a:ι→ℝ)(χ:Shade.Cut)(s:ℝ)(B:Hat G d)(p:Tile G)(b:ℂ): Prop:= Tendsto (fun i=>δ χ s (a i) B d p) L (𝓝 b)
def None (L:Filter ι)(a:ι→ℝ)(χ:Shade.Cut)(s:ℝ)(B:Hat G d): Submodule ℂ (Tile G) where
    carrier := {p|run L a χ s B p 0}
    zero_mem':= by change run _ _ _ _ _ _ _; unfold run; simp [tendsto_const_nhds]
    add_mem' := by rintro f g (hf:run _ _ _ _ _ _ _) (hg:run _ _ _ _ _ _ _); change run _ _ _ _ _ _ _; unfold run at *; simpa only [map_add,add_zero] using hf.add hg
    smul_mem' := by rintro t f (hf:run _ _ _ _ _ _ _); change run _ _ _ _ _ _ _; unfold run at *; simpa only [map_smul,smul_eq_mul, mul_zero] using hf.const_mul t
include S ha hs in
lemma gains {P:Tile G}{Q:Prices.Glow}(h:Cast P n a L B Q)(hp:n=d+4): run L a χ s B P (weight χ s Q d):= by
    subst n; unfold run weight μLand RG12.Strike.toll; obtain he:= Circuits.priced _ _ S ha h.book h.toIcon le_rfl ( le_refl d ) χ s hs; simp_rw [Center.pay]; simp only [true_and,ite_true] at he; exact he
include S ha hs
-- shapes of the canonical Wick calculus. costs are values at state tested after slot order V3. no_count=0 & k3.
theorem empty (w:MultiplierEstimates G)(x y z:Bond G)(ht:x.fee.cost+y.fee.cost+z.fee.cost=4)(hh:wage w=d): Pages.right x *Pages.right y * Pages.right z * Pages.left w∈ None L a χ s B:=by
    obtain H:= gains S ha χ s hs B ((((rising S ha B x).times (rising S ha B y)).times (rising S ha B z)).times (entering S ha B w)) (by omega); unfold weight μLand RG12.Strike.toll RG12.Strike.paid at H
    simp only [Pi.mul_apply,deco,rugged,Finset.sum_mul,Finset.mul_sum,finsetSum_coeff,monomial_mul_monomial,coeff_monomial] at H
    simp only [show ∀ i j k:ℕ,1+i+(1+j)+(1+k)+wage w≠d from fun i j k=>by omega, ite_false,mul_zero,Finset.sum_const_zero,integral_zero] at H; exact H
omit S ha hs [L.IsCountablyGenerated] in
private lemma debt_pos (q:Addr G) : 0<q.cost:= by rw [Pages.price]; omega
-- use when ALL V fields contracted, spend right sum4, left slack by addr costs
theorem occupied (w:MultiplierEstimates G)(x y z:Bond G)(q r t:Addr G)(ht:x.fee.cost+y.fee.cost+z.fee.cost=4)(hh:wage w+q.cost+r.cost+t.cost=d) : gem q x * gem r y * gem t z * Pages.left w∈ None L a χ s B:=by
    have he:wage w≠d:= by have hb:=debt_pos q; omega
    obtain H:=gains S ha χ s hs B ( (((rents S ha B x q).times (rents S ha B y r)).times (rents S ha B z t)).times (entering S ha B w) ) (by omega); unfold weight μLand RG12.Strike.toll RG12.Strike.paid at H; change run _ _ _ _ _ _ _; simpa only [Pi.mul_apply,deco,outgoing,monomial_mul_monomial,coeff_monomial,Nat.zero_add,he,ite_false,mul_zero,integral_zero] using H
omit ha S
lemma radial {f g:E4→ℂ}{m n:ℕ}(hf:Garden f m)(hg:Mode n g)(ht:n+4=m) : μLand χ s (f*g)=RG12.Strike.toll round0 (f*g) s:= by
    refine Generator.exchange χ s hs (fun x hx=> ((hf.openSite x hx).continuousAt).mul ((hg.jet x trivial).continuousAt) ) ?_; convert hf.line.mul hg.law using 1; omega
omit [L.IsCountablyGenerated] hs in
lemma factor (f g:E4→ℂ)(C:ℂ): RG12.Strike.toll f (fun x=>g x*C) s= RG12.Strike.toll f g s * C:= by unfold RG12.Strike.toll RG12.Strike.paid; rw [←integral_mul_const]; exact integral_congr_ae ( Eventually.of_forall fun i=> (mul_assoc ..).symm)
private lemma k1 (q:Addr G)(v:Bond G){f:E4→ℂ}(h: Mode n f)(he:n+4=v.k.length+q.L.length+3): μLand χ s (Hygro.high q v*f) =0:= by
    rw [radial χ s hs (charged ..) h he]
    obtain hp:= shave1 (kite q) q.L round0 v.k v.j f 0 s roundS hs; rw [crit,if_pos (by omega),← he, Nat.add_sub_cancel] at hp; rw [show Hygro.high q v*f=(fun x=> layer (RG12.Strike.leg (kite q) q.L v.j v.k) f 0 n x * height (q.L.length+1) q.c v.color ) from ?_,factor s,hp,zero_mul] -- args? factor includes hs
    funext y; change _ * f y= layer _ _ _ _ y * _
    unfold Hygro.high layer; rw [(show fresco n f 0 y=f y from (h.paid y).symm)]; ring

-- isolate monomials of two exterior Taylor legs. packages Integrable and zero
private lemma lyric (q:Addr G)(x y z:Bond G)(i j:Fin (d+1))(w:MultiplierEstimates G)(txy:x.fee.cost+y.fee.cost+z.fee.cost=4)(he:d=wage w+q.cost):
    let f(t:E4):ℂ:=if 0+(1+i.val)+(1+j.val)+wage w=d then high q x t * screen B y i t * screen B z j t * upcharge B w else 0
    Integrable (RG12.Strike.paid (rcast χ) f s) ∧ μLand χ s f=0:= by
    by_cases hi:y.k.length ≤ i.val ∧ z.k.length ≤ j.val ∧ 0+(1+i.val)+(1+j.val)+wage w=d
    · simp_rw [if_pos hi.2.2]; let a:=i.val-y.k.length; let b:=j.val-z.k.length; let f:=screen B y i * screen B z j; have H: Mode (a+b) f:= (chains B y i hi.1).mul (chains B z j hi.2.1); let g:= high q x * f; let u:= upcharge B w
      have hZ:(fun t:E4=> high q x t * screen B y i t * screen B z j t * upcharge B w)=(fun t=> g t * u):=by funext t; unfold g f u;  simp only [Pi.mul_apply]; ring -- fill
      change Integrable (RG12.Strike.paid (rcast χ) (fun t:E4=> Hygro.high q x t * screen B y i t * screen B z j t * upcharge B w) s) ∧ μLand χ s (fun t:E4=> high q x t * screen B y i t * screen B z j t * upcharge B w) =0; rw [hZ]; constructor
      · exact Generator.rests χ s hs (g:=fun t=>g t*u) (fun t ht=> (((charged q x).openSite t ht).continuousAt.mul ( (H.jet t trivial).continuousAt )).mul continuousAt_const)
      unfold μLand
      rw [factor s, show g=Hygro.high q x * f from rfl, ← μLand, k1 χ s hs _ _ H (by unfold Fee.cost Bond.fee at txy; have h' := Pages.price q; obtain ⟨i,j,K⟩:=hi; unfold a b; dsimp only at *; omega),zero_mul]
    let f(t:E4):ℂ:=if 0+(1+i.val)+(1+j.val)+wage w=d then high q x t * screen B y i t * screen B z j t * upcharge B w else 0
    change Integrable (RG12.Strike.paid (rcast χ) f s) ∧ _; have hz : f=0:=by
        funext t; unfold f; split_ifs with hk
        · by_cases hv:i.val<y.k.length; rw [dusty B y i hv]; simp
          have hv':j.val<z.k.length:=by omega
          rw [dusty B z j hv']; simp
        rfl
    change _ ∧ μLand χ s f=0; unfold μLand RG12.Strike.toll; rw [hz,show RG12.Strike.paid (rcast χ) (0:R→ℂ) s=fun _=>0 from funext fun x=> mul_zero .. ]; simp

include S ha
lemma solo (w:MultiplierEstimates G)(x y z:Bond G)(q:Addr G)(ht:x.fee.cost+y.fee.cost+z.fee.cost=4)(hh:wage w+q.cost=d): gem q x * Pages.right y * Pages.right z * Pages.left w ∈ None L a χ s B := by
    obtain H:= gains S ha χ s hs B ((((rents S ha B x q).times (rising S ha B y)).times (rising S ha B z)).times (entering S ha B w)) (by omega); unfold weight μLand RG12.Strike.toll RG12.Strike.paid at H; simp_rw [Pi.mul_apply,deco,rugged,outgoing,Finset.mul_sum,Finset.sum_mul,finsetSum_coeff, monomial_mul_monomial, coeff_monomial, Finset.mul_sum ] at H
    let f (i j:Fin (d+1)) (t:E4):ℂ:= if 0+(1+i.val)+(1+j.val)+wage w=d then high q x t * screen B y i t * screen B z j t * upcharge B w else 0
    have he(i j:Fin (d+1)) := lyric χ s hs B q x y z i j w ht hh.symm
    let g (i j:Fin (d+1)) := RG12.Strike.paid (rcast χ) (f i j) s
    have hx:(∫ t:E4,∑ j:Fin (d+1),∑ i: Fin (d+1),g i j t) = 0:= by
       rw [integral_finsetSum Finset.univ (fun i _=> show Integrable (fun x=>∑ j:Fin (d+1), g j i x) from integrable_finsetSum _ (fun j _=> (he j i).1))]; apply Finset.sum_eq_zero; intro i _; rw [integral_finsetSum Finset.univ (fun j _=> show Integrable (g j i) from (he j i).1)]; exact Finset.sum_eq_zero fun l _=>(he l i).2
    change run L a χ s _ _ (∫ t:E4,∑ j:Fin (d+1),∑ i:Fin (d+1),g i j t) at H; rw [hx] at H; exact H
end YM.FVA2.Generator.Seals
