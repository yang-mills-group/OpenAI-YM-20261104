import YM.FVA2.Generator.Solve1
/-!
# K2 annulus resonance: complete cancellation for the lattice mark normalization

This weight DOES require summing exterior and internal leg polarizations with the actual
roles of those legs at V3. Assemble each farm exactly holding fixed colors in ordering of
its attached then exterior slots. The role exchange in expansions is a simple commutation (next
chapter). The mathcal V₃ experience actually keeps the single unused mode m at the exterior,
δ for cov colors inside `high`, and (crucially) the orbital polynomials producing the moment
are of a Clean jet because we read true *TaylorGauge* prescription columns. See also `Solve1`. $a→0$ proof resources at fixed order not IR estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Generator.Seals.Borders
open Function Set Filter XSpace Pages Center XSpace.Litter XSpace.Scale XSpace.Trace XSpace.Lows XSpace.Mu RG12.Strike Lattice MeasureTheory
open Exterior Hygro Prices Circuits Polynomial
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{n d:ℕ}
-- First isolate sole weight of exterior slot. Avoid convergence order. Run API diagonal.
variable {ι:Type}{L:Filter ι}[L.IsCountablyGenerated]{a:ι→ℝ}(S:Tendsto a L (𝓝 0))(h:∀ᶠ i in L,0<a i)
variable (χ:Shade.Cut)(s:ℝ)(hs:0<s)(B:Hat G d)
def pole (q r:Addr G)(x y z:Bond G)(m:Fin (d+1))(w:MultiplierEstimates G):ℂ:= μLand χ s (fun t=> Hygro.high q x t * Hygro.high r y t * screen B z m t * upcharge B w)
def round (q r:Addr G)(x y z:Bond G)(m:Fin (d+1))(w:MultiplierEstimates G) :ℂ:= RG12.Strike.toll round0 (fun t=>Hygro.high q x t * Hygro.high r y t * screen B z m t) s * upcharge B w
abbrev debit (x y z:Bond G)(q r:Addr G)(w:MultiplierEstimates G):= gem q x * gem r y * right z * Pages.left w
private lemma bills (p:Bond G): p.fee.cost=1+p.k.length:=rfl
private lemma grade (q r:Addr G): score q.L r.L+1=q.cost+r.cost:=by unfold score; rw [Pages.price,Pages.price]; omega
set_option quotPrecheck false
-- $fCov(t) * m.loc - external q; true exponents, $Canon𝕌$
variable (q r:Addr G)(x y z:Bond G)(ht:x.fee.cost+y.fee.cost+z.fee.cost=4) (m:Fin (d+1)) (hm:m.val=score q.L r.L) (w:MultiplierEstimates G)
include hs S h ht hm in
lemma weld (hw:wage w+q.cost+r.cost=d): run L a χ s B (debit x y z q r w) (round s B q r x y z m w):=by
    obtain H:=gains S h χ s hs B ((((rents S h B x q).times (rents S h B y r)).times (rising S h B z)).times (entering S h B w)) (by omega)
    let F(t:E4):= high q x t * high r y t * screen B z m t; let v:= upcharge B w; have hz : z.k.length ≤ m.val:= by rw [bills,bills,bills] at ht; rw [hm]; unfold score; omega
    let M:= x.k.length+q.L.length+3+(y.k.length+r.L.length+3); let f:=Hygro.high q x * Hygro.high r y; let g:= screen B z m; have hp : pole χ s B q r x y z m w=round s B q r x y z m w:= by
       change RG12.Strike.toll (rcast χ) (fun x=> F x * v) s= RG12.Strike.toll round0 F s * v; rw [factor s]; apply congr_arg (·*v); change μLand _ _ (f*g)= RG12.Strike.toll round0 (f*g) s; apply radial χ s hs (m:=M) ((charged ..).times (charged ..)) (chains _ _ _ hz); unfold M; rw [bills,bills,bills] at *; rw [hm]; unfold score; omega
    rw [← hp]
    have he : weight χ s (outgoing q x * outgoing r y * rugged B z * deco (wage w) (upcharge B w)) d=pole χ s B q r x y z m w:= by
       unfold weight pole; apply congr_arg (μLand χ s); funext t; -- unknown metav! use explicit P.
       simp only [deco, outgoing,rugged,Pi.mul_apply,Finset.sum_mul,Finset.mul_sum, finsetSum_coeff, monomial_mul_monomial, coeff_monomial, Nat.zero_add]
       rw [Finset.sum_eq_single m,if_pos (by have he:= grade q r; omega)]; intro j _ hj; apply if_neg; have hv : j.val≠m.val:= fun h=>hj (Fin.ext h); have h':= grade q r; omega; simp
    rw [he] at H; exact H
-- cancellation. Hold ordered slots' COLORS x,y,z; orientation of Farm selects axes & D.
variable (θ:Farm)(i j:Axis)(X Y Z:G.ColorIndex)
def lea : Bond G:= ⟨stung θ i,activeAt θ i j,X⟩
def peal : Bond G:= ⟨[],alsoAt θ i j,Y⟩
def free : Bond G:= ⟨spike θ i,farAt θ i j,Z⟩
include hs hm
private abbrev speed (m:ℕ) (q r:Addr G)(X Y:G.ColorIndex)(B:Hat G d)(w:MultiplierEstimates G):ℂ:= height (q.L.length+1) q.c X * height (r.L.length+1) r.c Y * τ m * upcharge B w
/-- No exterior resonance. d compatible with tower family by use of Param `A` independent of Farm choice. -/
theorem pay2 (A:Maxwell.TaylorTower G): ∑ i:Axis,∑ j:Axis, round s (Bracket.seat d A) q r (lea θ i j X) (peal θ i j Y) (free θ i j Z) m w=0:= by
    let V:=Bracket.seat d A; let w':=hunt round0 s; let p:=slate (fun i=>panel V m i Z) 0; let σ:= kite q; let ρ:=kite r; let u:= q.L; let v:=r.L; let M:=m.val; have hHC:Clean p (score q.L r.L):= hm ▸ Harmony.clean A m Z -- dependent warning
    let C:=speed M q r X Y V w; let C':=speed (M-1) q r X Y V w
    have hh(V₀ f:R→ℂ)(d:ℂ): (∫ x:R,V₀ x)= (∫ x:R,f x)*d→ (∫ x:R,V₀ x)*upcharge V w=(∫ x:R,f x)* (d* upcharge V w):= fun hx=> hx ▸ mul_assoc ..
    cases θ with
    | alpha=>
       have he (i j:Axis): round s V q r (lea .alpha i j X) (peal .alpha i j Y) (free .alpha i j Z) m w= (∫ x:R, w' x * sep (score u v) (p j) x*( RG12.Strike.leg σ u j [i] x*RG12.Strike.leg ρ v i [] x)) * C:=by
           unfold round RG12.Strike.toll; unfold C speed; apply hh; rw [← integral_mul_const]; apply integral_congr_ae; filter_upwards with t; change w' t * (high q ⟨[i],j,X⟩ t * high r ⟨[],i,Y⟩ t * screen V ⟨[],j,Z⟩ m t)=_ -- other side
           rw [Harmony.bill]; unfold Hygro.high; dsimp only; change _ = _ * (height _ _ _ * height _ _ _ * τ m.val) -- check
           rw [show score u v=m.val from hm.symm]; unfold σ ρ u v p; ring
       change (∑ i:Axis,∑ j:Axis, round s V q r (lea .alpha i j X) (peal .alpha i j Y) (free .alpha i j Z) m w)=0; simp_rw [he,← Finset.sum_mul]; change rowA p u v σ ρ w' *C=0; rw [sinkA,zero_mul]; exacts [ Hygro.gauge _, dries roundS _ hs, hHC ] -- order
    | beta =>
       have he (i j:Axis): round s V q r (lea .beta i j X) (peal .beta i j Y) (free .beta i j Z) m w= (∫ x:R, w' x * sep (score u v) (p i) x*( RG12.Strike.leg σ u j [i] x*RG12.Strike.leg ρ v j [] x)) * C:=by
           unfold round RG12.Strike.toll; unfold C speed; apply hh; rw [← integral_mul_const]; apply integral_congr_ae; filter_upwards with t; change w' t * (high q ⟨[i],j,X⟩ t * high r ⟨[],j,Y⟩ t * screen V ⟨[],i,Z⟩ m t)=_
           rw [Harmony.bill]; unfold Hygro.high; dsimp only; change _ = _ * (height _ _ _ * height _ _ _ * τ m.val)
           rw [show score u v=m.val from hm.symm]; unfold σ ρ u v p; ring
       change (∑ i:Axis,∑ j:Axis, round s V q r (lea .beta i j X) (peal .beta i j Y) (free .beta i j Z) m w)=0; simp_rw [he,← Finset.sum_mul]; change rowB p u v σ ρ w' *C=0; rw [sinkB,zero_mul]; exacts [ dries roundS _ hs, hHC ]
    | delta =>
       have ht : m.val≠0:= by rw [hm]; unfold score; omega
       have he(i j:Axis): round s V q r (lea .delta i j X) (peal .delta i j Y) (free .delta i j Z) m w=(∫ x:R, w' x *sep (score u v-1) (fun l=>p j (i::l)) x*(RG12.Strike.leg σ u i [] x* RG12.Strike.leg ρ v j [] x))*C':=by
           unfold round RG12.Strike.toll; unfold C' speed; apply hh; rw [← integral_mul_const]; apply integral_congr_ae; filter_upwards with t; change w' t * (high q ⟨[],i,X⟩ t * high r ⟨[],j,Y⟩ t * screen V ⟨[i],j,Z⟩ m t)=_
           rw [Harmony.bits _ _ _ _ _ _ ht]; unfold Hygro.high; dsimp only; change _ = _ * (height _ _ _ * height _ _ _ * τ (m.val-1))
           rw [show score u v=m.val from hm.symm]; unfold σ ρ u v p; ring
       change (∑ i:Axis,∑ j:Axis, round s V q r (lea .delta i j X) (peal .delta i j Y) (free .delta i j Z) m w)=0; simp_rw [he,← Finset.sum_mul]; change rowC p u v σ ρ w' *C'=0; rw [sinkC,zero_mul]; exacts [ Hygro.gauge _, dries roundS _ hs, hHC ]
include S h
omit hm in -- derive score m≦d rather than ask.
theorem certified (A:Maxwell.TaylorTower G)(hw:wage w+q.cost+r.cost=d): (∑ i:Axis,∑ j:Axis,debit (lea θ i j X) (peal θ i j Y) (free θ i j Z) q r w) ∈ None L a χ s (Bracket.seat d A):= by
    let m:Fin (d+1):= ⟨score q.L r.L,by have hh:=grade q r; omega⟩; have he:= tendsto_finsetSum Finset.univ fun i _=> tendsto_finsetSum Finset.univ fun j _=> weld S h χ s hs (Bracket.seat d A) q r (lea θ i j X) (peal θ i j Y) (free θ i j Z) (by cases θ<;> rfl) m rfl w hw; rw [pay2 s hs] at he; swap; · rfl
    change run _ _ _ _ _ _ 0; unfold run; simp_rw [map_sum]; exact he
end YM.FVA2.Generator.Seals.Borders
