import YM.FVA2.O.Project.Dash
/-!
# Local uniqueness of compact OPE estimates

At finite truncation (`i < d`, all output weights through `k`). Need no bound
on higher perturbative orders or outputs. Coefficients agree at all log-scale times (radius>0)
once the power-log form is fixed. *Estimate* needed only in the short radius limit;
no regulator estimates involved. The log power bound can even depend on each
individual shape for the uniqueness.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Project
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh O.Bind
variable { G:Gauge }{ I:Type }{n m k i d:ℕ }{a b t:ℝ}{ u:Scan G n }{v:Scan G m}
variable { V:Arenas G }{ A:Album G }{ r c: FLog G n }
variable { x:Points n }{ y:Points m }{ s:Set (Points n) }
local notation "V0"=> install V
local notation "P"=> QuoteP u
abbrev By_F (f g:FLog G n)(x:Points n)(k i:ℕ): Prop:= ∀ t, BeforeT ( f t ) ( g t ) x k i
abbrev By_K (f g:FLog G n)(x:Points n)(k i:ℕ): Prop:= ∀ t, BeforeK ( f t ) ( g t ) x k i
lemma price_x (t:ℝ)(q:Q G): coeff i ( QuoteP u r t x q )= Score.fee t ( ( heft q:ℝ ) - (totalG u:ℝ) ) * coeff i ( r t x q ):= coeff_C_mul ..
lemma prices_F (h:By_F r c x k i): By_F ( P r ) ( P c ) x k i:= by
    intro t j ht v i hi; rw [price_x, price_x,h t j ht v i hi]
lemma prices_K (h:By_K r c x k i): By_K ( P r ) ( P c ) x k i:= by intro t j i hi; rw [price_x, price_x,h t j i hi]
lemma price_read (t:ℝ)(q:Toon G k): read_n V ( QuoteP u r t ) x i k q= Score.fee t ( (k:ℝ)-(totalG u:ℝ) ) * read_n V ( r t ) x i k q:= by
    unfold read_n Enh.detect; simp only [LinearMap.coe_mk, AddHom.coe_mk, finPath ]; simp_rw [ price_x t, Finset.mul_sum ]; exact Finset.sum_congr rfl ( fun _ _=>mul_assoc .. )
lemma step_one (t:ℝ)(q:Toon G k)(r:FLog G n)(u:Scan G n): coeff i (Submit V0 u ( Single ( flash q ) ) t r k x RootG)= coeff i ( party V0 ( squeeze t x ) RootG u ( Single ( flash q ) ) )-(sparse V0 ( QuoteP u r t ) k x RootG (Single ( flash q )) i + Score.fee t ((k:ℝ)-(totalG u:ℝ)) * read_n V ( r t ) x i k q):= by
    unfold Submit Basket; rw [map_sub,Bind.earn,← price_read ( V:=V ) t q ]; rfl
abbrev weighs (b:Toon G k)(t:ℝ)(V: Arenas G)(r:FLog G n)(x:Points n)(u:Scan G n)(i:ℕ): ℂ:= coeff i ( Submit (install V) u ( Single ( flash b ) ) t r k x RootG )
abbrev seeing (V:Arenas G)(r:FLog G n)(x:Points n)(b:Toon G k)(i:ℕ)(t:ℝ): ℂ:= read_n V ( r t ) x i k b
lemma sampled_v (h: By_F r c x k i)(he: By_K r c x k i)(u:Scan G n)(b:Toon G k): Score.fee t ((k:ℝ)-(totalG u:ℝ))*( seeing V r x b i t - seeing V c x b i t ) = weighs b t V c x u i - weighs b t V r x u i:= by
    have ht:= aligned ( A:=V0 ) ( y:=RootG ) ( u:=Single ( flash b ) ) ( prices_F ( u:=u ) h t ) ( prices_K ( u:=u ) he t ); unfold weighs; rw [ step_one, step_one, ht ]; unfold seeing; rw [mul_sub]; abel
abbrev P_here (X:FLog G n)(x:Points n)(k i:ℕ): Prop:= ∀ y:Grade G k, Rhythm ( fun t=> coeff i ( X t x ( Score.own y ) ) )
lemma looked_more (h: P_here r x k i)(b: Toon G k): Rhythm ( seeing V r x b i ):= by
    unfold seeing read_n Enh.detect; simp only [LinearMap.coe_mk,AddHom.coe_mk]; exact Rhythm.sum _ (fun j _=> Rhythm.mul ( h j ) (Rhythm.const ..))
lemma comeback (ht:x∈s)(hx:Exteriors A s r u k a d)(i:ℕ)(hv:i<d)(b:Toon G k): Rain ( (k:ℝ)+a-(totalG u:ℝ) ) (fun (_:Unit) t=> coeff i ( Submit A u (Single ( flash b )) t r k x RootG )) := Rain.pull ( hx 1 {RootG} (Single ( flash b )) isCompact_singleton ( singleton_subset_iff.mpr ok_wall ) i hv ) ( fun _=> (⟨x,ht⟩, ⟨RootG, mem_singleton _⟩) )
lemma strict_v (hF:By_F r c x k i)( hK:By_K r c x k i)( hr: P_here r x k i )( he:P_here c x k i )(hx:Exteriors V0 s r u k a d)( hp:Exteriors V0 s c u k a d)(ht:x∈ s)(hv:0<a)(he':i<d)(b:Toon G k): seeing V r x b i= seeing V c x b i:= by
    let b':ℝ:= ( (k:ℝ)-(totalG u:ℝ) ); let w(s:ℝ):= seeing V r x b i s-seeing V c x b i s; have hw(t:ℝ): w t= Score.fee (-t) b' * (weighs b t V c x u i -weighs b t V r x u i ):= by rw [← sampled_v ( V:=V ) hF hK u b,← mul_assoc,mul_comm ( Score.fee _ _ ) ( Score.fee _ _ ), fee_mul,one_mul ]; -- b' and both subtract defeq
    obtain hu:= Rain.minus ( comeback ht hp i he' b ) ( comeback ht hx i he' b ); have hx : Rain a ( fun (_:Unit) t=> w t ):= by
       simp_rw [hw]; have he: Rain (-b') ( fun (_:Unit) (t:ℝ)=> Score.fee (-t) b' ):= by simp_rw [ show ∀ t:ℝ,Score.fee (-t) b'=Score.fee t (-b') from ( fun i=>(by unfold Score.fee; simp) ) ]; exact Rain.all_fee
       exact Rain.size ( he.mul hu ) (by unfold b'; linarith)
    exact sub_eq_zero.mp ( Rhythm.asleep ( Rhythm.sub ( looked_more hr b ) ( looked_more he b ) ) ( ( Rain.lapse hx hv ).tendsto_at () ) )
lemma localOf (h:Ground V)(hp: Regular V)(ht:x∈ s)(hx:Exteriors V0 s r u k a d)( hQ:Exteriors V0 s c u k a d)( hv:0<a)(he:i<d)(hR:P_here r x k i)(hU:P_here c x k i)(hF:By_F r c x k i)(hK:By_K r c x k i): ∀ q:Grade G k,coeff i ( r t x ( own q ) )= coeff i ( c t x ( own q ) ):= by
    obtain H0:= LinearMap.ker_eq_bot.mp ( tactile h hp k ); exact congr_fun ( H0 ( a₁:=finPath x ( r t ) k i ) ( a₂:=finPath x ( c t ) k i ) (funext fun b=>congr_fun ( strict_v hF hK hR hU hx hQ ht hv he b ) t ))
-- Finite compatibility, require readers matched through this horizon only.
abbrev Matches_e (A:Album G)(u:Scan G n)(p:FLog G n)(s:Set (Points n))(k d:ℕ)(a:ℝ): Prop:= ∀ j≤k,Exteriors A s p u j a d
abbrev Patches_e (p:FLog G n)(s:Set (Points n))(k d:ℕ): Prop:= ∀ j≤k,∀ i<d, ∀ x∈s,P_here p x j i
lemma uniqueness {d k:ℕ}(h:Ground V)(he: Regular V)( hp:Matches_e V0 u r s k d a )(ht:Matches_e V0 u c s k d a)( hx:Patches_e r s k d )(hu:Patches_e c s k d)(hv:0<a): Same s k d ( r t ) ( c t ):= by
    intro x hx q hq i hi;
    suffices goal:∀ j ≤ k,∀ i<d,∀ t:ℝ,∀ u:Grade G j, coeff i ( r t x ( own u ))= coeff i ( c t x ( own u )) by exact goal (heft q) hq i hi t q.item
    intro j h'; induction j using Nat.strong_induction_on with | h j IH=>
       intro i hh; induction i using Nat.strong_induction_on with| h i ih=> exact fun _=>localOf h he hx ( hp j h' ) ( ht j h' ) hv hh ( ( by assumption : Patches_e r s k d ) j h' i hh x hx ) ( hu j h' i hh x hx ) (fun t j hj v k hk=> IH j hj ( hj.le.trans h' ) k ( lt_of_le_of_lt hk hh ) t v ) ( fun t v k hk=> ih k hk (lt_trans hk hh) t v )
lemma Markup.patch (hp:Markup r): Patches_e r s k d:= by intro j hj i hi x hx y; obtain ⟨C,h⟩:= hp.poly ( Score.own y ) i; exact ⟨C,h x ⟩
theorem settle (h:Ground V)(he: Regular V)(hA:OPEA V0 u r)( hp:OPEA V0 u c ): r=c:= by
    funext t x; by_cases hx:x∈conf n; swap; · rw [ hA.off t x hx,hp.off t x hx ];
    funext q; ext i; have he' := isCompact_singleton ( x:=x ); have hs:= singleton_subset_iff.mpr hx
    exact uniqueness ( u:=u ) ( s:={x} ) h he ( fun _ _=> hA.through _ he' hs _ ( i+1 ) ) ( fun _ _=> hp.through _ he' hs _ _ ) hA.toMarkup.patch hp.toMarkup.patch zero_lt_one x ( mem_singleton x ) q le_rfl i ( Nat.lt_succ_self i )
end YM.FVA2.O.Project
