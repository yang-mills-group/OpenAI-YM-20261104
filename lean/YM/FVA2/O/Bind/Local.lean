import YM.FVA2.O.Bind.Roof
/-!
# Local uniqueness for the FAR OPE

Free Gram tests (`detect` and `tactile`) and the large-distance bound from a far approximation
with positive extra decay; induction in output dimension and moment order. Use for consistency
of finite-horizon and order choices (`uniqueK`, `Same`). See `Weather` for also extracting
continuity in the shapes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Bind
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh
variable { G:Gauge }{n m k i d : ℕ }{v:ℝ }{ V:Arenas G }{B:ℝ→Frames G}{R:ℝ→Cn}{A:Album G}
variable {s:Set (Points n)}{K:Set (Points m)}{y:Points m}{x:Points n}{f g:Fable G n}{a:Scan G n}{u:Scan G m} {w k':ℕ}
local notation "A0"=> install V
abbrev vision (A:Album G)(f:Fable G n)(a:Scan G n)(b:Toon G k)(x:Points n)(t:ℝ)(i:ℕ):ℂ := Score.fee (-t) ( wght b )*sample A f a b x t i
lemma Blot (h:Law V R B)(ht:Fiasco A0 s k v d a f)(hv:0<v)(hi:i<d)(b:Toon G k): TendstoUniformly (fun t (x:↥s)=> vision A0 f a b x.val t i) (fun (x:↥s)=> read_n V f x.val i k b) atTop := by
    obtain H:= Rain.lapse ( sampled h b ht hi ) hv; rw [ Metric.tendstoUniformly_iff ] at *; intro ε hε; filter_upwards [ H ε hε ] with t h i; specialize h i; rw [ Pi.zero_apply,dist_zero_left ] at h; rw [ dist_comm,dist_eq_norm ]; exact h
lemma wage_cost_one (hx:∀ b:Grade G k',∀ n≤w, coeff n ( f x ( own b ))= coeff n ( g x ( own b ) )) : coeff w ( wage k' A y u ( f x ) ) = coeff w ( wage k' A y u ( g x ) ) := by
    unfold wage Settle; simp only [map_sum]; apply Finset.sum_congr rfl; intro j hj; rw [coeffF,coeffF]; apply Finset.sum_congr rfl; intro i hi; rw [ hx _ _ ( by have ht:=Finset.mem_range.mp hi; omega ) ]
abbrev BeforeT (f g:Fable G n)(x:Points n)(k i:ℕ): Prop:= ∀ j<k,∀ v:Grade G j,∀ y:ℕ,y ≤ i → coeff y ( f x ( own v ))= coeff y ( g x ( own v ) )
abbrev BeforeK (f g:Fable G n)(x:Points n)(k i:ℕ): Prop:=∀ v:Grade G k, ∀ j < i, coeff j ( f x ( own v ))= coeff j ( g x ( own v ) )
lemma aligned (he:BeforeT f g x k i)(ht:BeforeK f g x k i): sparse A f k x y u i=sparse A g k x y u i := by
    unfold sparse; rw [map_sum]; rw [ @_root_.map_sum _ _ _ _ _ _ _ _ ( coeff ( R:=ℂ ) i ) (fun j=> wage j A y u (g x)) ]; refine congr_arg₂ (·+·) (Finset.sum_congr rfl (fun _ hj=> wage_cost_one ( he _ ( Finset.mem_range.mp hj ) ) )) ( Finset.sum_congr rfl (fun _ _=>Finset.sum_congr rfl fun _ hj=> congr_arg₂ (·*·) ( ht _ _ ( Finset.mem_range.mp hj ) ) rfl) ) -- elaborator
lemma exactly (h:Law V R B)( he:Regular V )( ht:Ground V )(H:BeforeT f g x k i)(hq:BeforeK f g x k i)(hx:x∈s)( hF:Fiasco A0 s k v d a f )(hG:Fiasco A0 s k v d a g)(hv:0<v)(hi:i<d) :∀ u:Grade G k,coeff i (f x ( own u ))= coeff i ( g x ( own u )):= by
    obtain hu:= LinearMap.ker_eq_bot.mp ( tactile ht he k ); let p:↥s:= ⟨x,hx⟩;
    refine congr_fun ( hu  (a₁:=finPath x f k i ) ( a₂:= finPath x g k i ) (funext fun b=>?_ )) -- binder names
    obtain h1:= ( Blot h hF hv hi b ).tendsto_at p; obtain h2:= ( Blot h hG hv hi b ).tendsto_at p; let V': Toon G k→ℂ := read_n V g x i k;
    exact tendsto_nhds_unique (l:=atTop) h1 ( h2.congr (f₂:= fun t=> vision A0 f a b x t i ) fun t=> congr_arg (fun U=> Score.fee (-t) ( wght b )*( coeff i (party A0 x ( squeeze (-t) RootG ) a ( Single ( flash b ) )) - U)) ( aligned ( y:=squeeze (-t) RootG ) ( A:= A0 ) ( u:=Single (flash b) ) H hq ).symm ) -- Pulse
-- packaged through any finite k,d.
abbrev Same (s:Set (Points n))(k d:ℕ)(f g:Fable G n):Prop:=∀ x∈s,∀ v:Q G,heft v≤ k→ ∀ i<d, coeff i ( f x v )= coeff i ( g x v )
lemma uniqueK (h:Law V R B)(he:Regular V)(hx:Ground V)(hv:Observed A0)(hp: 0<v)(hT:v ≤1)(hC:Fiasco A0 s k v d a f)(hΓ:Fiasco A0 s k v d a g)(hF:PlainF s f k d)(hG:PlainF s g k d): Same s k d f g:= by
    intro x ht; let Goal (i:ℕ)(u:Q G): Prop:= coeff i (f x u)= coeff i ( g x u ); have H(v':ℕ)(hm:v'≤k):∀ i<d,∀ u:Grade G v', Goal i ( own u ):= by
       induction v' using Nat.strong_induction_on with| h v' ih=>
          intro i h'; induction i using Nat.strong_induction_on with| h i IH=> exact exactly h he hx (fun j hj p r hr=> ih j hj ( hj.le.trans hm ) r (lt_of_le_of_lt hr h') p ) (fun p j hj=> IH j hj (lt_trans hj h') p ) ht ( levels h he hv hF hC hm hp.le hT ) ( levels h he hv hG hΓ hm hp.le hT ) hp h'
    exact fun u hm i hi=> H (heft u) hm i hi u.item
lemma Same.inherits (h: Same s k d f g)(hu:i≤k)(hv:w≤ d): Same s i w f g:= fun x hx b h k' he=> (show Same s k d f g from by assumption) x hx b (le_trans h hu) _ (lt_of_lt_of_le he hv)
lemma rotate_p (h:Same s k d f g)(ht:Fiasco A s k v d a f): Fiasco A s k v d a g:= by
    intro m J p hK hT i hi; have hx:= ht m J p hK hT i hi; refine Rain.raise hx ?_; refine Eventually.of_forall (fun t x=>le_of_eq (congr_arg _ ?_) ); dsimp only; unfold Basket Lamp; simp only [map_sub,map_sum,Settle]; refine congr_arg ( _-·) (Finset.sum_congr rfl fun j hj=> Finset.sum_congr rfl fun q _=>?_); -- map sum? Settle order
    rw [ coeffF,coeffF ]; refine Finset.sum_congr rfl (fun j' hj'=>?_ ); rw [h ( x.1.val ) x.1.property _ ( by have he:= Finset.mem_range.mp hj; unfold heft Score.own; dsimp only; omega) j' ( by have he:= Finset.mem_range.mp hj'; omega )] -- name x type infer
end YM.FVA2.O.Bind
