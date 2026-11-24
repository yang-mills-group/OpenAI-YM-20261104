import YM.FVA2.Smooth.Decks
/-!
# Continuum finite scale (below unit): building the gradient identity

See `Smooth/Edition` for assembly through all formal orders.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Smooth.Cruise
open Set Function Filter Finset Metric MeasureTheory Real
open MS MS.Plane MS.Koszul MS.Landau MS.Landau.Detect MS.Heat MS.Tone MS.Latch MS.Latch.Job MS.Rake
open MS.Breeze MS.Book MS.Book.Convolve MS.Plane.Flux MS.High MS.Rake.Geo MS.Vane MS.Vista MS.Motif MS.Plane.Wire
open MS.Tone.Frame MS.City MS.Osc MS.Osc.Snap Belt
open MS.Land MS.Local.Physical MS.Dial MS.Port
open Lifetime Slots
open Complex (I)
open scoped Topology ContDiff BigOperators Interval
variable {W I : Type}{G:Gauge}{P Q:Geo I}{b:Deck G}{M:Booked b}
variable {k:ℝ}
variable [LinearOrder W][Fintype W]
open MS.Tide
open MS.Momentum
variable (S:MS_Data G M) (u:W→Rake.Label b)
-- compute on Board specialized Draw W.
local notation "Π"=> Draw W
local notation "μ₀"=> (fun (_:Draw W)=>planeF)
local notation "Δ"=> Rake.Geo.constantP G (Draw W) (PlanetD G)
local notation "Ψ"=> (field (p:=Landau.parity ( A:=Axis ) (C:=G.ColorIndex) ) (P:=QP))
variable {v r t:ℝ} {s: Steps W}
local notation "R"=> frameF (Draw W) v
local notation "Ω"=> approach R S
variable {x: Position W (Draw W)} {T T' U:Finset W} {ρ:Steps W} {J: Set (Draw W)} {q: Draw W}
variable {V:Steps W→Dance G (Draw W) W} {w:Legs (Lane4 G)} {A:Type}
private lemma ride_add {f g: Steps W→ Draw W→ℂ}(hp:Rides r T s f q)(he:Rides r T s g q) : Rides r T s (fun t y=> f t y+g t y) q:= Rides.add hp he
lemma steer (s':Sector A)(w:Legs A){f: Steps W→Draw W→Shared A ℂ}(hp:∀ l k,Rides r T s (fun t y=> f t y l k) q): Rides r T s (fun t y=> scatter s' w (f t y)) q:= by
 induction w generalizing f with| nil=> exact hp _ _ | cons i w ih=> exact ih (fun a b=> ride_add (hp (i::a) b) ((hp a (i::b)).along _))
lemma tide (F: Steps W→ Glade G (Draw W))(P:Edge G)(K:Law G) (hp:∀ a,Rides r T s (fun v x=> F v x t a) q): Rides r T s (fun u j=> tree Landau.parity P K (F u j t) w) q:= by
 apply steer; intro a b; unfold attaches; apply Rides.sum; intro i hi; apply Rides.sum; intro j hj; apply ride_add <;> exact ((hp _).along _).along _ -- check grouping
set_option maxHeartbeats 400000 in
lemma bornJ (hp:J∈𝓝 q)(hx:Mesh R x)(ht:∀ s': Steps W, charted R S u s' x ( V s' )) (T U: Finset W)(hT: U∈picks T)(h:t≤0)(i j:ℕ)(hk:∀ y∈J,∀ w,Rides r U s (fun b p=> aboard x (V b) U i p t w) y)(hh:∀ y∈J,∀ w,Rides r (T\U) s (fun b p=> aboard x ( V b ) (T\U) j p t w ) y) (w:Legs (Lane4 G)): Rides r T s (fun v p=> Cabin 0 (PlanetD G t) planeF (aboard x (V v) U i p t) (aboard x (V v) (T\U) j p t) w) q:= by
 obtain he:= n_small hT; unfold Cabin; simp_rw [Tone.pay0,one_mul ]; apply Cruise.steer; intro a b; apply Rides.sum; intro k _; apply Rides.sum; intro l _; refine Rides.money hp ?_ (Eventually.of_forall ?_); -- priorities
 · intro u'; obtain ⟨r,hr⟩:= tip0 (toTour R S u u' x hx) (ht u') (n:=i) he.2.1; obtain ⟨s1,h1⟩:= tip0 ( toTour R S u u' x hx ) (ht u') (n:=j) he.2.2.1; exact aboardM ( rootX x U ) (rootX x (T\U)) h hr.2.2 h1.2.2 _ _ _ _
 intro q0 y hy; unfold meshZ; apply Rides.prices ( s:=U  ) ( s':= T\U ) ( Finset.disjoint_left.mpr fun a ht h=> mem_sdiff.mp h |>.2 ht ) ( show T=U∪(T\U) from ?_ ); -- grouping actual term `2*P*(cross*F)*H`, works
 · exact ((hk y hy _).along _).along _
 · exact hh y hy _
 · intro z hz; have h (w:Legs (Lane4 G)): _:= same (W:=W) S u s V x ht U i y t w z hz; simp_rw [h] -- implicit needs `dsimp only`
 · exact same S u s V x ht (T\U) j y t _
 exact Eq.symm (Finset.union_sdiff_of_subset he.1.le) -- check order

lemma looping (hp:J∈𝓝 q)(hx:Mesh R x)(ht:∀ s': Steps W, charted R S u s' x ( V s' )){T: Finset W}(hT: 2≤T.card)(h:t≤0)(i:ℕ)(w:Legs ( Lane4 G ))(he:∀ y∈J,∀ a:Legs (Lane4 G), a.length>w.length→ Rides r T s (fun b p=> aboard x (V b) T i p t a) y): Rides r T s (fun b p=> sailP μ₀ Δ (aboard x (V b) T i) p t w ) q:= by
 unfold sailP cycle; dsimp only [constantP]; apply Rides.money hp ?_ (Eventually.of_forall ?_); · intro v; exact parallel (rootX x T) h (emerged (toTour R S u v x hx) (ht v) hT _) w
 intro p y hy; simp_rw [ at_trc ]; apply Rides.sum; intro u _; apply Rides.sum; intro t _; exact (he _ hy _ (by simp)).along _
-- Empty sector. Singleton derivatives. Need prevent colliding $V$.
lemma alone (ht:∀ s': Steps W, charted R S u s' x ( V s' ))(k:ℕ): Rides r ∅ s (fun u y=> aboard x (V u) ∅ k y t w ) q := by simp_rw [ aboard, ( show ∀ p,V p ∅=0 from fun p=> (ht p).1 ) ]; unfold perch; simp only [Pi.zero_apply,map_zero]; exact Rides.zeroS s r ∅ q
omit [LinearOrder W] in
-- singleton Fourier phase gradient scaled λ
lemma billL (w:W) (p:QP)(r:ℝ): HasFDerivAt (fun z:Draw W=> Tone.bill (r • z w) p) (Tone.bill ( r • q w ) p • (∑ i:Axis, Abroad.spout r (w,i) ( Lifetime.turn i p ))) q := by
 let K:= ∑ i:Axis, Abroad.spout r (w,i) ( Lifetime.turn i p ); have he (z:Draw W): Tone.bill (r • z w) p= Complex.exp ( K z ):= by
    unfold Tone.bill; congr 1 -- unfold bill?
    unfold K pairing; push_cast
    simp only [ Finset.sum_apply, Abroad.seen,Complex.real_smul, Lifetime.turn_eq, Pi.smul_apply, smul_eq_mul,Finset.mul_sum ]; exact Finset.sum_congr rfl fun i _=> by push_cast; ring
 simp_rw [he]; exact K.hasFDerivAt.cexp
omit [LinearOrder W][Fintype W] in
lemma unique_t (S':MS_Data G M)(K:Rake.Label b)(x y:I)(k:ℕ)(w:List Axis): beamH S' (frameF I v) K w k x= beamH S' (frameF I v) K w k y:= by induction w with| nil=>rfl| cons i w ih=> funext q l; change ( force i (beamH S' _ _ w k) ) x q l= ( force i (beamH S' _ _ w k) ) y q l; rw [force_eq,force_eq,ih]
lemma hmark (hp: ∀ w, x w =ᶠ[𝓝 q] (fun y=> r • y w ))(ht:∀ s': Steps W, charted R S u s' x ( V s' ))(i:W)(k:ℕ): Rides r {i} s (fun v y=> aboard x (V v) {i} k y t w ) q:= by
 -- bill_t ∑ turn *beam.Marks.Lo
 simp_rw [ aboard,perch,cove, ( show ∀ u,V u {i}=att R S _ u i from fun u=> (ht u).2.1 i ), rootX,dif_pos ( Finset.singleton_nonempty i ),min'_singleton,att ]; let T0 (p:Steps W) (y:Draw W):= beamH S R (u i) (p i) k y t w;
 -- same mark independent ζ.L position even after differentiation.Count.
 have hs(p: Steps W)(y: Draw W): T0 p y=T0 p q:= congr_fun (congr_fun ( unique_t S _ y q k (p i) ) t ) w;
 have hh(j:Axis): T0 (hop s (i,j)) q= Lifetime.turn j (net w)*T0 s q:= by simp only [T0,hop,Function.update_self]; exact Lifetime.force_eq ..;
 have he:= (hp i).self_of_nhds; change Rides r {i} s (fun v y=>Tone.bill ( x i y ) (net w)*T0 v y) q; simp_rw [ hs ];
 unfold Rides; dsimp only; apply HasFDerivAt.congr_of_eventuallyEq _ ( f:=fun z=> Tone.bill (r • z i) (net w)*T0 s q ) ?hv; swap; · exact hp i|>.mono ( fun u hu=> by dsimp only; rw [hu])
 convert! (billL ( q:=q ) i (net w) r).mul_const ( T0 s q ) using 1;
 ext1 y; simp only [Abroad.ray,sum_singleton,_root_.smul_apply, _root_.sum_apply, Abroad.seen,smul_eq_mul,Complex.real_smul,Finset.mul_sum, he, hh ]; exact Finset.sum_congr rfl fun i _=> by ring
end YM.FVA2.Smooth.Cruise
