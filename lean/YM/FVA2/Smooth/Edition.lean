import YM.FVA2.Smooth.Window
/-!
# Complete the corresponding derivative identity on the negative t portion

Use estimates for `Mesh` here (`frameF`), see `Smooth/Travel` to then pass
to other log-times.
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
-- induction over tag card & $n$ and finite ranks negative t. Open patch $J$ shared for all counts.Layout
variable (ho:IsOpen J)(hu:∀ i, EqOn ( x i ) (fun q=> r • q i) J)(hx:Mesh (frameF (Draw W) v) x)
variable (ht:∀ s':Steps W,charted (frameF (Draw W) v) S u s' x ( V s' ))
include ho hu hx ht
-- need v implicit via variable explicit profile 'no notation variable' to avoid ghost
lemma sailing (T: Finset W)(n:ℕ) : ∀ y∈J,∀ s:Steps W,∀ t:ℝ,t≤0 → ∀ w, Rides r T s (fun v p=> aboard x (V v) T n p t w) y := by
 induction T using Finset.strongInductionOn generalizing n with| _ T ih=>
  obtain h|h:= T.eq_empty_or_nonempty; · subst T; exact fun _ _ _ _ _ _=> alone S u ht n
  by_cases hT:2≤T.card; swap; · obtain ⟨i,hh⟩ := Finset.card_eq_one.mp ( show T.card=1 from by obtain hv:= Finset.card_pos.mpr h; omega ); rw [hh]; exact fun y hy _ _ _ _=> hmark S u (fun i=> (hu i).eventuallyEq_of_mem (ho.mem_nhds hy)) ht i n -- EqOn.*
  induction n using Nat.strong_induction_on with| h n hN=>
    let X(s:Steps W):= aboard x ( V s ); have h40(s:Steps W):= emerged (toTour R S u s x hx) (ht s) hT n; -- binder type?
    have h0 (s:Steps W)(t:ℝ)(hs:t≤0)(y:Draw W)(hp:y∈ J)(w: Legs (Lane4 G)) : Rides r T s (fun s y=> road 0 Ω ( X s ) T n y t w ) y:= by
       simp only [road,Src,multi,lonely,Pi.add_apply,Finset.sum_apply, root_0,sub_zero]; refine ride_add (Rides.sum _ _ (fun i hi=>?_)) ( Rides.sum _ _ fun i hi=> Rides.sum _ _ fun j hj=>?_ ); -- check
       · exact Cruise.tide ( t:=t ) ( q:=y ) (fun s=> X s T i) (PlanetD G t) (approach R S (n-i) y t) (fun l=> hN i (Finset.mem_Ico.mp hi|>.2) y hp s t hs l)
       obtain he:= n_small hi; exact bornJ S u ( ho.mem_nhds hp ) hx ht T i hi hs j.1 j.2 (fun y hy l=> ih i he.1 _ y hy _ _ hs l ) ( fun y hy l=> ih (T\i) he.2.2.2 _ y hy s t hs l ) w
    have he (s:Steps W) : X s T n= river ( folk 0 (X s) T n Ω ):= Cruise.motion _ (ht s) n hT
    intro y hy s' t hs w
    let K(s:Steps W):=(h40 s).2.choose; have hK(s:Steps W)(i:Draw W) (t:ℝ)(l:Legs (Lane4 G))(hl: K s< l.length) : X s T n i t l=0:= by change relax _ _ i t l=0; rw [cove,(h40 s).2.choose_spec i t l ( by specialize hl; unfold K at hl; omega ),mul_zero ]; -- need simp
    let k := max ( K s' ) ( (patch T).sup (fun i=> K ( hop s' i )) );
    suffices hc : ∀ (m:ℕ),∀ y∈J,∀ t:ℝ, t≤0→∀ l: Legs (Lane4 G), k<m+l.length→ Rides r T s' (fun p y=> X p T n y t l) y from hc (k+1) y hy t hs w (by omega);
    intro m; induction m with
    | zero=> intro y hy t hs w hw; apply Rides.by_zero; · funext q; exact hK s' q t _ (le_max_left (K s') _ |>.trans_lt ( show k<_ from by omega) );
             exact fun i hi=> hK (hop s' i) y t _ (( Finset.le_sup ( f:=fun i=> K ( hop s' i ) ) hi ).trans ( le_max_right ( K s' ) _ ) |>.trans_lt ( show k<_ from by omega ) );
    | succ m hm=>
      intro y hy t hs w hw;
      simp_rw [he]; unfold river; apply Rides.money ( ho.mem_nhds hy ) ;
      · intro s; change Boxed _ (fun i a=> folk 0 (aboard x (V s)) T n Ω i a w); rw [← vouchers]; exact ancestor (p:=rootX x T) hs (clocks _ u s hx (ht s) T hT n) w
      filter_upwards [ ae_restrict_mem measurableSet_Iic ] with t0 h1; have hf : t0≤0:= le_trans h1 hs; intro y hy; exact ride_add ( looping S u (ho.mem_nhds hy) hx ht hT hf n w ( fun y hy l hc=> hm y hy t0 hf l (by omega)) ) ( h0 s' t0 hf y hy w )
end YM.FVA2.Smooth.Cruise
