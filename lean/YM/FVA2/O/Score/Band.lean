import YM.FVA2.O.Score.Glyphs
/-!
# Matrix in the all-horizon, individual grade coordinates (`seats`)

Label coefficients: input first. `Town` for log-polynomial dependence,
needed when translating the scale law.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Score
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix
open Dframe FVA2.Scale MS.Rake MS.Theater Level
variable {G:Gauge}{n m d k:ℕ}
structure Civil (T:Frames G) : Prop where
    hue n: Base ( T n )
    dear n: FVA2.Scale.Native ( T n )
    growth {i j:ℕ}(h:i≤j): FVA2.Scale.Walk h ( T i ) ( T j )
variable {F H T: Frames G}
lemma vertex_at (i:Grade G d): at_grade (vertex i):= Level.top ( Land.read i )
abbrev seats (F:Frames G): Cast G := fun d i j=> PowerSeries.mk (fun k=> paygrade j ( coeff k ( F d ) ( vertex i ) ) )
lemma issued (H: Civil T)(p q:Grade G d): coeff 0 ( seats T d p q )= if p=q then 1 else 0:= by rw [seats, coeff_mk,( H.hue d ).zero,Module.End.one_apply, pivotA ]; simp [eq_comm]
lemma officials (hw: FVA2.Scale.Native ( F d )) (i:Grade G d)(k:ℕ): coeff k (F d) (vertex i)=∑ j: Grade G d, coeff k (seats F d i j) • vertex j:= by simp_rw [ seats, coeff_mk ]; refine Eq.symm ( whole_grade _ ?_ ); unfold at_grade; nth_rw 1 [ ← vertex_at i ]; rw [ (graded_test _).mp ( hw k ), vertex_at i ] -- test grammar
lemma officials_h (hp:FVA2.Scale.Native ( F d )) : seats ( H*F ) d=seats F d*seats H d:= by
    ext i j k; simp_rw [ Matrix.mul_apply,map_sum, coeff_mul ]; unfold seats; rw [ coeff_mk, Pi.mul_apply, coeff_mul,LinearMap.sum_apply, map_sum ]; rw [ Finset.sum_comm ]; refine Finset.sum_equiv (Equiv.prodComm ℕ ℕ) ?_ ?_; · simp [add_comm]
    intro p hp2; simp_rw [coeff_mk]; simp_rw [Module.End.mul_apply,officials hp i p.2]; simp only [map_sum,_root_.map_smul,seats,coeff_mk]; rfl -- first product orientation k-i. need change summation
abbrev replay (F:Frames G): Frames G:= fun i=> mirror (F i)
lemma Civil.turn (H:Civil F): Civil ( replay F ) := ⟨ fun n=>( H.hue n ).rewind, fun i=>(H.hue i).matter ( H.dear i ), fun i=>( H.growth i ).rewind ( H.hue _ ) (H.hue _ )⟩ -- binder implicit?
lemma seats_one : seats (1:Frames G)=1:= by
    funext n; ext1 i j; refine PowerSeries.ext fun k=>?_ ; simp only [ Pi.one_apply ]; rw [seats, coeff_mk, Pi.one_apply]; rw [ coeff_one, Matrix.one_apply ]; split
    · next h=> subst k; rw [ Module.End.one_apply,pivotA ]; split <;> split <;> simp_all [eq_comm]
    rw [ LinearMap.zero_apply,map_zero ]; split <;> simp_all
lemma spin_k (h:Civil F): seats ( replay F ) * seats F=1:= funext fun i=> Eq.trans (officials_h ( H:= F ) (h.turn.dear i)).symm ( Eq.trans (congr_arg ( fun T=> seats T i ) ( funext (fun i=> ( h.hue i ).turn' ))) (congr_fun seats_one i) ) -- `F` for input
lemma spin_v (h:Civil F): seats F *seats (replay F)=1:= funext fun i=> Eq.trans (officials_h ( H:= replay F ) (h.dear i)).symm (Eq.trans (congr_arg ( fun T=> seats T i ) ( funext (fun i=> ( h.hue i ).turn ))) (congr_fun seats_one i))
-- within-grade evaluation at larger horizon
lemma cap_map (H:Civil T)(i:Q G)(h:heft i≤n)(k:ℕ): coeff k (T n) ( cap i h )=∑ j: Grade G (heft i), coeff k ( cue ( seats T ) i ( own j ) ) • cap ( own j ) ( d:=n ) ( show heft ( own j )≤n from h ) := by
    change coeff k (T n) ( up h ( vertex i.item ) )=_; rw [ H.growth h k _, officials (H.dear _) i.item k,map_sum ]; simp_rw [ _root_.map_smul ]; apply Finset.sum_congr rfl; intro j _; rw [report]; rfl
abbrev Town (B: ℝ→Cast G):Prop:=∀ i a b k,Rhythm (fun t=> coeff k ( B t i a b ))
lemma scene_k {B:ℝ→Frames G}(h:∀ i k,Meter.Tracks ( fun t=> B t i ) k ): Town ( fun t=> seats (B t) ):= by
    intro i a b k; simp_rw [seats, coeff_mk]; exact h i k _ _
end YM.FVA2.O.Score
