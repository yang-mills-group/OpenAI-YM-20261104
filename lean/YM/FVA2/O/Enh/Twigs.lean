import YM.FVA2.O.Enh.Stream
/-!
# Gluing inner and exterior positions for OPE

Euclidean points, exterior profiles off the origin (`Outside`).
See `orange` and `storyH`, etc., for working in corresponding MS geometry.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Enh
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo O.Seam
variable { I J G : Type } {n m d : ℕ }
variable {x:Points n}{y:Points m}
def forest (x:Points n)(y:Points m): Points (n+m):= points ( Fin.append x.ofLp y.ofLp )
abbrev outgoing (y:Points m): Points (1+m):= forest (0:Points 1) y
@[simp] lemma forest_left (i:Fin n): forest x y ( Fin.castAdd m i )= x i:= Fin.append_left ..
@[simp] lemma forest_right (i:Fin m): forest x y ( Fin.natAdd n i )=y i:= Fin.append_right ..
lemma distil (t:ℝ): squeeze t ( forest x y )= forest (squeeze t x) (squeeze t y):= by
    ext1 i; induction i using Fin.addCases <;> first | rw [forest_left]; simp only [squeeze,PiLp.smul_apply,forest_left] | rw [forest_right]; simp only [squeeze,PiLp.smul_apply,forest_right]
lemma squeeze_home (t:ℝ) : squeeze t (outgoing y)=outgoing (squeeze t y):= by unfold outgoing; rw [distil,squeeze,smul_zero]
@[fun_prop] lemma continual [TopologicalSpace I]{f:I→ Points n}{g:I→ Points m}(h:Continuous f)(he:Continuous g): Continuous (fun i=>forest (f i) (g i)):= by
    let p i: Fin (n+m)→ E4 := ( forest (f i) ( g i ) ).ofLp; refine (PiLp.continuous_toLp 2 (fun _: Fin (n+m)=> E4)).comp (show Continuous p from ?tmp ); case tmp => refine continuous_pi (fun i=>?_ ); induction i using Fin.addCases <;> simp [p] <;> fun_prop
-- combine configuration predicates
abbrev Left (m n:ℕ) := Fin.castAddEmb ( n:=m ) n
abbrev Right (m n:ℕ): Fin n ↪ Fin (m+n) := Fin.natAddEmb m
lemma opposite (i:Fin m)(j:Fin n): Left m n i ≠ Right m n j:= by
    intro h; have he:=congr_arg Fin.val h; change i.val=m+j.val at he; omega
lemma forest_sep (hx:x∈ conf n)(hy:y∈conf m)(h:∀ i j,x i≠ y j): forest x y∈ conf (n+m):= by
    intro i j he; change forest x y i= forest x y j at he; induction i using Fin.addCases with
    | left i=> rw [forest_left] at he; induction j using Fin.addCases with
      | left j=> rw [ forest_left ] at he; rw [hx he]
      | right j=> rw [forest_right] at he; exact False.elim ( h i j he )
    | right i=> rw [forest_right] at he; induction j using Fin.addCases with
      | left j=> rw [forest_left] at he; exact False.elim ( h j i he.symm )
      | right j=> rw [forest_right] at he; rw [ hy he ]
lemma take_r (h:forest x y∈ conf (n+m)): y∈conf m:= by intro i j he; exact ( Right n m ).injective ( h (show forest x y ( Fin.natAdd n i )=forest x y ( Fin.natAdd n j ) from ( forest_right i ).trans ( (show y i=y j from he).trans ( forest_right ( x:=x ) j).symm )) )
abbrev Outside (m:ℕ): Set (Points m):={y| outgoing y∈conf (1+m)}
lemma room (h:y∈ Outside m): y∈conf m:= take_r h
lemma lives ( t:ℝ ) ( h:y∈Outside m ): squeeze t y ∈ Outside m:= by change outgoing ( squeeze t y )∈ conf (1+m); rw [← squeeze_home t]; exact squeeze_away h _
lemma clear (h:y∈ Outside m) (i:Fin m): y i≠0:= by
    intro hx; apply opposite (0: Fin 1) i; exact h ( show forest (0:Points 1) y ( Fin.castAdd m 0 )=forest (0:Points 1) y ( Fin.natAdd 1 i ) from ( by rw [forest_left,forest_right,hx]; rfl ) )
lemma filled [TopologicalSpace I]{p:I→ Points m} (e:Continuous p)(i:Fin m): Continuous (fun x=> Theater.out (p x i)) := ( Theater.out.toLinearMap.continuous_of_finiteDimensional ).comp (by fun_prop : Continuous (fun x=>p x i))
lemma Legs (K:Set (Points m))(h:IsCompact K)(i:Fin m): ∃ C:ℝ,0<C ∧∀ x∈K, ‖Theater.out ( x i )‖≤ C:= by obtain ⟨C,hC⟩:= h.exists_bound_of_continuousOn (filled ( p:=id ) continuous_id i).continuousOn; exact ⟨ max C 1, lt_max_of_lt_right zero_lt_one,fun x hx=> ( hC x hx ).trans ( le_max_left .. )⟩
lemma spread (K:Set (Points m))(h:IsCompact K)( F:Points m→ QP )(ht:Continuous F)(hp: ∀ x∈K,F x≠0): ∃ C:ℝ,0<C ∧∀ x∈K,C≤ ‖F x‖:= by
    obtain he|he:= K.eq_empty_or_nonempty; · rw [he]; exact ⟨1, zero_lt_one, fun _ h=>False.elim h ⟩
    obtain ⟨x,hx,hH⟩:= h.exists_isMinOn he ht.norm.continuousOn; exact ⟨ ‖F x‖, norm_pos_iff.mpr ( hp x hx ),fun i h=> hH h ⟩
variable { s:Set ( Points m ) }
lemma storyY (hp:IsCompact s)(ht:s⊆Outside m)(i:Fin m): ∃ c:ℝ,0<c∧∀ y∈s,c≤‖Theater.out (y i)‖:= spread _ hp _ (filled continuous_id i) (fun _ h=> fun t=> clear (ht h) i ( Theater.out.injective ( t.trans (map_zero _).symm ) ))
lemma storyH (hp:IsCompact s)(ht:s⊆ conf m)(i j:Fin m)(h:i≠j): ∃ c:ℝ,0<c∧∀ y∈s,c≤ ‖Theater.out ( y i )-Theater.out (y j)‖ := spread _ hp _ ( ( filled continuous_id i ).sub ( filled continuous_id j ) ) ( fun _ hz=> sub_ne_zero.mpr (fun e=> h ( ht hz|>.eq_iff.mp ( Theater.out.injective e ) ))) -- apply direct
variable {P:Geo I}
def orange (f:I→ Points m): Rake.Position (Fin m) I:= fun k i=> Theater.out (f i k)
lemma orange_h {f:I→ Points m}( hp:∀ i,f i∈ conf m ): O.Price.separable ( orange f ):= by intro i j k ht; apply hp i; exact Theater.out.injective ht
lemma due {f:I→Points m}(hp:O.Price.separable (orange f))(i:I): f i∈conf m:= by intro j k h; apply hp i; exact congr_arg Theater.out h
variable {x:I→ Points n}{y:I→ Points m}
lemma colored (hx: O.Price.separable ( orange x ))(ht: O.Price.separable ( orange y ))(he:∀ i j,CoverSep P ( orange y j-orange x i )): O.Price.separable ( orange (fun i=> forest ( x i ) ( y i )) ):= orange_h fun v=> forest_sep (due hx v) ( due ht v ) (fun i j=> fun e=> far_ne ( he i j ) v ( congr_arg Theater.out e.symm ))
end YM.FVA2.O.Enh
