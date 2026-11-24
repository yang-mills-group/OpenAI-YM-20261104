import YM.FVA2.DerivD.Staff
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.DerivD
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real TopologicalSpace
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh O.Bind O.Project
/-!
# Chain rule on concatenated position tuples
-/
open Dframe Facets Equator O.Price O.Enh O.Read
variable {G:Gauge}{ n m :ℕ}{ Q':Staff G}{A: Album G}{ x x':Points n}{y y': Points m}
def tribe : ( Points n×Points m )→ₗ[ℝ] Points (n+m) where
    toFun x:=forest x.1 x.2
    map_add' x y:= by apply PiLp.ext; intro i; induction i using Fin.addCases <;> simp
    map_smul' x i:= by apply PiLp.ext; intro i; induction i using Fin.addCases <;> simp
lemma append_scale (P:Staff G)(v:Axis)(F:Scan G (n+m) → Cn)(p:Scan G n)(q:Scan G m)(i:Fin n): Raise P ( Fin.castAdd m i ) v ( Fin.append p q ) F= Raise P i v p ( fun l=> F ( Fin.append l q ) ):= by
    unfold Raise; simp_rw [LinearMap.coe_mk, AddHom.coe_mk]; -- `rw` dependent avoids motive by slicing at `append`. Define g.
    have h (l:Q G): update (Fin.append p q) ( Fin.castAdd m i ) l=Fin.append ( update p i l ) q:= by
       funext k; induction k using Fin.addCases with
       | left j=> by_cases h:j=i; subst j; rw [update_self,Fin.append_left,update_self]; rw [ update_of_ne (show Fin.castAdd m j ≠ Fin.castAdd m i from fun k=>h ((Left _ _).injective k)),Fin.append_left,Fin.append_left,update_of_ne h ]
       | right j=> rw [update_of_ne (show Fin.natAdd n j≠ Fin.castAdd m i from Ne.symm (opposite i j) ),Fin.append_right,Fin.append_right];
    simp_rw [ h ]
    rw [Fin.append_left]
lemma append_phase (P:Staff G)(v:Axis)(F:Scan G (n+m) → Cn)(p:Scan G n)(q:Scan G m)(j:Fin m): Raise P ( Fin.natAdd n j ) v ( Fin.append p q ) F= Raise P j v q ( fun l=> F ( Fin.append p l ) ):= by
    unfold Raise; simp_rw [LinearMap.coe_mk, AddHom.coe_mk];
    have h (l:Q G): update (Fin.append p q) ( Fin.natAdd n j ) l=Fin.append p ( update q j l ):= by
       funext k; induction k using Fin.addCases with
       | left i=> rw [update_of_ne ( show Fin.castAdd m i≠ Fin.natAdd n j from opposite i j ), Fin.append_left, Fin.append_left ]; -- might diseq defeq
       | right i=> by_cases h:i=j; subst i; rw [update_self,Fin.append_right,update_self]; rw [ update_of_ne (show Fin.natAdd n i ≠ Fin.natAdd n j from fun k=>h (( Right _ _).injective k)),Fin.append_right,Fin.append_right,update_of_ne h ]
    simp_rw [h]; rw [Fin.append_right]
lemma combined (k:ℕ)(x:Points n)(y:Points m)(P:Staff G)(F:Scan G (n+m) → Cn)(p:Scan G n)(q:Scan G m): Γ P F ( Fin.append p q ) k ( forest x y )= Γ P ( fun l=> F ( Fin.append l q ) ) p k x+Γ P ( fun l=> F ( Fin.append p l ) ) q k y:= by
    unfold Γ; simp_rw [_root_.sum_apply,appears]; rw [Fin.sum_univ_add]; simp_rw [forest_left,forest_right,append_scale,append_phase]
lemma interior_phase (H:Influence Q' A)(ht: forest x y∈ conf (n+m))(v:Scan G m): Shard Q' ( fun x i=> party A x y i v ) x:= by
    intro i k; let F:= LinearMap.toContinuousLinearMap (tribe (n:=n) (m:=m)); let h (x:Points n):= (x,y); have hf: HasFDerivAt h ( ContinuousLinearMap.inl ℝ _ _ ) x:= ( hasFDerivAt_id .. ).prodMk (hasFDerivAt_const _ _); obtain he:= F.hasFDerivAt.comp x hf; obtain hx:= ( H (n+m) ( forest x y ) ht ( Fin.append i v ) k ).comp x he; refine hx.congr_fderiv ?_; ext1 p; change Γ _ _ ( Fin.append i v ) k ( forest p 0 )= _; rw [combined,map_zero, add_zero]
lemma exterior_phase (H:Influence Q' A)(ht: forest x y∈ conf (n+m))(v:Scan G n): Shard Q' ( fun y i=> party A x y v i ) y:= by
    intro i k; let F:= LinearMap.toContinuousLinearMap (tribe (n:=n) (m:=m)); let h (y:Points m):= (x,y); have hf: HasFDerivAt h ( ContinuousLinearMap.inr ℝ _ _ ) y:= ( hasFDerivAt_const x y ).prodMk ( hasFDerivAt_id .. ); obtain he:= F.hasFDerivAt.comp y hf; obtain hx:= ( H (n+m) ( forest x y ) ht ( Fin.append v i ) k ).comp y he; refine hx.congr_fderiv ?_; ext1 p; change Γ _ _ ( Fin.append v i ) k ( forest 0 p )= _; rw [combined,map_zero, zero_add]
end YM.FVA2.DerivD
