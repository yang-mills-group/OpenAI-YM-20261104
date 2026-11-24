import YM.FVA2.DerivD.Regular
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
/-! # First-order differentiation on any number of simultaneous near and far positions -/
open O.Bind O.Canon O.Read
variable {G:Gauge}{n m k d:ℕ}{P:Staff G}{A:Album G}{V:Arenas G}{r:ℝ→Cn}{H:ℝ→Frames G}
variable {x:Points n}{y:Points m}{p:Q G}
variable (v:Scan G n)(u:Scan G m)
-- formulate using FarCoefficients on squeezed x (u↦value), then give normative $r.Alp`.
abbrev Tender (V:Arenas G)(v:Scan G n)(u:Scan G m)(x:Points n)(y:Points m)(d:ℕ): Cn:= Basket (install V) v u ( FarCoefficients V v x ) d x y
variable (h:Physical V r H)(he:Influence P (install V))(hr:x∈conf n)(hs:y∈Outside m)(ht:forest x y∈conf _)
include he ht
local notation "Λ"=> install V
include h hr
lemma tenderL (d:ℕ): Shard P ( fun x i=> Tender V i u x y d ) x:= by
    let A(x:Points n)(i:Scan G n):=party Λ x y i u; let B(x:Points n)(i:Scan G n):=Lamp Λ d y u ( FarCoefficients V i x );
    apply Shard.sub ( interior_phase he ht u ); unfold Lamp Settle; apply Shard.league; intro j hj; apply Shard.league; intro i _; simp_rw [mul_comm _ (lonelyG Λ y _ u)]; apply Shard.along; exact establish h hr he _
omit h hr
include hs
lemma tenderR (d:ℕ): Shard P ( fun y i=> Tender V v i x y d ) y:= by
    apply Shard.sub ( exterior_phase he ht v ); unfold Lamp Settle; apply Shard.league; intro j hj; apply Shard.league; intro i _; apply Shard.along; exact exterior_phase he hs _
include h hr
lemma joint (k d:ℕ): ContDiffAt ℝ ∞ ( fun p:Points n×Points m=> coeff k ( Tender V v u p.1 p.2 d )) (x,y):= by
    unfold Tender Basket; simp_rw [ map_sub ]; apply ContDiffAt.sub
    · exact ( regular_at he (Fin.append v u) _ ht ).comp ( f:= ( LinearMap.toContinuousLinearMap tribe ) ) ( x,y ) ( LinearMap.toContinuousLinearMap tribe ).contDiff.contDiffAt
    unfold Lamp Settle; simp_rw [ map_sum, coeffF ]; refine ContDiffAt.sum ( fun j _=> ContDiffAt.sum fun i _=> ContDiffAt.sum fun k _=> ( ( along_far h he hr _ k v ).comp (x,y) ( contDiffAt_fst ) ).mul ?_ );
    let P: (Points n)×(Points m)→L[ℝ] Points (1+m):= ( LinearMap.toContinuousLinearMap (tribe ( n:=1 ) ( m:=m ) ) ) ∘L ( ContinuousLinearMap.prod 0 ( ContinuousLinearMap.snd ℝ _ _ ) ); exact ( regular_at he ( Fin.append ( Single (own i) ) u ) _ hs ).comp (f:=P) (x,y) P.contDiff.contDiffAt
omit h hr hs he ht
private theorem together_c {E F K:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup K][NormedSpace ℝ K]{g:E × F→K}{p:E×F}{V:E→L[ℝ]K}{P:F→L[ℝ]K}(h:DifferentiableAt ℝ g p)(hp:HasFDerivAt (fun i=> g (i,p.2)) V p.1)(ht: HasFDerivAt (fun j=>g (p.1,j)) P p.2): HasFDerivAt g ( ContinuousLinearMap.coprod V P ) p:= by
    let T:= fderiv ℝ g p; refine h.hasFDerivAt.congr_fderiv ?_; obtain ⟨p,q⟩:=p; apply ContinuousLinearMap.ext; rintro ⟨i,j⟩; change T (i,j)= V i+P j; let V1: E→L[ℝ] E×F:=ContinuousLinearMap.inl ℝ E F; let V2:F→L[ℝ] E×F:=ContinuousLinearMap.inr ℝ E F; rw [ show (i,j)=V1 i+V2 j from ?_,map_add];
    · obtain l:T ∘L V1=V:= ( ( h.hasFDerivAt.comp p ( hasFDerivAt_prodMk_left p q ) ).unique hp ); obtain r:T ∘L V2=P:= ( ( h.hasFDerivAt.comp q ( hasFDerivAt_prodMk_right p q ) ).unique ht ); exact congr_arg₂ ( ·+· ) ( DFunLike.congr_fun l i ) ( DFunLike.congr_fun r j )
    exact Prod.ext ( add_zero i ).symm ( zero_add j ).symm
abbrev Packet (G:Gauge)(n m:ℕ):= Scan G n × Scan G m × ℕ
def Issue (P:Staff G)(n m:ℕ)(i:Packet G n m)(f: Packet G n m→ℂ): Points n × Points m →L[ℝ] ℂ:= ContinuousLinearMap.coprod ( Living P n ( i.1,i.2.2 ) ( fun j=> f ( j.1,i.2.1,j.2 ) ) ) ( Living P m i.2 ( fun j=> f ( i.1,j ) ) )
def Car (t:ℝ)(V:Arenas G)(d:ℕ)(i:Packet G n m)(x:Points n× Points m):= coeff i.2.2 ( Acres t ( totalG i.1 )*Tender V i.1 i.2.1 ( squeeze t x.1 ) x.2 d )
def Box (t:ℝ)(n m:ℕ): Set ( Points n×Points m ):= {p | p.1∈conf n ∧ p.2∈Outside m ∧ forest ( squeeze t p.1 ) p.2∈conf (n+m)}
include h he
lemma whole_p (d:ℕ)(t:ℝ)(n m:ℕ): Cochain (Issue P n m) (Car t V d) (DerivD.Box t n m):= by
    intro i ⟨x,y⟩ ⟨hx,hV,hE⟩; let v:=i.1; let u:=i.2.1; have hx:= squeeze_away hx t; obtain hu:= ( joint v u h he hx hV hE i.2.2 d ).comp ( x,y ) ( ContinuousLinearMap.prodMap (lending n t) ( ContinuousLinearMap.id ℝ (Points m) ) ).contDiff.contDiffAt;
    refine together_c ?_ ?_ ?_
    · unfold Car Acres; simp_rw [coeff_C_mul]; exact ( hu.differentiableAt ( by simp ) ).const_mul _
    · dsimp only [Car]; rw [ sigil (fun a=> Acres t ( totalG a ) * Tender V a i.2.1 ( squeeze t x ) y d ) ]; exact normed t ( tenderL u h he hx hE d ) _ _ -- unroll
    dsimp only [Car]; rw [show i.2 = (u,i.2.2) from rfl, sigil ( fun a=> Acres t ( totalG i.1 )* Tender V i.1 a ( squeeze t x ) y d ) ]; exact Shard.along ( tenderR v he hV hE d ) _ _ _
end YM.FVA2.DerivD
