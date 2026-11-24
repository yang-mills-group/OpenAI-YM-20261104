import YM.FVA2.O.Read.Light
/-!
# FAR probe matrix

`SheetCore` ingredient of `Sheet`: pull back to unit scale via the scale law. Constant
leading independent of t; prove polynomial cost in log-scale t at every order.
See `O/Read/Fire` to invert.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Read
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real TopologicalSpace
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh O.Bind O.Project
variable { G:Gauge }{ I J:Type }{n m d k:ℕ}{ u: Scan G n }{ v:Scan G m }
variable { s:Opens ( Points 1 ) }{ a:Toon G d }{x:Points n}{y: Points m}
variable {H:ℝ→ Frames G}{r:ℝ→Cn}{V:Arenas G}{A:Album G}{p:Cn}{b t:ℝ}
local notation "V0"=> install V
-- notation for column vector
abbrev LetterQ (p:Toon G d) := Single (flash p)
/-- Actual $B_T$ figures. -/
abbrev Sheet (H:ℝ→Frames G)(A:Album G)(P:Geology G d)(t:ℝ): Matrix ( Toon G d ) ( Toon G d ) Cn:= fun b j=> ∑ i:Toon G d, smearing ( P b i ).val ( fun y:Points 1=> LongT H A t ( flash j ) y ( LetterQ i ) )
/-- After column weighting. Ignores exponential powers. -/
abbrev SheetCore (H:ℝ→Frames G)(r:ℝ→Cn)(V:Arenas G)(P:Geology G d)(t:ℝ): Matrix ( Toon G d ) ( Toon G d ) Cn:= fun b j=> ∑ i:Toon G d, smearing ( P b i ).val ( fun y:Points 1=> ProgramY H r V t ( flash j ) y ( LetterQ i ) )
abbrev Stone (d:ℕ)(G:Gauge)(t:ℝ): Matrix ( Toon G d ) ( Toon G d ) Cn:= Matrix.diagonal (fun b=> Acres t ( heft ( flash b )) )
lemma above (d:ℕ)(t:ℝ): Stone d G t * Stone d G (-t)=1:= by unfold Stone; rw [Matrix.diagonal_mul_diagonal]; exact congr_arg Matrix.diagonal ( funext ( fun i=> acres_b t ( heft ( flash i ) ) ))
lemma whats (A:Album G)(b:Scan G 1)(v:Scan G m)(y:Points m): party A (0:Points 1) y b v=A _ ( outgoing y ) ( Fin.append b v ):= rfl
lemma cash_term (he:Observed A)(V:Exterior m)(u:Scan G 1)(v:Scan G m): draw V.val ( fun y=> party A (0:Points 1) y u v ):= fun i=> ( he ( 1+m ) ( Fin.append u v ) i ).comp ( f:=outgoing ) ( ( show Continuous ( outgoing (m:=m) ) from Enh.continual continuous_const continuous_id ).continuousOn ) ( fun _ hz=> V.property hz )
lemma viewed (he:Observed A)(b:Scan G 1)(Q:Exterior m)(hp:Rooted p) : draw Q.val ( fun y=> party ( tune p A ) (0:Points 1) y b v ):= by
    exact continual_k ( A:=fun y=> party A (0:Points 1) y b v ) ( cash_term he Q b v ) hp
variable {P: Geology G d}
local notation "Q'"=> Sheet H V0 P t
local notation "V1"=> SheetCore H r V P t
variable (h:Law V r H)(he:Observed ( install V ))(ht:Regular V)
include h he
lemma recorded (b:Q G)(K:Exterior m)(v:Scan G m): draw K.val (fun y=> ProgramY H r V t b y v):= by
    intro i; simp only [ ProgramY, concert,map_sum, coeffF ]; refine continuousOn_finsetSum _ ( fun j _=> continuousOn_finsetSum _ ( fun k _=>?_ ) ); let F:= party ( m:=m ) ( tune ( r (-t) ) V0 ) (0: Points 1); obtain hp: draw K.val ( fun x=> F x ( decode (Single b) j ) v ):= viewed he _ K ( p:=r (-t) ) ( (h.led _).start ); exact ( hp ( i-k ) ).const_mul _
lemma oldR (K:Exterior m)(b: Scan G 1)(v:Scan G m) : ChargeP d 0 ( fun (i:↥( CoverP K.val )) t=> party ( tune ( r (-t) ) V0 ) (0:Points 1) i.val b v ):= by
    let F (i:↥(CoverP K.val)):= party V0 (0:Points 1) i.val b v; have hR : ChargeP d 0 ( fun (i:↥( CoverP K.val )) (_:ℝ)=> F i ):= by
        intro k _; obtain ⟨C,hC⟩:= K.val.hasCompactSupport.exists_bound_of_continuousOn ( cash_term he K b v k ); exact Rain.cash ⟨ C,fun i=> hC _ i.property ⟩
    have hp : ChargeP d 0 ( fun (_: Unit ) t=> r (-t) ):= by intro i hi; obtain hx:= (Rhythm.unit.mpr ( h.smooth i )).pre ( -( Polynomial.X:Polynomial ℝ ) ); apply Rain.rhythm ( f:=fun t=> coeff i ( r (-t) ) ); simpa only [ Polynomial.eval_neg, Polynomial.eval_X ] using hx
    obtain H:= ChargeP.Pact ( I:= ↥(CoverP K.val) ) ( g:=fun _ t=> r (-t) ) hR ( hp.pull (fun _=>()) ) ( fun _ t=> (h.led (-t)).start ); exact H
lemma watched ( b:Q G )( K: Exterior m )(v: Scan G m) : ChargeP d 0 ( fun (i:↥( CoverP K.val )) t=> ProgramY H r V t b i.val v ):= cost_tag ( T:=fun t=> Night H (-t) ) ( Uniform.flips ( rhythm_b h ) ) _ _ ( fun i=> oldR h he K ( decode ( Single b ) i ) v )
lemma prepaid ( p q: Toon G d ): ChargeP k 0 ( fun (_:I) t=> SheetCore H r V P t p q ):= by unfold SheetCore; exact ChargeP.sum _ ( fun i _=> paid_u ( watched h he _ _ _ ) ( Eventually.of_forall ( fun t=> recorded h he _ _ _ ) ) )
-- lead: constant coefficient $ProgramY` = unscaled value.
omit he
lemma root_t (p:Q G): coeff 0 ( ProgramY H r V t p y v )=coeff 0 ( lonelyG ( install V ) y p v ):= by
    unfold ProgramY; rw [ Score.solo,map_sum ]; simp_rw [ coeff_zero_eq_constantCoeff_apply, map_mul, ← coeff_zero_eq_constantCoeff_apply ]; unfold Night; simp_rw [ issued (( slot h _ ).turn) ]; simp only [ ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ, ↓reduceIte ]; unfold party tune; rw [← Constants.actual_subst _ _ (( h.led _ ).start),coeff_mk,Program.pay0 ]; -- defeq left
lemma leadY (p q:Toon G d): coeff 0 (SheetCore H r V P t p q)= Portfolio V0 P p q:= by unfold SheetCore; rw [map_sum]; simp_rw [smearing,coeff_mk,root_t h ]

include he ht
lemma forever (b:Q G)(v:Scan G m)(Q:Exterior m): draw Q.val ( fun y=> LongT H V0 t b y v ):= by simp_rw [ routeY h ht ]; exact region _ ( recorded h he _ _ _ ) _
lemma sheet_b : Q'= V1* Stone d G t:= by
    ext1 i j; rw [ Stone, Matrix.mul_diagonal ]; unfold Sheet SheetCore; simp_rw [ routeY h ht, smearing_mul _ ( recorded h he _ _ _ ) _ ]; rw [ Finset.sum_mul ]; exact Finset.sum_congr rfl fun i _=> mul_comm ..
end YM.FVA2.O.Read
