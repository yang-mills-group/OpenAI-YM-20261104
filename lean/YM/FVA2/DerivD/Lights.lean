import YM.FVA2.DerivD.Tuples
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
# Uniform power-log cost of every iterated shape derivative

Choose compact inner and exterior parameter sets with separation, and each
moment order & finite field list/horizon first. Then give one polynomial
bound (after engineering scale factors as in `Rain`), which can vary with
all these parameters and data. No exchanging cutoff & radius limits.
-/
open O.Read O.Canon O.Enh
variable {G:Gauge}{ I E:Type }{ n m k d:ℕ }{Q': Staff G}{V:Arenas G}{H:ℝ→ Frames G}{r:ℝ→ Cn}
variable {s:Set (Points n)}{K:Set ( Points m )}{x:Points n}{z:Points n × Points m}{t p b:ℝ}
local notation "Λ"=> install V
lemma issue (i:Packet G n m): Stencil ( Issue Q' n m i ):= by
    unfold Issue; let K:= Living Q' n (i.1,i.2.2); let M:= Living Q' m i.2; let p:( Rows G n )→ Packet G n m := fun j=> ( j.1,i.2.1,j.2 ); let q: ( Rows G m ) → Packet G n m:= fun t=> ( i.1,t );
    apply Stencil.add (P:=fun f=> (K (f ∘ p )) ∘L ContinuousLinearMap.fst ℝ _ _ ) ( R:=fun f=> ( M ( f ∘ q ) ) ∘L ContinuousLinearMap.snd ℝ _ _ );
    · exact Stencil.comp ( ( ContinuousLinearMap.compL ℝ (Points n × Points m) ( Points n ) ℂ ).flip ( ContinuousLinearMap.fst ℝ _ _ ) ) ( Stencil.before _ p ( inhabits Q' n (i.1,i.2.2) ) (fun _=>rfl) )
    exact Stencil.comp ( ( ContinuousLinearMap.compL ℝ (Points n × Points m) ( Points m ) ℂ ).flip ( ContinuousLinearMap.snd ℝ _ _ ) ) ( Stencil.before _ q ( inhabits Q' m i.2 ) (fun _=>rfl) )
lemma spring (t:ℝ)(n m:ℕ): IsOpen ( DerivD.Box t n m ):= IsOpen.inter ( (conf_open n ).preimage continuous_fst ) ( ( ( Outside_open m ).preimage continuous_snd ).inter ( ( conf_open (n+m) ).preimage (( LinearMap.toContinuousLinearMap tribe ).continuous.comp ( f:=fun x:(Points n×Points m)=> ( squeeze t x.1,x.2 ) ) ( ( ContinuousLinearMap.prodMap ( lending n t ) (ContinuousLinearMap.id ℝ _ ) ).continuous ) )) )
variable (h:Physical V r H)(he:Influence Q' (install V))
def Slip (t:ℝ)(V:Arenas G)(d:ℕ)(i:Packet G n m)(x:Points n× Points m):= coeff i.2.2 ( Submit (install V) i.1 i.2.1 t ( LogPricing V i.1 ) d x.1 x.2 )
include h
lemma normal (d:ℕ)(v:Packet G n m)(ht:z.1∈conf n): Car t V d v z = O.Score.fee t ( totalG v.1 ) * Slip t V d v z:= by unfold Slip Car Acres Tender Submit; rw [coeff_C_mul,← Physical.shapes h t z.1 ht ]
include he
variable { A: Album G }
lemma carr (hs:IsCompact s)(hx:s⊆conf n)(hr:IsCompact K)(hK:K⊆ Outside m)(d:ℕ)(q:Packet G n m)(i:ℕ): Rain ((d:ℝ)+1) ( fun (p:↥( s ×ˢ K )) t=> iteratedFDeriv ℝ i ( Car t V d q ) p.val ):= by
    refine harmonics ( t:=fun t:ℝ=> DerivD.Box t n m ) (A:= Issue Q' n m) ( Z:=fun i t=> Car t V d i ) (fun i=> issue i ) (( district hs hx hr hK ).mono ( fun t hT=> ⟨fun p hp=> ⟨ hx hp.1,hK hp.2,hT _ hp.2 _ hp.1 ⟩,spring t n m,whole_p h he _ _ _ _⟩ )) (fun j=>?_) i q
    obtain hp:= ( Physical.listed ( n:=n ) h s hs hx d ( j.2.2+1 ) j.1 ) m K j.2.1 hr hK j.2.2 ( Nat.lt_succ_self _ ); let q(p:↥( s ×ˢ K )):s×K:=( ⟨ p.val.1,p.property.1 ⟩,⟨ p.val.2,p.property.2⟩ ); have hA (X:↥(s ×ˢ K))(t:ℝ) := normal ( t:=t ) ( z:= X.val ) h d j ( hx X.property.1 ); simp_rw [hA]; exact Rain.size ( Rain.mul ( a:= ( totalG j.1:ℝ ) ) Rain.all_fee ( Rain.pull hp q ) ) ( by linarith ) -- binder issue simp
omit h he
-- delimits constant rescaling cost sharing (works at all t eventually in same neighborhood).  no measure comp
lemma purge [NormedAddCommGroup E][NormedSpace ℝ E] {s:Set E}{U:ℝ→Set E}{f g:ℝ→ E→ℂ} (hH:∀ᶠ r:ℝ in atTop,s⊆ U r ∧ IsOpen ( U r ) ∧ ContDiffOn ℝ k ( g r ) ( U r ) ∧ ∀ x∈ U r, f r x= O.Score.fee r b * g r x ) (ht: Rain p ( fun (x:↥s) t=> iteratedFDeriv ℝ k (g t) x.val ) ): Rain ( b+p ) ( fun (x:↥s) t=> iteratedFDeriv ℝ k ( f t ) x.val ):= by
    obtain ⟨C,hC,n,h⟩:= ht; refine ⟨C,hC,n,?_⟩; filter_upwards [hH,h] with r hH h x; obtain ⟨ he,H,hQ,hV⟩:=hH; have ht:=H.mem_nhds ( he x.property ); have hx : f r=ᶠ[𝓝 x.val] (( O.Score.fee r b ) • g r):= eventuallyEq_of_mem ht ( fun x hx=> hV x hx );
    rw [ ( hx.iteratedFDeriv ℝ k ).eq_of_nhds, iteratedFDeriv_const_smul_apply ( hQ.contDiffAt ht ), norm_smul ]; apply (mul_le_mul_of_nonneg_left ( h x ) (norm_nonneg _)).trans_eq; unfold O.Score.fee post; simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (exp_pos _|>.le), neg_add,add_mul, exp_add ]; rw [show -r * b = -b * r from (by ring)]; ring; -- order sign
include h he
lemma slip (hs:IsCompact s)(hx:s⊆ conf n)(hr:IsCompact K)(hK:K⊆ Outside m)(d:ℕ)(q:Packet G n m)(i:ℕ): Rain ((d:ℝ)+1-( totalG q.1:ℝ )) ( fun (p:↥( s ×ˢ K )) t=> iteratedFDeriv ℝ i ( Slip t V d q ) p.val ):= by
    apply Rain.size (a:=-( totalG q.1:ℝ )+((d:ℝ)+1)); swap; · linarith
    apply purge ( U:=fun t=>DerivD.Box t n m ) _ ( carr h he hs hx hr hK d q i ); filter_upwards [ district hs hx hr hK ] with t hT; refine ⟨ fun p hp=> ⟨hx hp.1,hK hp.2,hT _ hp.2 _ hp.1⟩, spring t n m, chainM ( spring t _ _ ) ( whole_p h he _ _ _ _ ) ( fun i=> issue i ) i q, ?_⟩; intro x hx; rw [ normal h _ _ hx.1, ← mul_assoc, show O.Score.fee t (-( totalG q.1:ℝ))= O.Score.fee (-t) (totalG q.1) from ?_, mul_comm ( O.Score.fee (-t) _ ), O.Score.fee_mul, one_mul ]; simp [ O.Score.fee ]
end YM.FVA2.DerivD
