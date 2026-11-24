import YM.FVA2.DerivD.Lights
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
/-! # cost of coefficients themselves; preserve growth through all derivatives -/
open O.Read O.Canon
variable {G:Gauge}{ n m k d:ℕ}{p:Staff G}{t:ℝ}{u:Scan G n}
variable {V:Arenas G}{H:ℝ→Frames G}{r:ℝ→Cn}
variable (he: Influence p ( install V ))(h:Physical V r H)
variable {s s':Set ( Points n )}{p':Q G}{P: Geology G k}{x:Points n}
local notation "X"=> ( install V )
abbrev Post (V:Arenas G)(p':Q G)(t:ℝ)(x:Points n)(i:Scan G n): Cn:= OPECoefficients V i t x p'
private abbrev PencilP (V:Arenas G)(p':Q G)(t:ℝ)(k:Rows G n)(x:Points n):= coeff k.2 ( NormP t ( fun x i=> FarCoefficients V i x p' ) x k.1 )
include h
lemma exhibit (hx:x∈conf n)(b:Q G)(t:ℝ)(k:ℕ): coeff k ( Acres t ( totalG u )* Post V b t x u )=PencilP V b t ( u,k ) x:= by unfold PencilP NormP Post; rw [ Physical.shapes h t x hx ]
include he
lemma link (b:Q G)(n:ℕ)(t:ℝ): Cochain ( Living p n ) ( PencilP V b t ) ( conf n ):= by
    intro q x hx; let F(x:Points n)(i:Scan G n):= FarCoefficients V i x b; exact ( normed ( x:=x ) t ( establish ( x:=squeeze t x ) h ( squeeze_away hx t ) he b ) q.1 q.2 ).congr_fderiv ( sigil (NormP t F x ) q.1 q.2 ).symm
variable (hk:IsCompact s)(hs:s⊆conf n)
include hk hs
lemma earns (v: Rows G n)(n:ℕ)(b:Q G): Rain ( heft b:ℝ ) ( fun (x:↥s) t=> iteratedFDeriv ℝ n ( PencilP V b t v ) x.val ):= by
    let H(i:Rows G _) (t:ℝ) (x:s):= exhibit ( u:=i.1 ) h ( hs x.property ) b t i.2;
    apply harmonics ( t:=fun _=> conf _ ) ( A:=Living p _ ) ( Z:=fun i t=> PencilP V b t i ) ( inhabits p _ ) ( Eventually.of_forall (fun t=> ⟨ hs,conf_open _, link he h b _ t⟩ )); intro i;
    simp_rw [show ∀ (x:↥s) (t:ℝ), PencilP V b t i x.val=coeff i.2 ( Acres t (totalG i.1) * Post V b t x.val i.1 ) from fun x t=> (H i t x).symm]; unfold Acres; simp_rw [coeff_C_mul]; have hT:= stamp_fee (u:=i.1) ( k:=i.2+1 ) ( h.works i.1|>.toMarkup ) hk hs b i.2 ( Nat.lt_succ_self _ );  simp only [ QuoteP,O.Project.pack,coeff_C_mul ] at hT; exact Rain.size ( Rain.mul ( a:=( totalG i.1:ℝ ) ) ( b:= (heft b:ℝ)-( totalG i.1:ℝ ) ) Rain.all_fee hT ) ( by linarith ) -- argument order
lemma costs (v:Scan G n)(i j:ℕ)(b:Q G): Rain (( heft b:ℝ )-( totalG v:ℝ )) ( fun (x:↥s) t=> iteratedFDeriv ℝ i ( fun x=> coeff j ( Post V b t x v ) ) x.val ):= by
    apply Rain.size ( a:= - ( totalG v:ℝ )+( heft b:ℝ ) ); swap; · linarith
    apply purge ( U:=fun _=> conf _ ) _ ( earns he h hk hs ( v,j ) i b ); refine Eventually.of_forall (fun t=> ⟨ hs,conf_open _, chainM ( conf_open _ ) ( link he h b _ _ ) ( inhabits p n ) i (v,j), ?_⟩); intro x hT; rw [ ← exhibit h hT b t j, Acres, coeff_C_mul (φ:= Post V b t x v), ← mul_assoc, show O.Score.fee t (-( totalG v:ℝ ))= O.Score.fee ( -t ) (totalG v) from ?_, mul_comm ( O.Score.fee (-t) _ ), O.Score.fee_mul,one_mul ]; simp [O.Score.fee]
-- The full far-shape estimate uses a slightly larger compact set containing the test set in its interior.
lemma report ( hP:Detected V P )( b:Toon G k)( hV: s⊆ interior s' )( hK:IsCompact s' )(ht:s'⊆ conf n)( i j:ℕ ) : Rain ((k:ℝ)+1-( heft ( flash b ):ℝ )) ( fun ( x:↥s ) t=> iteratedFDeriv ℝ i ( fun x=> coeff j ( QuoteShape H X P u t x b - FarCoefficients V u x ( flash b ) ) ) x.val ):= by
    apply harmonics ( i:=(u,j) ) ( t:=fun _=>interior s' ) ( A:=Living p _ ) ( Z:=fun u t x=> coeff u.2 ( QuoteShape H X P u.1 t x b - FarCoefficients V u.1 x ( flash b ) ) ) ( inhabits p _ ) ?_ ?_; -- args
    · filter_upwards [O.Read.life P hK ht] with t hT; refine ⟨ hV,isOpen_interior,?_⟩; intro q x hx; let F(x:Points n)(u:Scan G n):= QuoteShape H X P u t x b; let U(x:Points n)(u:Scan G n):= FarCoefficients V u x ( flash b ); exact (( Shard.sub (F:=F) (F':=U) ( color_f he hK h.awake hT hx b ) ( establish h ( ht ( interior_subset hx ) ) he _ )) q.1 q.2).congr_fderiv ( sigil ( F x - U x ) q.1 q.2).symm
    intro i; exact post_quote h.scope h.dimensions h.awake hk hs hP ( h.far i.1 |>.2.2 s hk hs k ( i.2+1 ) ) b i.2 (Nat.lt_succ_self _)
end YM.FVA2.DerivD
