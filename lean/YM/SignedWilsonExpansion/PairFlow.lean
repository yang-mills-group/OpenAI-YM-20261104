import YM.SignedWilsonExpansion.PanelE
namespace YM.SignedWilsonExpansion.PairFlow
/-! # Complete continuation of paired E vertices at differential scales
    full heat profile, then remove bulk IR. -/
set_option autoImplicit false
noncomputable section
open Function MeasureTheory Set Filter Finset
open MS MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.Plane.Wire MS.High MS.Tone MS.Land MS.Latch MS.Rake MS.Heat MS.Breeze
open Energy (leg)
open FVA2 FVA2.Lambda Area HighRank HighScale Walk PhasePair PanelE FourierGaussian TwoGrid AxisChoice OrderHigh MassShift MarkShift
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}
local notation "P" => FourP
local notation "μ" => covMeasure Axis
local notation "Z" => Momentum.sq
local notation "K1" => PlanetD G
local notation "E" => Energy.plane 1 2 G 0
local notation "η" => Energy.called 1 2 G
local notation "π" => TwoGrid.price
local notation "Ω" => AxisChoice.disk
local notation "Wφ" => PhasePair.rate
local notation "Wγ" => PhasePair.rateV
local notation "S" => PanelE.plateZ
variable {B: Land.Booked (Press.portDeck G)}(M:Land.MS_Data G B) (simple:G.Simple)
variable (q:Fin 2→FourP) {d:ℝ}(hd:d≠0)(hx:Injective q)(hv:q 1-q 0=axis d)
local notation "X" => axis d
local notation "U0" => PhasePair.read M q η 0
variable (y v:ℝ)(p:P)(A:G.ColorIndex)(t:ℝ)
local notation "Vℓ" => leap v (PhasePair.read M q η 2)
local notation "α" => (v*OrderHigh.kinetic G)
local notation "β" => (v*OrderHigh.locus G)
local notation "mk" => PhasePair.source M q
local notation "LK" => leap v (MarkRows.packet M η 2)
local notation "†" => PlanetD G t
local notation "cost" => bias d
local notation "Wκ" => FourierGaussian.wind d
local notation "P₀" => FourierGaussian.rise d
local notation "P₁" => FourierGaussian.early d
local notation "O" => FourierGaussian.dot d
local notation "ℓ" => FourierGaussian.bonus d
local notation "H" => Shells.hot t
local notation "m" => Fintype.card G.ColorIndex
abbrev quoteK (F:Law G)(p:P)(A:G.ColorIndex):= price p (fun p=> κZ F p A)
lemma plus (F G':Law G): quoteK (F+ G') p A=quoteK F p A+quoteK G' p A:= by unfold quoteK κZ; simp_rw [ Pi.add_apply,mul_add,Finset.sum_add_distrib ]; exact map_add (price p) ..
lemma derive {F:ℝ→Law G}{K:Law G}(he:∀ w:Legs (Lane4 G), w.length=2 → HasDerivAt (fun t=> F t w) (K w) t): HasDerivAt (fun t=>quoteK (F t) p A) ( quoteK K p A ) t:= by
   unfold quoteK; simp_rw [TwoGrid.price_s]; refine (HasDerivAt.fun_sum (fun i hi=>?_)).div_const _; refine HasDerivAt.fun_sum (fun i hi=>?_); exact HasDerivAt.fun_sum (fun j hj=> (he _ rfl).const_mul _)
lemma quote_lim {F:ℝ→Law G}(hp:∀ w:Legs (Lane4 G),w.length=2→Tendsto (fun t=> F t w) atBot (𝓝 0)): Tendsto (fun t=>quoteK ( F t ) p A) atBot (𝓝 0):= by
    have he(p:P): Tendsto (fun t=> κZ ( F t ) p A) atBot (𝓝 0):= by
       let X' (i:Axis)(j:Axis): Legs (Lane4 G):= [ W i A p,W j A (-p) ]; unfold κZ; convert (tendsto_finsetSum Finset.univ (fun i _=> tendsto_finsetSum Finset.univ (fun j _=> ( hp (X' i j) rfl ).const_mul ( Landau.precision i j p:ℂ) ) )) using 1; simp only [ mul_zero, Finset.sum_const_zero ]
    unfold quoteK; simp_rw [TwoGrid.price_s]; simpa only [ Finset.sum_const_zero,zero_div ] using ((tendsto_finsetSum Finset.univ (fun i _=> he (turns i p))).div_const (4:ℂ))
lemma exercise (f g h:ℝ→ℂ)(hu:∀ t, HasDerivAt f (h t) t)(hv:∀ t, HasDerivAt g (h t) t)(hp:Tendsto f atBot (𝓝 0))(hc:Tendsto g atBot (𝓝 0)): f t=g t:= sub_eq_zero.mp ( Canvas.regression t (f:=fun t=> f t-g t) (fun t=>by convert! ((hu t).sub (hv t)) using 1; simp) (by simpa only [ sub_zero ] using hp.sub hc ) )
include hd hv hx
lemma energy_low : quoteK ( U0 (y,t) ) p A = S (axis d) p* P₀ t:= by
    refine exercise t (fun t=>quoteK (U0 (y,t)) p A) (fun t=> S (axis d) p* P₀ t) (fun t=> S (axis d) p * cost t) ?_ (fun t=>( warden d t hd ).const_mul _ ) ?_ ?_; rotate_left
    · exact quote_lim p A (fun w _=> provisional M q hx _ w y)
    · simpa only [mul_zero] using (reaches_cold d hd).const_mul ( S (axis d) p )
    intro t; have he:= derive p A t (F:=fun t=> U0 (y,t)) ( K:=PhasePair.source M q 0 (y,t)) ( fun w h=> PhasePair.run_speed M q hx (y,t) w h ); rw [source0 M, hv] at he; unfold quoteK at *; rw [PanelE.mean_lead t p A M y] at he; exact he
abbrev aFactor (p:P)(s:ℝ):= β+α*Wφ s p
include simple
lemma effort (p:P)(F:Law G) : quoteK ( tree parity (†) ( MarkShift.wall M v ) F ) p A=
                                    (α * Wγ H p) • (quoteK F p A+quoteK F (-p) A):= by
    unfold quoteK; simp_rw [ Walk.dotL, PhasePair.kinetic_contract M simple ]; rw [TwoGrid.currency (c:=(( α* Wγ H p):ℝ)) (f:=fun p=>↑( α *Wγ H p )) ( fun i=> by unfold PhasePair.rateV; simp_rw [trcB] ) (fun p=> κZ F p A+κZ F (-p) A), PanelE.combine, TwoGrid.antip p (f:=fun p=> κZ F p A) ]; rfl
lemma energy_cost : quoteK ( leap v ( source M q 2 ) (y,t)) p A=
    S (axis d) p*(2*( (α*Wγ H p) • P₀ t + aFactor ( G:=G ) v p t • cost t + α • Wκ t)) := by
    rw [ PhasePair.source2 M q hx simple, plus, plus, hv ]; unfold quoteK;
    rw [ show π p (fun p=>κZ ( tree parity (†) ( MarkShift.wall M v ) (U0 (y,t))) p A)=_ from effort M simple q hd hx hv v A t p (U0 (y,t)), PanelE.delta_X t p A M simple v y ]; simp_rw [ PanelE.delta_Y _ _ _ M simple, PanelE.delta_X t p A M simple v y ]; -- eta pair vertices
    rw [ energy_low M q hd hx hv, energy_low M q hd hx hv ]; unfold aFactor; rw [ PanelE.plate_even ]; simp_rw [ Complex.real_smul ]; ring
lemma energy_delta : quoteK ( Vℓ (y,t) ) p A=S (axis d) p*(2*( aFactor ( G:=G ) v p t • P₀ t + α • P₁ t)) := by
   refine exercise t (fun t=>quoteK (Vℓ (y,t)) p A) ( fun t=> S (axis d) p * (2*( aFactor ( G:=G ) v p t • P₀ t + α • P₁ t )) ) (fun t=> quoteK (leap v (source M q 2) (y,t)) p A ) (fun t=> derive p A t (F:=fun t=>Vℓ (y,t)) (K:=leap v (source M q 2) (y,t)) (fun _ h=> PhasePair.leap_speed M q hx simple (y,t) v _ h) ) ?_ ( quote_lim p A ( F:=fun t=>Vℓ (y,t)) (fun w _=> (descent2 M q hx v y 2).2.2 _) ) ?_
   · intro t; rw [energy_cost M simple q hd hx hv]; have ht: HasDerivAt ( aFactor ( G:=G ) v p) (α* Wγ (Shells.hot t) p) t:= by unfold aFactor; convert! (( ( PhasePair.gain p t ).const_mul α ).const_add β ) using 1
     convert! ( ((ht.smul ( warden d t hd ) |>.add (vessel d t hd|>.const_smul α)).const_mul 2 ).const_mul ( S ( axis d ) p )) using 1; rw [add_comm ((v*OrderHigh.kinetic G*PhasePair.rateV (Shells.hot t) p) • P₀ t)]; -- order of smul
   have hp: Tendsto (fun t=> Wφ t p) atBot (𝓝 0):= by unfold PhasePair.rate rateV; simpa only [mul_zero,zero_mul] using (((TreeLine.amp_cold p.sq).const_mul (2:ℝ)).mul_const ( Z p ^2 ))
   have he: Tendsto (fun t=> aFactor ( G:=G ) v p t) atBot (𝓝 β):= by simpa only [aFactor,mul_zero,add_zero] using (( hp.const_mul α ).const_add β )
   simpa only [ smul_zero, add_zero, mul_zero ] using ((((he.smul ( reaches_cold d hd )).add ((J0 d hd).const_smul α)).const_mul (2:ℂ)).const_mul ( S ( axis d ) p ))

/- close the mask scalar.-/
local notation "pRod" => PhasePair.provisional
omit simple hx hv hd
lemma cycle_profile {K:Law G}(he:∀ w z:Lane4 G,Bubble.wing w→Bubble.wing z→K [w,z]=0)(ht:Heat.Pass (†) K μ): cycle (†) μ K []=∫ p:P, ( (H (Z p)):ℂ)* (∑ a:G.ColorIndex, quoteK K p a)∂μ:= by
   have hz(p:P): Flux.trc ( PlanetD G t ) p K [] =( H (Z p):ℂ ) * ( ∑ a:G.ColorIndex, κZ K p a ):= by
       rw [ at_trc, Walk.dotL, Walk.starLine ]; have hp(x y:Branch G Axis)(ht:parity x=true)(hx:parity y=true): K [(x,p),(y,-p)]=0:=he (x,p) (y,-p) ht hx; simp_rw [ hp (Area.U₀ _ _) (Area.C₀ _) rfl rfl, hp (Area.C₀ _) (Area.U₀ _ _) rfl rfl, mul_zero, Finset.sum_const_zero,add_zero ]; unfold κZ; simp_rw [ Walk.bond,Complex.ofReal_mul,mul_assoc,Finset.mul_sum ];
   unfold cycle; rw [ ← TwoGrid.count_int (f:=fun k=> Flux.trc ( PlanetD G t ) k K [] ) ( ht [] ) ]; simp_rw [ hz ]; apply integral_congr_ae; apply Eventually.of_forall; intro p; dsimp only; rw [ TwoGrid.currency (f:=fun p=>↑(H (Z p))) (c:= (( H (Z p)):ℂ )) (fun i=>by simp_rw [ trcB ]) (fun p=> ∑ a:G.ColorIndex, κZ K p a), TwoGrid.sale ]; -- maybe unbound
-- PlateZ*hot. moments.
lemma neg_good (F:P→ℂ)(h: Integrable F μ): Integrable (fun p=> F (-p)) μ:= ( (Measure.measurePreserving_neg μ).integrable_comp_emb ((Homeomorph.neg P).measurableEmbedding)).mpr h
lemma hot_plate : ( (H (Z p):ℝ):ℂ )* S (axis d) p=8*(O t p + O t (-p) ):= by unfold PanelE.plateZ FourierGaussian.dot; rw [Landau.sq_neg,AxisChoice.dial_neg]; push_cast; ring
lemma hot_spin : (( H (Z p):ℝ ):ℂ)* S (axis d) p*( Wφ t p:ℂ)=8*( ℓ t p+ ℓ t (-p) ):= by rw [hot_plate]; unfold FourierGaussian.bonus PhasePair.rate; rw [PhasePair.rate_neg]; ring
lemma beats_paid : Integrable (fun p=> ( (H (Z p):ℝ):ℂ )* S (axis d) p) μ ∧ Integrable (fun p=> (( H (Z p):ℝ ):ℂ)* S (axis d) p*( Wφ t p:ℂ)) μ:= by simp_rw [hot_spin,hot_plate]; exact ⟨ (( (dot_int d t).add ( neg_good _ (dot_int d t)) ).const_mul ( 8:ℂ )),(( (wind_int d t).add (neg_good _ ( wind_int d t )) ).const_mul (8:ℂ) )⟩
lemma beats : (∫ p:P, ( (H (Z p):ℝ):ℂ )* S (axis d) p∂ μ)=16*cost t ∧ (∫ p:P, (( H (Z p):ℝ ):ℂ)* S (axis d) p*( Wφ t p:ℂ)∂μ)=16*Wκ t:= by
    constructor
    · simp_rw [ hot_plate ]; rw [ integral_const_mul, integral_add (dot_int d t) ( neg_good _ (dot_int d t)),integral_neg_eq_self ]; unfold FourierGaussian.bias; ring
    simp_rw [ hot_spin ]; rw [ integral_const_mul, integral_add (wind_int d t) ( neg_good _ (wind_int d t)),integral_neg_eq_self ]; unfold FourierGaussian.wind; ring
include hx hv hd
lemma scalar_prime0 : cycle ( PlanetD G t ) μ ( U0 (y,t) ) []=( m:ℂ )*(16*cost t* P₀ t):= by
    rw [ cycle_profile t (fun w z he ht=> other_heads M q hx _ _ ( Bubble.side he ) ( Bubble.side ht ) (y,t)) ( Wallet.cour ( afford_E M q hx _ _ ) t ) ]; simp_rw [ energy_low M q hd hx hv, Finset.sum_const ]; rw [ Finset.card_univ ]; simp only [ nsmul_eq_mul ];
    let F(p:P):= ((H (Z p)):ℂ)* S (axis d) p; simp_rw [ show ∀ p, ((H (Z p)):ℂ)*( ( m:ℂ )*( S (axis d) p* P₀ t ))= (m:ℂ)*(F p * P₀ t) from fun p=>by unfold F; ring ]; rw [ integral_const_mul, integral_mul_const,(beats (d:=d) t).1 ]; -- maybe simp_rw
include simple
lemma scalar_primeD : cycle ( PlanetD G t ) μ ( Vℓ (y,t) ) []=( m:ℂ )*( 32*(β • (cost t* P₀ t)+ α • (Wκ t* P₀ t+ cost t * P₁ t ))):= by
    have ht: Vℓ (y,t)∈ Wallet G:= ( Wallet G ).sub_mem ( afford_E M q hx _ (y+v,t) ) ( afford_E M q hx _ (y,t) ); rw [ cycle_profile t (fun w z he hv=>leap_odd M q hx simple w z he hv (y,t) v) ( Wallet.cour ht t ) ]; simp_rw [ energy_delta M simple q hd hx hv,Finset.sum_const ]; rw [ Finset.card_univ ]; simp only [ nsmul_eq_mul ];
    let F(p:P):= ((H (Z p)):ℂ)* S (axis d) p; let G'(p:P):= F p*( Wφ t p:ℂ )
    let e:= ( m:ℂ )*2; let b:= e*(β • P₀ t+α • P₁ t); let w:=e*(α • P₀ t); let h(p:P) : ((H (Z p)):ℂ)*( (m:ℂ)*(S (axis d) p * (2*( aFactor ( G:=G ) v p t • P₀ t+ α • P₁ t ))))= F p*b+ G' p*w:= by unfold aFactor G' F b w e; simp_rw [ Complex.real_smul ]; push_cast; ring
    simp_rw [ h ]; rw [ integral_add ( Integrable.mul_const (f:=F) (beats_paid (d:=d) t).1 b ) ( Integrable.mul_const (f:=G') ( beats_paid (d:=d) t ).2 w ), integral_mul_const,integral_mul_const,(beats (d:=d) t).1,(beats (d:=d) t).2 ]; unfold b w e; simp_rw [ Complex.real_smul ]; ring
-- reconstruct finite values from initial UV. 
omit simple
lemma connected0 : U0 (y,t) []=(m:ℂ)*8*P₀ t^2:= by
   refine exercise t (fun t=>U0 (y,t) []) (fun t=> (m:ℂ)*8*P₀ t ^2) (fun t=> (m:ℂ)* ( 16*cost t * P₀ t ) ) ?_ ?_ ( PhasePair.provisional M q hx _ [] y ) ?_
   · intro t; obtain he:= PhasePair.ground_flow_still M q hx (y,t); rw [scalar_prime0 M q hd hx hv y] at he; exact he
   · intro t; convert! ((( warden d t hd ).pow 2 ).const_mul _ ) using 1; ring
   simpa using ((( reaches_cold d hd ).pow 2 ).const_mul (( m:ℂ )* 8 ))
include simple
lemma connected2 : Vℓ (y,t) []=(m:ℂ)*16*(β • (P₀ t* P₀ t)+ ( (2:ℝ)*α ) • ( P₀ t * P₁ t )):= by
    refine exercise t (fun t=>Vℓ (y,t) []) (fun t=>(m:ℂ)*16*(β • (P₀ t* P₀ t)+((2:ℝ)*α) • ( P₀ t * P₁ t ))) (fun t=>(m:ℂ)* (32*( β • (cost t*P₀ t )+α • (Wκ t * P₀ t+ cost t*P₁ t ))) ) ?_ ?_ ((descent2 M q hx v y 2).2.2 []) ?_
    · intro t; obtain he:= PhasePair.action_flow_still M q hx simple (y,t) v; rw [scalar_primeD M simple q hd hx hv y v] at he; exact he
    · intro t; convert! ( ( (( warden d t hd |>.mul (warden d t hd)).const_smul β ).add ((warden d t hd|>.mul ( vessel d t hd)).const_smul ((2:ℝ)*α)) ).const_mul _ ) using 1; simp_rw [ Complex.real_smul ]; push_cast; ring
    have hp:= reaches_cold d hd; simpa using ((((hp.mul hp).const_smul β).add (( hp.mul ( FourierGaussian.J0 d hd ) ).const_smul ((2:ℝ)* α)) ).const_mul ( ( m:ℂ )*16 ) )
local notation "C0" => FourierGaussian.count0 d
omit simple
lemma energy_end : sale_at M q y 0=(m:ℂ)* 8 *( C0:ℂ )^2:= by
    refine tendsto_nhds_unique (PhasePair.IR M q hx _ y) (( ( reaches_end d hd |>.pow 2 ).const_mul ((m:ℂ)*8)).congr (fun t=> (connected0 M q hd hx hv y t).symm) )
include simple
lemma delta_end : sale_at M q (y+v) 2-sale_at M q y 2=(( 2*(α+β)):ℝ) • sale_at M q y 0:= by
    have he:= Tendsto.sub ( PhasePair.IR M q hx 2 (y+v)) (PhasePair.IR M q hx 2 y)
    obtain ht:= reaches_end d hd; let z:=( m:ℂ )*16
    have hp:Tendsto (fun t=> Vℓ (y,t) []) atTop (𝓝 ( z*( β • (( C0:ℂ )*( C0:ℂ ))+( 2*α ) • (( C0:ℂ )*(( C0:ℂ )/2))))) := (((( ht.mul ht ).const_smul β).add ((( ht.mul (J1 d hd) ).const_smul ((2:ℝ)*α)))).const_mul z).congr fun t=>( connected2 M simple q hd hx hv y v t).symm
    rw [ tendsto_nhds_unique he ( show Tendsto (fun i=> PhasePair.read M q η 2 (y+v,i) [] - PhasePair.read M q η 2 (y,i) []) _ _ from hp ), energy_end M q hd hx hv ]; unfold z; simp_rw [ Complex.real_smul ]; push_cast; ring
end
end YM.SignedWilsonExpansion.PairFlow
