import YM.SignedWilsonExpansion.Grid.Pipeline
namespace YM.SignedWilsonExpansion.Overlap.Economy
/-! # Complete continuation of 𝔼12 – 02 different plane energy vertex pair at differential scales
    full heat profile, then remove bulk IR. -/
set_option autoImplicit false
noncomputable section
open Function MeasureTheory Set Filter Finset
open MS MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.Plane.Wire MS.High MS.Tone MS.Land MS.Latch MS.Rake MS.Heat MS.Breeze
open Energy (leg)
open FVA2 FVA2.Lambda Area HighRank HighScale Walk PhasePair PanelE FourierGaussian TwoGrid AxisChoice OrderHigh MassShift MarkShift
open Rim Realm Fair Align Duet PairFlow
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge} (s:Bool)
local notation "P" => FourP
local notation "μ" => covMeasure Axis
local notation "Z" => Momentum.sq
local notation "K1" => PlanetD G
local notation "E" => Energy.plane 1 2 G 0
local notation "η" => Energy.called 1 2 G
local notation "π" => Fair.price
local notation "Ω" => AxisChoice.disk
local notation "Wφ" => PhasePair.rate
local notation "Wγ" => PhasePair.rateV
local notation "S" => Realm.plateQ
variable {B: Land.Booked (Press.portDeck G)}(M:Land.MS_Data G B) (simple:G.Simple)
variable (q:Fin 2→FourP) {d:ℝ}(hd:d≠0)(hx:Injective q)(hv:q 1-q 0=axis d)
local notation "X" => axis d
local notation "U0" => Duet.extract M q s (!s) 0
variable (y v:ℝ)(p:P)(A:G.ColorIndex)(t:ℝ)
local notation "Vℓ" => leap v (Duet.extract M q s (!s) 2)
local notation "α" => (v*OrderHigh.kinetic G)
local notation "β" => (v*Align.salaryQ G)
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
abbrev reckon (F:Law G)(p:P)(A:G.ColorIndex):= Fair.price p (fun p=> κZ F p A)
lemma combineD (F G':Law G): reckon (F+ G') p A=reckon F p A+reckon G' p A:= by unfold reckon κZ; simp_rw [ Pi.add_apply,mul_add,Finset.sum_add_distrib ]; exact map_add (Fair.price p) ..
lemma deriveD {F:ℝ→Law G}{K:Law G}(he:∀ w:Legs (Lane4 G), w.length=2 → HasDerivAt (fun t=> F t w) (K w) t): HasDerivAt (fun t=>reckon (F t) p A) ( reckon K p A ) t:= by
   unfold reckon; simp_rw [Cohort.price_s]; refine (HasDerivAt.fun_sum (fun i hi=>?_)).div_const _; refine HasDerivAt.fun_sum (fun i hi=>?_); exact HasDerivAt.fun_sum (fun j hj=> (he _ rfl).const_mul _)
lemma quote_lim {F:ℝ→Law G}(hp:∀ w:Legs (Lane4 G),w.length=2→Tendsto (fun t=> F t w) atBot (𝓝 0)): Tendsto (fun t=>reckon ( F t ) p A) atBot (𝓝 0):= by
    have he(p:P): Tendsto (fun t=> κZ ( F t ) p A) atBot (𝓝 0):= by
       let X' (i:Axis)(j:Axis): Legs (Lane4 G):= [ W i A p,W j A (-p) ]; unfold κZ; convert (tendsto_finsetSum Finset.univ (fun i _=> tendsto_finsetSum Finset.univ (fun j _=> ( hp (X' i j) rfl ).const_mul ( Landau.precision i j p:ℂ) ) )) using 1; simp only [ mul_zero, Finset.sum_const_zero ]
    unfold reckon; simp_rw [Cohort.price_s]; simpa only [ Finset.sum_const_zero,zero_div ] using ((tendsto_finsetSum Finset.univ (fun i _=> he (Fair.mix i p))).div_const (12:ℂ))
local notation "L0" => Duet.freight M q s (!s)
include hx hv
lemma bareK : reckon ( U0 (y,t) ) p A =0:= by
    refine PairFlow.exercise t (fun t=> reckon ( U0 (y,t) ) p A) (fun _=>0) (fun _=>0) ?_ (fun x=> hasDerivAt_const x (0:ℂ) ) ( quote_lim p A (fun w _=> provisionalX M q hx s (!s) 0 w y) ) tendsto_const_nhds
    intro t; have he:= deriveD p A t (F:=fun t=> U0 (y,t)) (K:=L0 0 (y,t)) (fun w hp=> Duet.run_speedD M q hx s (!s) (y,t) w hp); rw [source0D,hv] at he; have hu : reckon ( Cabin (X) (PlanetD G t) μ (Energy.plane (degreeX (!s)) 2 G 0) (Energy.plane (degreeX s) 2 G 0)) p A=0:= Fair.price_fix (fun i=> Realm.evolve_X s t _ A M y)
    rw [hu] at he; exact he
include simple
omit hx hv in
lemma effortD (p:P)(F:Law G) : reckon ( tree parity (†) ( MarkShift.wall M v ) F ) p A=
                                    (α * Wγ H p) • (reckon F p A+reckon F (-p) A):= by
    unfold reckon; simp_rw [ Walk.dotL, PhasePair.kinetic_contract M simple ]; rw [Fair.currency (c:=(( α* Wγ H p):ℝ)) (f:=fun p=>↑( α *Wγ H p )) ( fun i=> by unfold PhasePair.rateV; simp_rw [Fair.magπ] ) (fun p=> κZ F p A+κZ F (-p) A), show (∀ f g:P→ℂ, π p (fun p=> f p+g p)=π p f+π p g) from fun f g=>map_add (π p) f g, Fair.antipode p (f:=fun p=> κZ F p A) ]; rfl
lemma drive : reckon (leap v ( L0 2 ) (y,t)) p A= S (axis d) p * ( (2*β:ℝ) • cost t ):= by
    -- multiplication-parentheses just below; explicit two steps correspond choice of updated mark. 
    let F(s': Bool):= leap v (MarkRows.packet M (Energy.called (degreeX s') 2 G) 2 ) (y,t)
    let L(s': Bool):= Energy.plane (degreeX s') 2 G 0
    have he (s':Bool): reckon (Cabin (axis d) (K1 t) μ (F (!s')) (L s')) p A= S (axis d) p* ( β • cost t):= Realm.forward s' t p A M simple v y
    have hu(s':Bool)(k:P) : κZ (Cabin (X) (K1 t) μ (L s') (F (!s'))) k A=κZ (Cabin (X) (K1 t) μ (F (!s')) (L s')) k A:= Realm.rear s' t k A M simple v y
    have ht : reckon (Cabin (axis d) (K1 t) μ (L (!s)) (F s)) p A= S (axis d) p* ( β • cost t):= by
        rw [← he (!s), Bool.not_not ]; have h(k:P): κZ ( Cabin (X) (K1 t) μ (L (!s)) (F s)) k A=κZ (Cabin (X) (K1 t) μ (F s) (L (!s))) k A:= by simpa only [ Bool.not_not ] using hu (!s) k
        unfold reckon; simp_rw [h]
    rw [ source2D M q hx s (!s) simple v, combineD, combineD, hv,he,ht ]; rw [ effortD M simple,bareK s M q hx hv y p, bareK s M q hx hv y (-p) ]; simp only [ add_zero, zero_add, smul_zero, Complex.real_smul ]; push_cast; ring
include hd
lemma charge : reckon (Vℓ (y,t)) p A=S (axis d) p*( (2*β:ℝ) • P₀ t):= by
    refine PairFlow.exercise t (fun t=>reckon (Vℓ (y,t)) p A) (fun t=> S (axis d) p * ( (2*β:ℝ) • P₀ t )) (fun t=> S (axis d) p* ( (2*β:ℝ) • cost t )) ?_ (fun t=> (( warden d t hd ).const_smul (2*β:ℝ)).const_mul _ ) (quote_lim p A (fun w _=> (descent2D M q hx s (!s) v y 2).2.2 _) ) ?_
    · intro t; have he:= deriveD p A t (F:=fun t=> Vℓ (y,t)) (K:= leap v (L0 2) (y,t)) (fun w h=> leap_speedD M q hx s (!s) simple (y,t) v w h); rw [ drive s M simple q hx hv ] at he; exact he
    · simpa only [ smul_zero,mul_zero ] using ((( reaches_cold d hd ).const_smul (2*β:ℝ)).const_mul ( S (axis d) p ))
-- scalar kernel independent charge. Connect at cold0.
omit simple hx hv hd
lemma cycle_slice {K:Law G}(he:∀ w z:Lane4 G,Bubble.wing w→Bubble.wing z→K [w,z]=0)(ht:Heat.Pass (†) K μ): cycle (†) μ K []=∫ p:P, ( (H (Z p)):ℂ)* (∑ a:G.ColorIndex, reckon K p a)∂μ:= by
   have hz(p:P): Flux.trc ( PlanetD G t ) p K [] =( H (Z p):ℂ ) * ( ∑ a:G.ColorIndex, κZ K p a ):= by
       rw [ at_trc, Walk.dotL, Walk.starLine ]; have hp(x y:Branch G Axis)(ht:parity x=true)(hx:parity y=true): K [(x,p),(y,-p)]=0:=he (x,p) (y,-p) ht hx; simp_rw [ hp (Area.U₀ _ _) (Area.C₀ _) rfl rfl, hp (Area.C₀ _) (Area.U₀ _ _) rfl rfl, mul_zero, Finset.sum_const_zero,add_zero ]; unfold κZ; simp_rw [ Walk.bond,Complex.ofReal_mul,mul_assoc,Finset.mul_sum ];
   unfold cycle; rw [ ← Fair.pack_int (f:=fun k=> Flux.trc ( PlanetD G t ) k K [] ) ( ht [] ) ]; simp_rw [ hz ]; apply integral_congr_ae; apply Eventually.of_forall; intro p; dsimp only; rw [ Fair.currency (f:=fun p=>↑(H (Z p))) (c:= (( H (Z p)):ℂ )) (fun i=>by simp_rw [ Fair.magπ ]) (fun p=> ∑ a:G.ColorIndex, κZ K p a), Cohort.sale ]; -- maybe unbound
lemma hotM : ( (H (Z p)):ℂ )* S (axis d) p=8*(MV d t p+MV d t (-p)):= by unfold plateQ MV; rw [Landau.sq_neg,Fair.costN]; push_cast; ring
lemma hot_sum : (∫ p:P,( (H (Z p)):ℂ )* S (axis d) p∂μ)=16*cost t:= by simp_rw [ hotM ]; rw [integral_const_mul, integral_add ( mv_int (d:=d) t ) ( neg_good _ ( mv_int (d:=d) t ) ), integral_neg_eq_self, Realm.costMV ]; ring
include simple hx hv hd
lemma scalar_slice : cycle ( PlanetD G t ) μ ( Vℓ (y,t) ) []=( m:ℂ )*(32* ( β • (cost t* P₀ t) )):= by
    have ht : Vℓ (y,t)∈ Wallet G:= ( Wallet G ).sub_mem ( Duet.worthwhile M q hx s (!s) 2 (y+v,t) ) ( Duet.worthwhile M q hx s (!s) 2 (y,t) ); rw [ cycle_slice t (fun w z he hv=> Duet.leap_oddD M q hx s (!s) simple w z he hv (y,t) v) ( Wallet.cour ht t ) ]; simp_rw [ Economy.charge s M simple q hd hx hv, Finset.sum_const ]; rw [ Finset.card_univ ]; simp only [ nsmul_eq_mul ]
    let f := ( m:ℂ )*((2*β:ℝ) • P₀ t)
    simp_rw [ show ∀ p:P, ( (H (Z p)):ℂ )*( (m:ℂ)*( S (axis d) p*( (2*β:ℝ) • P₀ t ) ) ) = ( (H (Z p)):ℂ ) * S (axis d) p * f from fun p=>by unfold f; ring ]; rw [ integral_mul_const, hot_sum ]; unfold f; simp_rw [ Complex.real_smul ]; push_cast; ring
lemma constantE : Vℓ (y,t) []= ((m:ℂ)*16)*( β • ((P₀ t)^2) ) := by
   refine PairFlow.exercise t (fun t=> Vℓ (y,t) []) (fun t=>(m:ℂ)*16*( β • ((P₀ t)^2) )) (fun t=>( m:ℂ )*(32* ( β • (cost t* P₀ t ))) ) ?_ ?_ ( (Duet.descent2D M q hx s (!s) v y 2).2.2 [] ) ?_
   · intro t; have he:= Duet.action_flow_stillD M q hx s (!s) simple (y,t) v; rw [ scalar_slice s M simple q hd hx hv y v ] at he; exact he
   · intro t; convert! (((( warden d t hd ).pow 2 ).const_smul β ).const_mul _) using 1; simp_rw [ Complex.real_smul ]; push_cast; ring
   · simpa using (((( reaches_cold d hd ).pow 2 ).const_smul β).const_mul ( (m:ℂ)*16 ) )
local notation "C0" => FourierGaussian.count0 d
lemma income : Duet.opposite M q s (!s) (y+v) 2 - Duet.opposite M q s (!s) y 2= (2*β:ℝ) • PhasePair.sale_at M q y 0:= by
   have he:= Tendsto.sub ( Duet.opaIR M q hx s (!s) 2 (y+v)) ( Duet.opaIR M q hx s (!s) 2 y ); obtain hq:= reaches_end d hd
   let V:= ( m:ℂ )*16; have ht:Tendsto (fun t=> Vℓ (y,t) []) atTop (𝓝 ( V*(β • ((C0:ℂ)^2)) )):= (((hq.pow 2).const_smul β).const_mul V).congr (fun t=> ( constantE s M simple q hd hx hv y v t ).symm)
   rw [ tendsto_nhds_unique he ( show Tendsto (fun t=> Duet.extract M q s (!s) 2 (y+v,t) [] - Duet.extract M q s (!s) 2 (y,t) [] ) _ _ from ht ), PairFlow.energy_end M q hd hx hv ]; unfold V; simp_rw [Complex.real_smul]; push_cast; ring
end
end YM.SignedWilsonExpansion.Overlap.Economy

