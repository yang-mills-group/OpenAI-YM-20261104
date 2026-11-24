import YM.FVA2.StratParity
import YM.FVA2.TokenPay
/-!
# Rigidity of the actual higher-order field pricing across signed connection inversion
 stronger than fitting p. Mark $\hbar$ parity throughout.Momentum.Real.W.Plan.
 -/
set_option autoImplicit false
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 700000
namespace YM.FVA2.Erase
open Set Filter Function Finset MeasureTheory Pert Pert.Position Maxwell Maxwell.Free PositionX PositionX.Jet PositionX.Ribbon Topology Elegant Verne Counterpart Blaze Frost ColorCode
open MS MS.Land MS.Landau MS.Tide MS.Menus  Lattice BoxOffice ArchTurn
open PositionX.Bend Prow PertExtension.LatticePT WorldJet Plot
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}(V: Warehouse G){h:G.Simple}{B: Booked (wings G)}(M:MS_Data G B){p:ℝ}(R:Booth p V.F){s:ℝ}{n m d:ℕ}
variable (P:Land.Prescription (wings G))(HS: Blaze.ExactSpin V P)(HU:Frost.Trusted P) (H: MixedStory.AllProfiles M V P)
local notation "ℓ"=> V.F
local notation "Ω"=> sameAxis V.F d
variable {q:ℕ+}(hq:1<q.val)(K:Knocker h R q hq ( BoxOffice.warehouse V ))
local notation "Fχ"=> Elegant.clockM P q 0
variable (i:BasisIx G d)(u:Owner G d)(x y:ℝ) {Y:Word (Buffer ℓ d)}
local notation "Δ"=> par V.F d
local notation "ϵ"=> ( Reed.ϕ (R:=ℂ) )
-- coordinate & turn
lemma ξi (p:E V.F d): (Ω).coord i ( Δ p )= ϵ i.grade* (Ω).coord i p:= by
   rw [ ← (Ω).sum_repr p ]; simp_rw [map_sum,map_smul, field_par, map_smul, Finset.mul_sum ]; apply Finset.sum_congr rfl; intro j _; by_cases h:i=j; subst j; simp [smul_eq_mul, mul_comm ]; simp [Module.Basis.coord_apply,h];
-- normalized leading issue at n=0.Unit.F.C.Price. proof_learnt preserving Hart.$a all
lemma mirror (S:Word (Buffer ℓ d))(i j:BasisIx G d)(m:ℕ) : (Ω).coord i (frameWord ℓ (cPar ℓ ∘ turn S) m (Ω j))= (ϵ (i.grade+j.grade+m))* (Ω).coord i (frameWord ℓ S m ( Ω j )):= by
    have he:(Ω).coord i (bufferL ℓ ( cPar ℓ ( turn S m ) ) ( Ω j ))= (ϵ (i.grade+j.grade+m))* (Ω).coord i (bufferL ℓ ( S m ) (Ω j)):= by
       rw [bufferL_eq,cPar_eq,ξi, field_par, ← bufferL_eq,map_smul,map_smul ]; unfold turn; let f:= ((Ω).coord i).restrictScalars ℝ; let c := ( Ω j ); let p :Buffer ℓ d→ₗ[ℝ] ℂ:={ toFun q:= f (q.val c),map_add' x y:=f.map_add _ _,map_smul' x a:=f.map_smul _ _ }; change ϵ i.grade *( ϵ j.grade • p (( (-1:ℝ)^m ) • S m ) )= _; rw [ map_smul, Complex.real_smul ]; change ϵ i.grade * ( ϵ j.grade * (( ( ((-1:ℝ)^m):ℝ ):ℂ ) * _) )= _; unfold Reed.ϕ; push_cast; rw [pow_add,pow_add ]; rw [mul_assoc,mul_assoc ] ; rfl
    unfold frameWord; rw [LinearMap.add_apply,LinearMap.add_apply,map_add,map_add, mul_add ]; refine congr_arg₂ (·+·) he ?_; unfold topD; split
    next hm=> subst m; by_cases h:i=j; swap; · simp [Module.Basis.coord_apply,Ne.symm h ]
              subst i; rw [add_zero, Reed.ϕ,pow_add, ← Reed.ϕ, Reed.invol ]; simp
    next _=> simp
private def ornament (Q:ℕ)(k:ℕ) (i:BasisIx G d) : Polynomial ℝ:= ((-1:ℝ)^(i.grade+Q+k)) • ( P.fees d u k ).register i
lemma moneyShape (n:ℕ): (Ω).coord i (frameWord ℓ (cPar ℓ ∘ turn ( posesD V P HS HU x y d )) n (Ω ( Land.read u )))= factorEF x d i.size* ↑( ( ornament P u ( Land.read u ).grade n i : Polynomial ℝ ).eval y ):= by rw [mirror, frame_projects, fare ]; unfold ornament Reed.ϕ; rw [ Polynomial.eval_smul ]; unfold oil; rw [smul_eq_mul,Complex.ofReal_mul]; push_cast; ring
private lemma schemeReflect (he:∀ d (u:Owner G d)(i:BasisIx G d), ornament P u (Land.read u).grade n i=(P.fees d u n).register i) : (cPar ℓ (d:=d) ∘ turn (posesD V P HS HU x y d)) n= bareReset V P x y n HS HU d:= by
   let S(d):= posesD V P HS HU x y d; let W(d):= cPar ℓ ( d:=d )∘ turn ( S d ); have h0(d:ℕ)(u:Owner G d): bufferL ℓ ( W d n ) (sameAxis V.F d ( Land.read u ))= bufferL ℓ (S d n) (sameAxis V.F d (Land.read u )):= by
       let Y:= sameAxis V.F d; let t:= Y ( Land.read u ); have hu: frameWord ℓ ( W d ) n t= frameWord ℓ ( S d ) n t:= by apply Y.repr.injective; ext1 i; change Y.coord i _=Y.coord i _; rw [show Y.coord i ( frameWord ℓ ( W d ) n t)=_ from moneyShape V P HS HU i u x y n, he d u i,frame_projects,fare ]; rfl
       unfold frameWord at hu; simp only [LinearMap.add_apply] at hu; exact add_right_cancel hu
   apply follows_right; apply (Ω).ext; intro i; let m:= i.size; let q:= not_under i; let p:Owner G i.size:= i.2; let t:=sameAxis V.F m (Land.read p); have hf : Ω i= up ℓ q t := (same_up V.F q (Land.read p)).symm
   have hS : zoomL ℓ q ( S d n )=S m n:= collective ..; have hW : zoomL ℓ q ( W d n )=W m n:= by unfold W turn; rw [Function.comp_apply, Function.comp_apply, zoomL_par,map_smul,hS ];
   rw [hf ]; change ( W d n ).val ( up ℓ q t )=( S d n ).val ( up ℓ q t ); rw [← zoomL_eq, ← zoomL_eq,hS,hW ]; exact congr_arg _ ( h0 m p ) -- order
private lemma topSub {V:Type*}[NormedAddCommGroup V]{P Q:ℕ→V}{x:V}(h:Tendsto P atTop (𝓝 x))(ht:Tendsto Q atTop (𝓝 x)): Tendsto (fun i=> P i-Q i) atTop (𝓝 0):= by simpa using! h.sub ht
include HS HU H K
lemma spirited (n d:ℕ)(i:BasisIx G d)(u:Owner G d) : ornament P u ( Land.read u ).grade n i= (P.fees d u n).register i:= by
    induction n using Nat.strong_induction_on generalizing u d with | h n ih=>
       by_cases hn:n=0; · subst n; by_cases hz:i=Land.read u; swap; · rw [ornament, evenE V M P HS HU H _ _ hz ]; exact smul_zero _
                          subst i; rw [ ornament,add_zero,pow_add,← Reed.ϕ, Reed.invol, one_smul ];
       let X(k:ℕ):ℝ:=0-Pond.clock q k; let L(k):= posesD V P HS HU (epsilon q k) (X k) d; let Y(k):=bust h V P HS HU q 0 k d; let U(k:ℕ):Word (Buffer V.F d):= cPar V.F ∘ turn ( L k ); let C (k:ℕ): Word (Buffer V.F d):= cPar V.F ∘ turn ( Y k );
       have hF : ∀ᶠ k in atTop,luxury ( U k ) ( C k )= luxury ( L k ) ( Y k ):= by
           let Z:= warehouse V; filter_upwards [ trade h V P M HS HU H q hq 0 d, Z.report_par h q hq d ] with k hk hZ; let f:= Z.ftReport h q k d; let T:= Fχ k; let g:= cPar ( d:=d ) ℓ; change g ∘ f=turn f at hZ; have hx: g ∘ turn f=f:= by rw [← hZ ]; exact funext fun i=> cPar_cycle ℓ _
           unfold U C; rw [ ← Verne.transported _ _ ( cPar V.F ) Plot.follow_parity, ← Plot.TurnC, show luxury (L k) (Y k)= ren T f from hk.1.symm, Plot.turnsR (s:=T) ( clockParity V M R P HS HU H hq K ( X k )) ( φzero P q 0 k ) f, ren_writes,hx ]; -- cPar $χ$
       let T:= ( Buffer ℓ d ); let t' := turns h V M (0:ℝ) d; let g : Buffer ℓ d→L[ℝ] Buffer ℓ d:= LinearMap.toContinuousLinearMap (E:=Buffer ℓ d) (F':=Buffer ℓ d) (cPar ℓ); have hK(n): Tendsto (fun i=>Y i n) atTop (𝓝 ( t' n )):= ticking V M P HS HU H hq d n 0;
       have hX(k): U k 0=0:= by unfold U; rw [Function.comp_apply,turn_zero, show L k 0=0 from motherZ V M P HS HU H _ _ (epsilon_pos q k ).ne',map_zero ];
       obtain hh:sepSim t' := turnL V M 0 d; have ht : Tendsto (fun i=>C i n) atTop (𝓝 ( t' n )):= by have hu : g (( -1:ℝ )^n • t' n )= _ := congr_fun hh n; rw [ ← hu ]; exact g.continuous.continuousAt.tendsto.comp ( (hK n).const_smul ( (-1:ℝ)^n ) );
       have hx:=clean_ξ hF (Eventually.of_forall fun k=> ⟨ hX k,fun j hj=> schemeReflect V P HS HU _ _ ( fun d u i=> ih j hj _ i u ) ⟩ ) ( Nat.pos_of_ne_zero hn ) ( show Tendsto (fun i=>Y i 0) _ (𝓝 0) from Elegant.reports0 h V M _ d ▸ hK 0 ) ( topSub (V:=Buffer ℓ d) (P:=fun i=>Y i n) (Q:=fun i=>C i n) (hK n) ht );
       let K(j:ℕ):= factorEF ( epsilon q j ) d i.size; let Z:= ornament P u (Land.read u).grade n i; let p:=( P.fees d u n ).register i; apply sub_eq_zero.mp; apply Erase.slot_t _ q hq _ (not_under i);
       let R: Buffer ℓ d→ℂ:= fun t=> ((sameAxis ℓ d).coord i) ( t.val (sameAxis ℓ d ( Land.read u )) ); let η:= sameAxis V.F d; have hp: ContinuousAt R 0 := by
            let T : E ℓ d →L[ℂ]ℂ:= LinearMap.toContinuousLinearMap (η.coord i); exact T.continuous.continuousAt.comp ( ( Continuous.clm_apply ( show Continuous (fun p:Buffer ℓ d=>p.val) from continuous_subtype_val) ( show Continuous (fun _:Buffer ℓ d=> η (Land.read u)) from continuous_const) ).continuousAt )
       rw [← show R 0=0 from map_zero ( η.coord i ) ]; apply Tendsto.congr _ ( hp.tendsto.comp hx ); intro j; rw [ ← zero_sub (Pond.clock q j), Polynomial.eval_sub,Complex.ofReal_sub,mul_sub ]; unfold R; let t:= η (Land.read u); change η.coord i ( bufferL ℓ ( U j n ) t-bufferL ℓ ( L j n ) t)=K j* (( Z.eval ( X j ):ℝ):ℂ)- K j*(( p.eval ( X j ):ℝ):ℂ); have hg {T:Word (Buffer ℓ d)}: frameWord ℓ T n= bufferL ℓ ( T n ):= by unfold frameWord topD; rw [ if_neg hn, add_zero ];
       rw [map_sub, ← hg, ← hg, frame_projects, fare ]; exact congr_arg₂ (·-·) ( moneyShape V P HS HU i u _ _ n ) rfl -- check Frame projects chooses RHS
lemma parity_rule {n:ℕ}(he: Odd (i.grade+( Land.read u ).grade+n)) : (P.fees d u n).register i=0:= by
    obtain hv:= spirited V M R P HS HU H hq K n d i u; unfold ornament at hv; rw [he.neg_one_pow, neg_one_smul ] at hv; exact neg_eq_self.mp hv
end YM.FVA2.Erase
