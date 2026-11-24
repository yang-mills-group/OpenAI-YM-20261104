import YM.FVA2.RateC
import YM.FVA2.UniformPoint
/-!
# Noether rigidity in the finite-regulator comparison and stronger bare leading estimates. 

No CUP bounds on the bare matrices! Use the exact leading Wick comparison once and
Gram to conclude the entire zeroth-order field regulator solution has no correction.
This relies on **engineering growth not suppression**, and the momentum team polynomial in log,
not true for arbitrary reexpression choices for the position-normalization C.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Erase
open Function Filter Set MS MS.Land MS.Landau MS.Logarithm MS.High MS.Tide MS.Menus
open Pert Maxwell Maxwell.Free Pert.Position Pert.RawLabels PositionX PositionX.Bend PositionX.Jet MS.Book MS.Book.Program
open Panel ColorCode Forge BoxOffice WorldJet Elegant MS.Book.Convolve MeasureTheory Verne Counterpart
open ArchTurn PertExtension.LatticePT
open scoped BigOperators Classical Topology ContDiff
variable {G:Gauge}(V: Warehouse G){h:G.Simple}{B: Booked (wings G)}(M:MS_Data G B){p:ℝ}(R:Booth p V.F){s:ℝ}{n m d:ℕ}
variable (P:Land.Prescription (wings G))(HS: Blaze.ExactSpin V P)(HU:Frost.Trusted P) (H: MixedStory.AllProfiles M V P)
local notation "ℓ"=> V.F
variable (i:Owner G d) (j:BasisIx G d)
local notation "Ω"=> sameAxis V.F d
-- projection at d. no choice of η.Sx. Hp log. sx complex cost.
lemma fare (x y:ℝ)(n:ℕ): (Ω).coord j (bareD V P x y n d (Ω ( Land.read i )))= factorEF x d j.size*oil (P.fees d i) j n y := by
   rw [D_own, loadAt, Blaze.factory,map_sum, Finset.sum_eq_single_of_mem j ( Finset.mem_univ _ ) ]; · simp; rfl
   intro k _ hk; simp [hk]
variable {q:ℕ+}
private lemma empty_poly (F:Polynomial ℝ)(x:ℕ→ℝ)(hv:Tendsto x atTop atBot)(hf:Tendsto (F.eval ∘ x) atTop (𝓝 0)): F=0:= by -- use duplicate from RateC private
    by_cases ht:F.degree≤0
    · have ht:= Polynomial.eq_C_of_degree_le_zero ht; have hh : F.coeff 0=0:= by
         apply tendsto_nhds_unique _ hf; conv in F.eval => rw [ht];
         simp only [Polynomial.eval_C]; exact tendsto_const_nhds
      rw [ht, hh,map_zero ]
    obtain he:= F.abs_tendsto_atBot ( lt_of_not_ge ht ); have hx:= he.comp hv; have hQ : Tendsto (fun i=>|F.eval ( x i )|) atTop (𝓝 0):= by simpa [abs_zero,Function.comp_def ] using hf.abs;
    obtain ⟨i,hi,hI⟩:=( ( hQ.eventually ( gt_mem_nhds (zero_lt_one) ) ).and ( hx.eventually (eventually_ge_atTop 1 ) ) ).exists; exact False.elim ( (not_lt_of_ge (show |F.eval (x i)| ≥ 1 from hI)) hi )
lemma slot_t (U:Polynomial ℝ)(q:ℕ+)(hq:1<q.val) (m:ℕ)(hm:m ≤ d)(h:Tendsto (fun k=>factorEF (epsilon q k) d m*(↑(U.eval (-Pond.clock q k):ℝ):ℂ)) atTop (𝓝 0)): U=0:= by
    let x(k):=-Pond.clock q k; apply empty_poly U x (tendsto_neg_atTop_atBot.comp ( Pond.forward q hq )); have H:Tendsto (fun k:ℕ=> ( (( epsilon q k ):ℝ):ℂ )^(d-m)) atTop (𝓝 ( (0:ℂ)^(d-m))) := by
       have ht:= Complex.ofRealCLM.continuous.continuousAt.tendsto.comp ((epsilon_zero hq).mono_right inf_le_left); exact ht.pow _
    let f(k:ℕ):=(↑(U.eval ( x k )):ℂ); have ht:= H.mul h; rw [mul_zero] at ht;
    apply Tendsto.congr' _ (Complex.reCLM.continuous.continuousAt.tendsto.comp ht ); refine Eventually.of_forall fun i=>?_ ; let W:ℂ:= epsilon q i;
    have h: W≠0:= by unfold W; exact_mod_cast (epsilon_pos q i).ne';
    have hx: W^(d-m)*(( factorEF W d m )* f i)=f i:= by rw [← mul_assoc,factorEF,← mul_assoc,mul_right_comm,pow_sub₀ _ h hm ]; field_simp -- need pow_sub₀ signature
    exact congr_arg Complex.reCLM hx
lemma planted (n:ℕ)(i: Owner G d)(Q:Land.Prescription (wings G))(q:ℕ+) (hq:1<q.val) (he:Tendsto (fun k=> (Ω).coord j (( bareD V P (epsilon q k) (-Pond.clock q k) n d-bareD V Q (epsilon q k) (-Pond.clock q k) n d ) ( Ω ( Land.read i )))) atTop (𝓝 0)): (P.fees d i n).register j = (Q.fees d i n).register j:= by
   apply sub_eq_zero.mp; apply slot_t (d:=d) _ q hq j.size ( not_under j ); simp_rw [LinearMap.sub_apply,map_sub,fare, ← mul_sub, oil, ← Complex.ofReal_sub ] at he; simp_rw [Polynomial.eval_sub]; exact he -- orientation map Real
include HS HU H
lemma evenE (hi:j≠ Land.read i): ( P.fees d i 0 ).register j=0:= by
   let P':= P; let q:ℕ+ :=3; have hq:1< q.val:=by decide
   let f(k):= epsilon q k; let x(k):=0-Pond.clock q k; let D(k):= projectionD V P (f k) (x k) 0 d; let g(k):= mother V P HS HU d q 0 k; let L(k):= (Ω).coord j ( ( bareD V P ( f k ) (x k) 0 d ) (Ω ( Land.read i ) ));
   let Q:Buffer ℓ d→ℂ:= fun p=> (Ω).coord j (p.val (Ω ( Land.read i ))); have hQ(k):Q (g k)=L k:= by
       unfold Q L; change (Ω).coord j ( bareD V P (f k) ( x k ) 0 d (Ω ( Land.read i ))-Ω (Land.read i)) = _; rw [map_sub, show ∀ i:BasisIx G d,(Ω).coord j (Ω i)=if i=j then 1 else 0 from ?_,if_neg (Ne.symm hi),sub_zero ]; intro i; by_cases H:i=j <;> simp [Module.Basis.coord_apply,H] -- orientation
   have ht(B:Buffer ℓ d): ContinuousAt Q B:= by
        let T : E ℓ d →L[ℂ]ℂ:= LinearMap.toContinuousLinearMap ((Ω).coord j); exact T.continuous.continuousAt.comp ( ( Continuous.clm_apply ( show Continuous ( fun p:Buffer ℓ d=>p.val ) from continuous_subtype_val ) ( show Continuous (fun _:Buffer ℓ d=>Ω ( Land.read i )) from continuous_const ) ).continuousAt )
   apply slot_t _ q hq j.size ( show j.size≤d from not_under j );
   rw [ ← show (fun k=> Q (g k)) = ( fun k=> factorEF (epsilon q k) d j.size * ↑(( (P.fees d i 0).register j ).eval (-Pond.clock q k)) ) from ?_ , ← show Q 0=0 from map_zero ((Ω).coord j) ]; apply Tendsto.comp (ht 0).tendsto ( rent_calm V P M HS HU H d q hq 0 ); exact funext (fun k=> by rw [hQ]; unfold L; rw [fare ]; unfold x; rw [zero_sub ]; rfl) -- layout new lines
lemma solo (x y:ℝ)(d:ℕ)(hx:x≠0): bareD V P x y 0 d=1:= by
   apply (sameAxis V.F d).ext; intro i; rw [ D_pane, loadAt,Blaze.factory, Finset.sum_eq_single ( Land.read i.2 (d:=i.size) ) ]; · unfold rateV; let j:= Land.read i.2 (d:=i.size) («B»:= wings G); unfold oil; rw [ (P.init i.size i.2).Single j le_rfl, if_pos rfl,Polynomial.eval_one,Complex.ofReal_one,mul_one,factorEF, show j.size=i.size from rfl,inv_mul_cancel₀ (pow_ne_zero i.size (by exact_mod_cast hx)),one_smul ]; exact same_up .. -- factor shift b
   · intro j _ h; rw [rateV,oil, evenE V M P HS HU H _ j h, Polynomial.eval_zero,Complex.ofReal_zero,mul_zero,zero_smul ]
   simp
lemma motherZ (x y:ℝ)(hx:x≠0): bareReset V P x y 0 HS HU d=0:= by
   apply PositionX.Ribbon.follows_right; change projectionD V P x y 0 d=0; rw [projectionD,solo V M P HS HU H x y d hx ]; exact sub_self _
open Prow PayAll Fountain
lemma fares_free {q:ℕ+}(_hq:1<q.val)(i:ℕ)(d:ℕ): Elegant.motion V q i d 0= unglue V P HS HU q 0 i d 0:= by rw [φconomic, pred_zero, renamed, show dawnFrame V P HS HU q 0 i d 0=0 from motherZ V M P HS HU H (epsilon q i) _ (epsilon_pos q i).ne',market_zero ] -- i d.C
lemma budget0 {q:ℕ+}(hq:1<q.val)(p: Pert.Position.Section ℓ d): ∃ C:ℝ,0<C∧∀ᶠ i in atTop, ‖lookie ℓ p ( Elegant.motion V q i d 0 )-lookie ℓ p (pureBank ℓ d)‖ ≤ C*feel q i:= by
    obtain he:=( start_power V P M HS HU H q hq 0 ( show Tendsto ( fun i:ℕ=>i ) atTop atTop from tendsto_id ) d p 0 ).1; obtain ⟨C,hc,hᵢ⟩:= he; refine ⟨C,hc,hᵢ.mono fun i hi=>?_⟩;
    rw [fares_free V M P HS HU H hq, ← dist_eq_norm,← Spring.vintage_ms V M 0 ]; exact hi
lemma RawZero {q:ℕ+}(hq:1<q.val){T:Set (Points n)}(U:T ⊆ conf n)(hx:IsCompact T)(v:Fin n→ E ℓ d): ∃ C:ℝ,0<C∧∀ᶠ i in atTop,∀ o∈origins q i,∀ u:Grid.offsets q n i,Grid.sample q i u∈ T→ dist ( PowerSeries.coeff 0 ( rawL V q i u o d v ) ) (visible ℓ d ( Grid.sample q i u ) v) ≤ C*feel q i:= by
    obtain ⟨C,h,Q⟩:= Fountain.rate_point V P M HS HU H q hq 0 U hx 0 v; refine ⟨C,h,?_⟩; filter_upwards [ Q ] with i hX o ho u hu; obtain he:= hX o ho u hu; rw [ born_eff, solo V M P HS HU H _ _ _ ( epsilon_pos q i ).ne',vintage V M 0 _ ( U hu ) ] at he; exact he
end YM.FVA2.Erase
