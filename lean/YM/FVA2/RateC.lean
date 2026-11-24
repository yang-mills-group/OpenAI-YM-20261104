import YM.FVA2.PolarMD
/-! # An exact check of the Wilson → MS intermediate coupling is odd.
From only geometric power bounds and exact finite identities; no assumption on smooth comparison clock phases.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Plot
open Function Filter Set MS MS.Land MS.Landau MS.Logarithm MS.High MS.Tide MS.Menus
open Pert Maxwell Maxwell.Free Pert.Position Pert.RawLabels PositionX PositionX.Bend PositionX.Jet MS.Book MS.Book.Program
open Panel ColorCode Pic Forge Forge.Parity BoxOffice WorldJet Elegant MS.Book.Convolve
open scoped BigOperators Classical Topology ContDiff
variable {G:Gauge}(V: Warehouse G){h:G.Simple}{B: Booked (wings G)}(M:MS_Data G B){p:ℝ}(R:Booth p V.F){s:ℝ}{n m d:ℕ}
variable (P:Land.Prescription (wings G))(HS: Blaze.ExactSpin V P)(HU:Frost.Trusted P) (H: MixedStory.AllProfiles M V P)
local notation "ℓ"=> V.F
open Finset
variable {q:ℕ+}(hq:1<q.val) (A:Knocker h R q hq ( BoxOffice.warehouse V ))
lemma parity0 {a:Word ℝ}(he:turn a= -a)(n:ℕ)(h:Even n): a n=0:= by obtain ht:= congr_fun he n; change (-1:ℝ)^n • a n= -a n at ht; rw [h.neg_one_pow,one_smul] at ht; linarith
private lemma ℤone {S F T:Word ℝ}(he:light S)(hf:light T)(hk:0<n)(hv:∀ i:ℕ,i<n→S i=T i): ren S F n=ren T F n+ (S n-T n)*F 1:= by
    apply Complex.ofReal_injective; let f(i:ℕ):ℂ := (F i:ℝ); have h (x:Word ℝ)(H:Jet.light x) : ((ren x F n:ℝ):ℂ)=substitute (symbol x) f n:= by rw [renReal _ H _, Program.rules, show Finset.Iic n = Finset.range (n+1) from by ext; simp ]; rfl
    let a:=symbol S; let b:= symbol T; push_cast; rw [h S he,h T hf]; 
    have hz : Preset b a n := fun i hi=> by rw [show ∀ a:Word ℝ,PowerSeries.coeff i (symbol a)=_ from fun a=> bill_q a i,show PowerSeries.coeff i (symbol S)=_ from bill_q ..,hv i hi];
    rw [Program.only_one f hz (litK hf) hk, bill_q,bill_q ]; rfl
private lemma rigid {S T:Word ℝ}(he:light S)(hT:turn T= -T)(hx:Even n)(hn:0<n)(hp:∀ i:ℕ,i<n→Even i→S i=0) : ren S T n=S n*T 1:= by
    let k:= -(turn S); let A:= turn T; have hk:Jet.light k:= by unfold light k; simp [ show S 0=0 from he ];
    have hi : turn (ren S T)= - ren k T:= by
       rw [ ← ren_turn_x T he]; obtain hv:= ren_turn_v T hk; unfold k at hv; rw [neg_neg] at hv; rw [← hv,hT ]; exact (ren_writes (-LinearMap.id) k T).symm
    have ht : ∀ i,i<n→ k i= S i:= by
        intro i hv; rcases Nat.even_or_odd i with hx|hx; · rw [show S i=0 from hp i hv hx ]; simp [k, turn, hp i hv hx ]
        simp [k,turn,hx.neg_one_pow ]
    have hg:ren k T n=ren S T n+(-2*S n)*T 1:= by rw [ℤone hk he hn ht, show k n= - S n from ( by unfold k turn; simp only [hx.neg_one_pow,one_smul,Pi.neg_apply] ) ]; ring
    obtain hh:= congr_fun hi n; rw [Pi.neg_apply, hg,show turn ( ren S T ) n= ren S T n from (by unfold turn; rw [hx.neg_one_pow,one_smul])] at hh; linarith
private lemma empty_poly (F:Polynomial ℝ)(x:ℕ→ℝ)(hv:Tendsto x atTop atBot)(hf:Tendsto (F.eval ∘ x) atTop (𝓝 0)): F=0:= by
    by_cases ht:F.degree≤0
    · have ht:= Polynomial.eq_C_of_degree_le_zero ht; have hh : F.coeff 0=0:= by
         apply tendsto_nhds_unique _ hf; conv in F.eval => rw [ht]; -- conv goal?
         simp only [Polynomial.eval_C]; exact tendsto_const_nhds
      rw [ht, hh,map_zero ]
    obtain he:= F.abs_tendsto_atBot ( lt_of_not_ge ht ); have hx:= he.comp hv; have hQ : Tendsto (fun i=>|F.eval ( x i )|) atTop (𝓝 0):= by simpa [abs_zero,Function.comp_def ] using hf.abs;
    obtain ⟨i,hi,hI⟩:=( ( hQ.eventually ( gt_mem_nhds (zero_lt_one) ) ).and ( hx.eventually (eventually_ge_atTop 1 ) ) ).exists; exact False.elim ( (not_lt_of_ge (show |F.eval (x i)| ≥ 1 from hI)) hi )
local notation "Ψ"=> Elegant.clockM P q 0
local notation "θ"=> Bend.curveF (warehouse V) q h R
local notation "T"=> isell h V P HS HU q 0 R
include HS HU H A -- C.born uniform. K.turn etc
lemma coupling_e (p:ℕ) (he:Even p) (hk:0<p): (P.team p).coupling=0:= by
   induction p using Nat.strong_induction_on with| h p ih=>
    let x(i):=0-Pond.clock q i; let f:= (P.team p).coupling;
    have hl(k:ℕ)(h₁: Even k)(hT:0<k)(i:ℕ): Ψ i k=( P.team k ).coupling.eval (x i):= by unfold clockM ζq Clock.rate; simp only [PowerSeries.coeff_mk,if_neg ( show k ≠0 from (by omega) ), if_neg (show k≠1 from (by obtain ⟨j,hj⟩:=h₁; omega) ) ]; rfl
    have hu(k:ℕ)(h₁:k<p)(hc:Even k)(i:ℕ): Ψ i k=0:= by
        by_cases ht:k=0; · rw [ ht ]; exact φzero ..
        rw [hl k hc (by omega) i, ih k h₁ hc (by omega), Polynomial.eval_zero]
    have heT : ∀ᶠ i in atTop, (T i) p= Ψ i p * θ i 1:= by
       filter_upwards [ meterBound h V P M HS HU H q hq (0:ℝ) R, κ_odd (warehouse V) q h R hq] with i hi hv; rw [hi]; exact rigid (φzero ..) hv he hk fun _ hi h₁=>hu _ hi h₁ i -- binder pricing T order?
    have hp:TurnsOn atTop T (ξ h V M 0 R):=ℚpricing h V P M HS HU H q hq (0:ℝ) R; -- T replaced manual
    apply empty_poly f x (show Tendsto x atTop atBot by simpa [x,Function.comp_def] using tendsto_neg_atTop_atBot.comp ( Pond.forward q hq ))
    obtain hh:= hp p; obtain hL:= A.holdsA;
    have hx:Tendsto (fun i=> T i p / θ i 1 ) atTop (𝓝 0) := by rw [parity0 (χodd (h:=h) V M R (0:ℝ)) p he] at hh; simpa only [div_one,Pi.div_def] using hh.div hL one_ne_zero; -- 0/1 fill
    apply hx.congr'; filter_upwards [heT,A.definedA ] with i hi hT; rw [hi,mul_div_cancel_right₀ _ hT.2]; exact hl _ he hk _
lemma clockParity : ∀ (x:ℝ), turn (ζq P.team x) = - ζq P.team x:= by
    intro x; funext p; change (-1:ℝ)^p • ζq P.team x p= -ζq P.team x p; rcases Nat.even_or_odd p with he|he; swap; · rw [he.neg_one_pow, neg_one_smul ]
    rcases p with _|p; · rw [show ζq P.team x 0=0 from Clock.rooted ..,smul_zero,neg_zero ]
    simp [ζq, Clock.rate, show p≠0 from (by obtain ⟨a,hG⟩:=he; omega), coupling_e V M R P HS HU H hq A ( p+1 ) he ( Nat.succ_pos _ ) ]
-- bare Laurent parameter uniqueness. Position equivalences plus parity suffice;
-- canonical changes need not actually be unique as maps on actions, or PL pivots.
include H A
lemma coupling_eq {U:Land.Prescription (wings G)}(S: Blaze.ExactSpin V U)(T': Frost.Trusted U)(E: MixedStory.AllProfiles M V U)(n:ℕ)(hL:1<n): (P.team n).coupling=(U.team n).coupling:= by
   induction n using Nat.strong_induction_on with | h n ih=>
    let X(i):=0-Pond.clock q i; let f:= (P.team n).coupling; let g:= (U.team n).coupling; let V':= clockM U q 0; let b:= isell h V U S T' q 0 R;
    have hv(i:ℕ) (P:Land.Prescription (wings G))(n:ℕ)(hn:1<n): Elegant.clockM P q 0 i n=(P.team n).coupling.eval (X i):= by unfold clockM ζq Clock.rate; simp only [PowerSeries.coeff_mk,if_neg (show n≠0 from (by omega)),if_neg (show n≠1 from (by omega))]; rfl
    have HZ : ∀ᶠ i in atTop, (T i n)=(b i n)+(f-g).eval ( X i )* θ i 1:= by
         filter_upwards [ meterBound h V P M HS HU H q hq 0 R, meterBound h V U M S T' E q hq 0 R ] with i hx hh; unfold b; rw [hx,hh ]; apply Eq.trans (ℤone (φzero P q 0 i) (φzero U q 0 i) (show n>0 from by omega) ?_) ?_
         · intro k h; rcases k with _|(_|k); · exact ( φzero P q 0 i ).trans (φzero U q 0 i).symm; -- Dot grammar h
           · exact ( φone P q 0 i ).trans (φone U q 0 i).symm
           rw [hv i P _ (by omega), hv i U _ (by omega), ih _ h (by omega)]
         rw [Polynomial.eval_sub,hv i P n hL,hv i U n hL ]
    have hx : Elegant.TurnsOn atTop T (ξ h V M 0 R):=ℚpricing h V P M HS HU H q hq 0 R; have ht : Elegant.TurnsOn atTop b (ξ h V M 0 R):=ℚpricing h V U M S T' E q hq 0 R; apply sub_eq_zero.mp; refine empty_poly (f-g) X (show Tendsto X atTop atBot by simpa [ X, Function.comp_def ] using tendsto_neg_atTop_atBot.comp (Pond.forward q hq)) ?_;
    apply ( show Tendsto (fun i=> (T i n-b i n)/θ i 1) atTop (𝓝 0) from (by simpa only [ Pi.div_def, Pi.sub_def, div_one, sub_self] using (( hx n ).sub ( ht n )).div A.holdsA one_ne_zero)).congr'; filter_upwards [HZ, A.definedA] with i hi H; rw [hi,add_sub_cancel_left,mul_div_cancel_right₀ _ H.2]; rfl
lemma clock_eq {U:Land.Prescription (wings G)}(S: Blaze.ExactSpin V U)(T': Frost.Trusted U)(E: MixedStory.AllProfiles M V U) : Clock.rate P.team= Clock.rate U.team := by
    funext x; apply PowerSeries.ext; intro i; simp only [Clock.rate, PowerSeries.coeff_mk ]; by_cases h:i≤1; · interval_cases i <;> simp
    rw [coupling_eq V M R P HS HU H hq A S T' E i (by omega)]
end YM.FVA2.Plot
