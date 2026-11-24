import YM.FVA2.ScaleGenerator
/-!
# Identify the unique MASS correction as in the manuscript

 Uses THE X calibration and any ERA flows prescribed at that coordinate. Shows equivalence
 of imposing exact generator criterion when computing the nilpotent-strict correction to the
 grade-scaling of the regulator perturbative limit by using only itself. Proved in actual Booth.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.FVA2.RadScale.Era
open Function Filter Topology Set MeasureTheory Finset
open Lattice Maxwell Maxwell.Free Pert Pert.Position Pert.RawLabels PositionX PositionX.Bend PositionX.Jet PositionX.Ribbon Elegant Verne Strat Panel ColorCode
open MS MS.Land MS.Landau MS.Menus MS.Tide MS.Tone Hop Ember Taper Forge
open Month Meter
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{F:Labels.Frames G}
abbrev shift (F:Labels.Frames G)(s:ℝ)(N:Strat F):= Λ F (-s)* N * Λ F s
lemma glimpse_T (A:Hop F)(s:ℝ): (glance s A).Z= shift F s A.Z:= rfl
lemma glimpse_s (N:Strat F){t:ℝ}: only (shift F t N) = shift F t (only N):= by unfold shift; rw [onlyT,onlyT, onlySeq,onlySeq ]; -- lower closure
variable {W Q:ℝ→Hop F} {A: Panel F}{D:(d:ℕ)→ Detector F d}{r:ℝ}{R: Booth r F}
/-- Conjugate scale by ANY Near conversion. Provide coefficients in generator comparison. -/
lemma link (H:Month A W D R)(K: Hop F)(T:Month (Hop.act A K) Q D R)(s:ℝ): K*Q s=W s*glance s K:= by
    apply Hop.distinct _ _ _ D R H.first H.funds; rw [ ← Hop.act_step, ← Hop.act_step, ← T.eats, ← H.eats,← bevel ]
-- strictly lowering K marker
lemma hop_ident (K:Hop F){v w:Hop F} (s:ℝ) (hv:K.f=headway)(hP: K.Z.only=1)(h: gradedStep v)(he:gradedStep w) (ht: K*v=w*glance s K): v=w:= by
   obtain hp:= congr_arg Hop.f ht; obtain hx:= congr_arg (fun p:Hop F=> only p.Z) ht;
   change only (K*v).Z=only (w *glance s K).Z at hx
   rw [walkF,walkF, timely,hv,ren_head,head_ren v.rooted ] at hp; apply Hop.ext hp; rw [walkZ,walkZ, onlyT, iconic,onlyT, timely,hv,resumeHead,hP,resume0,one_mul,glimpse_T, glimpse_s, hP, show shift F s 1=1 from ?_] at hx; unfold gradedStep at h he; rw [ mul_one,h,he ] at hx; exact hx -- h prop not eq.rewrite gradedStep
   unfold shift; rw [mul_one, south ]
private lemma burn1 (M:Hop F)(j:ℕ): PowerSeries.coeff j ((PS M.f)^j)=1:= by
    let f:=M.f; let A:ℝ→+*ℂ:=Complex.ofRealHom; let b:= Elegant.symbol f; have hb:b=PowerSeries.map A ( PS f ):= by apply PowerSeries.ext; intro i; rw [ Elegant.bill_q, PowerSeries.coeff_map, PowerSeries.coeff_mk ]; rfl
    obtain ht:( PowerSeries.coeff j ( b ^ j ) = _ ) := (Elegant.ageT (Elegant.litK M.rooted) j); -- namespace Lit
    rw [hb, ←map_pow, PowerSeries.coeff_map] at ht; apply Complex.ofReal_injective;
    change A (_:ℝ)= ( (1:ℝ):ℂ ); rw [ht, Elegant.bill_q, M.primary ]; simp
section onlys
variable {d n:ℕ} (s:ℝ){T:Hop F}{u: Word (Buffer F d)}
local infixl:70 "◆"=> luxury
local notation "L" => Taper.Step (F:=F) (d:=d)
private lemma focuses (v:Hop F)(h:∀ i<n,u i=0)(k:ℕ)(hz:k≤n): ren v.f u k=u k:= by rw [ RadScale.substitute v.f v.rooted u k, Finset.sum_range_succ, burn1,one_smul,show ∑ i∈ range k, PowerSeries.coeff k (PS v.f ^i) • u i=0 from ( sum_eq_zero fun i hi=>by rw [ h i ((mem_range.mp hi).trans_le hz), smul_zero ] ),zero_add ]
private lemma stage_fee (b:Hop F)(H: (ren b.f u) ◆ b.Z.wire d=( b.Z.wire d )◆ ( L s ∘ u ) ) (h:∀ i<n, u i=0): u n = L s (u n):= by
   let V:= b.Z.wire d; let f:=ren b.f u; let g:= L s ∘ u;
   have hf : V 0=0:= b.tangent d;
   obtain hT:= congr_fun H n;
   rw [slotFx, slotFx,focuses b h _ le_rfl, Function.comp_apply, show crossW f V n=0 from ( Finset.sum_eq_zero (s:=range (n+1)) fun i hi=> ?_), show crossW V g n=0 from ( Finset.sum_eq_zero (s:=range (n+1)) fun i hi=>?_ ),add_zero,add_zero,add_comm ( b.Z.wire d n ) ] at hT;
   exact add_right_cancel hT
   swap
   · obtain hl:= Nat.lt_succ_iff.mp ( mem_range.mp hi ); unfold f; rw [ focuses b h i hl ]; rcases lt_or_eq_of_le hl with hp|rfl; · rw [ h i hp, zero_lB ];
     rw [Nat.sub_self,hf,zero_rB]
   obtain hl:= Nat.lt_succ_iff.mp ( mem_range.mp hi ); by_cases hp:i=0; subst i; rw [hf,zero_lB ]; unfold g; rw [ Function.comp_apply, h (n-i) (by omega), map_zero,zero_rB ]; -- awkward refine doesn't unfold crossW for hT.
lemma bit_lower (a:Buffer F d)(h:withinBlock F a=0)(hv:a=L 1 a): a=0:= by
    let T:= sameAxis F d; let φ i:= Verne.factor (-1) i; apply follows_right; apply T.ext; intro i; apply T.repr.injective; ext j; let c:= T.coord j (bufferL F a (T i)); change c= T.coord j 0; rw [map_zero]; by_cases he: i.size=j.size; · exact ( diagStrict F _ ).1 h _ _ he
    have hf : c=( ( Verne.factor ( -1 ) j.size:ℂ )*( Verne.factor 1 i.size:ℂ )) * c:= Eq.trans ( congr_arg (fun b:Buffer F d=>T.coord j (bufferL F b (T i))) hv ) ( Verne.reprφ F φ _ _ _ a );
    rw [ ← Complex.ofReal_mul ] at hf; apply by_contradiction; intro hh; 
    -- adjust to explicit inference
    unfold Verne.factor at hf; have he0: 1= Real.exp (-(j.size:ℝ) * -1) * Real.exp (-(i.size:ℝ)*1):= Complex.ofReal_injective (by rw [Complex.ofReal_one ]; exact mul_right_cancel₀ hh (( one_mul c ).trans hf )); rw [ ← Real.exp_add ] at he0; conv_lhs at he0 => rw [ ← Real.exp_zero ]
    obtain hχ := Real.exp_injective he0; have hk: (i.size:ℝ)=(j.size:ℝ):=by norm_num at hχ; linarith
    exact he (by exact_mod_cast hk)
end onlys

-- derivative criterion entails EXACT normalization for required pattern, not just tangent dimension.
lemma solo (H:Month A W D R)(K:Hop F)(hK:K.f=headway)(hP: K.Z.only=1)(T:Month (Hop.act A K) Q D R)(h:Preserves W D)(hQ:Preserves Q D) : K=1:= by
    obtain h1:= link H K T 1; obtain hx:= hop_ident K 1 hK hP ( ( gradingCriterion T ).1 hQ 1 ) ( ( gradingCriterion H ).1 h 1 ) h1; apply Hop.ext hK ( Strat.ext fun i=> ?_ );
    rw [ eZ,zeroed ]; funext n; let f:= K.Z.wire i; let b:= W 1; rw [hx] at h1; obtain he:= congr_arg Hop.Z h1; rw [walkZ,walkZ, Hop.timely,hK,resumeHead ] at he;
    induction n using Nat.strong_induction_on with| h n ih=>
       apply bit_lower (f n) (_:_ ) (stage_fee 1 b ( u:=f ) ?_ ?_);
       · obtain hp:= congr_arg (fun p:Strat F=> p.wire i n) hP; exact hp.trans (congr_fun (zeroed F i) n)
       · obtain hh:= congr_arg ( fun p:Strat F=> p.wire i ) he; change ( resume K.Z b.f*b.Z ).wire i=( b.Z*shift F 1 K.Z ).wire i at hh; rw [pay,pay,resume_wire,Taper.reflectStep ] at hh; exact hh
       · exact ih
-- strict comparison; selected(C) equivalence at ANY eligible Month.Ability.
lemma Subsame {S N:Strat F}(hS:pulse S)(hN:pulse N)(h:S.only=1)(h':N.only=1)(H:Month (A.flip S) W D R)(T:Month (A.flip N) Q D R)(he: Preserves W D)(hx:Preserves Q D): N=S:= by
   let A':= A.flip S; let B:= refresh D S hS; let P:= B*N; obtain ⟨hX,hB,hq⟩:= right_refresh D S hS;
   let g:= flag P ( Strat.pulse.grow B N hX hN ); -- argument bug
   have hK:Hop.act A' g=A.flip N:= by rw [flag_act,Panel.flip_mul ]; unfold P; rw [← mul_assoc,hB,one_mul ]; -- maybe expand A'
   have hP: only B=1:= by have hp:= onlyT (refresh D S hS) S; rw [ h,hq,onek,mul_one ] at hp; exact hp.symm
   have hp:= solo H g rfl ( show only ( B*N )=1 from ( by rw [ onlyT,hP,h',one_mul ] ) ) ( (hK.symm ▸ T) : Month (Hop.act A' g) Q D R ) he hx
   have hx:P=1:= congr_arg Hop.Z hp;
   calc
      N = S*P:=by unfold P; rw [ ← mul_assoc,hB,one_mul ]
      _ = _:=by rw [hx,mul_one ]

-- actually apply in X canonical theorem.
structure Adjusted (C:Panel F)(N:Strat F)(D:(d:ℕ)→ Detector F d){r:ℝ}(R:Booth r F): Prop where
   regular : pulse N
   lower : only N=1
   solves : ∃ U:ℝ→Hop F, Month (Panel.flip C N) U D R ∧ Era.Preserves U D
variable {h:G.Simple}(V:Warehouse G) {O: Land.Booked (wings G)}(M:MS_Data G O){t:ℝ}(T:Booth t V.F)(v:ℝ)(hx:Pic.pass V h M T)
local notation "Xv"=> Pic.X V h M v T
local notation "Sv"=> chooseN V M T v hx
local notation "τ"=> nested V.F h ( BoxOffice.warehouse V )
lemma real_X : Adjusted Xv Sv τ T:= ⟨( focusN V M T v hx ).stable,( focusN V M T v hx ).head, Forge.Cray V h M T v hx, Forge.real_c V h M T v hx, (gradingCriterion (Forge.real_c V h M T v hx)).2 (fun _=> Forge.grade_c ..)⟩
lemma chosen (W:Strat V.F)(H:Adjusted Xv W τ T): W=Sv:= by
    obtain ⟨T,hP,hM⟩:= H.solves; obtain L:= real_X V M (t:=t) _ v hx; obtain ⟨U,Sz,hq⟩:= L.solves
    exact Subsame L.regular H.regular L.lower H.lower Sz hP hq hM
include hx in
lemma criterionX (W:Strat V.F): Selected V Xv W ↔ Adjusted Xv W τ T:= by
   constructor; · intro hC; rw [ Forge.unique_pick (h:=h) V Xv (Pic.innerX (h:=h) ..) hC ( Forge.focusN V M T v hx ) ]; exact real_X ..
   intro h; rw [ chosen V M T v hx W h ]; exact Forge.focusN ..

end YM.FVA2.RadScale.Era

