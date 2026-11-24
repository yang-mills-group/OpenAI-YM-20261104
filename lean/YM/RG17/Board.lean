import YM.RG17.Decode

/-!
# Panel from true two-point correlations

Left inverse's polynomial coupling costs APPLY on the reporting
columns; error on physical unit norm generally only takes MUCH sharper
spatial powers. Bound inverse of moving frame in physical units by coarse
rates, sufficient on spatial errors from signed correlation readouts.
No assumption on a physical free leading *comparison*; lower monitor
on independently computed zeroth Gram port required (next file).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter MeasureTheory Spec Extraction Table OPE OPE.Orbits
open OPE.Nesting
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    {F:Final C f S} (L:Layout F)
    (P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (H:Services C f S) {n:ℕ}{d:Fin n→ℕ}
set_option quotPrecheck false
local notation "ρ"=>OPE.run
local notation "v₀"=>voices (vacTags S)
local notation "y₀"=>OPE.Short.gapPos

lemma moment_cont (view:Viewers F) (v:Labels S d) (r:ℝ)(hr:0<r) {x:Points n}(hx:x∈conf n):ContinuousAt (fun x:Points n=> Orbits.moment (spectator F view) (posed r x) v) x := by
   have hd:Injective (beside (posed r x) y₀):= beside_distinct.mpr ⟨posed_on hx hr,injective_of_subsingleton _,fun _ j=> nomatch j⟩
   apply ContinuousAt.congr ((whole_cont_at v v₀ (spectator F view) (spectate F view) hd).comp (f:=fun x:Points n=> ⟨posed r x,0,y₀⟩) (((posed_continuous r).prodMk continuous_const).continuousAt))
   filter_upwards [(conf_open _).mem_nhds hx] with z hz
   exact OPE.Short.tagged F (tags v) (posed r z) view (posed_on hz hr)
lemma main_int (v:Labels S d)(view:Viewers F){r:ℝ}(hr:0<r) (X:Test n)(hx:tsupport X⊆conf n):
    Integrable (fun x=> X x * Orbits.moment (spectator F view) (posed r x) v):=localized X _ (fun _ h=> moment_cont view v r hr (hx h))

include H P
lemma allMoments {v:ℝ→ Labels S d}{c:Fin n→ℝ}(hp:GradePrice P d v c) {K:Set (Points n)}(hk:IsCompact K)(hx:K⊆conf n) {q:ℝ}(he:(∑ i,c i)<q) :
    ∀ᶠ r in home, ∀ x∈K, ∀ u:Viewers F, ‖Orbits.moment (spectator F u) (posed r x) (v r)‖≤ Real.exp (q*ρ r):=by
   obtain ⟨M,η,hM,hη,hx'⟩:= roomCosts hk hx
   let p (r:ℝ)(w:Points n × Viewers F):=Orbits.moment (spectator F w.2) (posed r w.1) (v r)
   have hz: ∀ᶠ r in home,∀ w:Points n × Viewers F,w.1∈K→ ‖p r w‖ ≤ Real.exp (q*ρ r):=by
       apply refine_geometry; intro u l hl ht h
       let P' (r:ℝ)(e:Fin n→ℕ):= Orbits.moment (S:=S) (spectator F (u r).2) (posed r (u r).1) (d:=e)
       have hy:= positiveLength.filter_mono ht
       have hc:= ageLarge.mono_left ht
       have hf'' (e:Fin n→ℕ) (hle:e≤d):∀ᶠ r in l,∀ z:Labels S e,P' r e z= P' r d (fun i=>F.sector.derivatives.rise (hle i) (z i)):=
          (h.and hy).mono (fun r hh z=> OPE.Levy.inclusionMoment F _ _ hle z _ _ (posed_on (hx hh.1) hh.2))
       have hx'' (e:Fin n→ℕ)(_:e≤d)(z:Labels S e):RateLE l ρ (fun r=> P' r e z) (weight e+0):=by
          intro a ha; obtain ⟨δ,hδ,Hδ⟩:= exists_between ha
          let ε:=δ-weight e; have hε:0<ε:=by linarith
          have hz := raw_price F H z v₀ hM hη (δ:=1) zero_lt_one hε
          filter_upwards [h, hy, hz.filter_mono ht, (((lengthRate.rpow (-weight e-ε)).pays ageLarge) a (by dsimp only [ε]; linarith only [Hδ])).filter_mono ht] with r hr ht hv hX
          let x := (u r).1; let w:Loc (Fin n) Empty := (posed r x,0,y₀)
          have hw: w∈ FitsOn (Fin n) Empty M η 1 r:= ⟨hx' r ht x hr,⟨fun i=>i.elim,fun i=> i.elim⟩⟩
          specialize hv w hw (u r).2; rw [Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)] at hX
          rw [show P' r e z=whole (spectator F (u r).2) w.1 z y₀ v₀ from (OPE.Short.tagged F (tags z) w.1 _ (posed_on (hx hr) ht)).symm]; exact hv.trans hX
       exact ⟨l,hl,le_rfl,(cardinalityCharged P ht hp 0 P' hf'' hx'') q (by linarith only [he])⟩
   exact hz.mono (fun r hr x hx u=>hr (x,u) hx)
lemma costOfMoment {v:ℝ→ Labels S d}{c:Fin n→ℝ}(hp:GradePrice P d v c)(u:ℝ→ Viewers F) (ψ:Test n)(hs:tsupport ψ⊆conf n):RateLE home ρ (fun r=> measured F (v r) r (u r) ψ) (∑ i,c i):=by
   intro e he; obtain ⟨q,hq,hp'⟩:= exists_between he; let f:=∫ x:Points n,‖ψ x‖; let a(r):= Real.exp (q*ρ r)
   have h':RateLE home ρ (fun r=> a r*f) (q+0):= (RateLE.exp q ageLarge).mul (RateLE.const f ageLarge)
   filter_upwards [allMoments P H hp ψ.hasCompactSupport hs hq,h' e (by linarith only [hp'])] with r h hh
   apply le_trans ?_ ((Real.le_norm_self _).trans hh)
   change ‖∫ x:Points n,ψ x * _‖≤ _
   refine (norm_integral_le_of_norm_le (g:=fun x:Points n=> a r* ‖ψ x‖) ((ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).norm.const_mul (a r)) ?_).trans_eq (integral_const_mul ..)
   filter_upwards with x; by_cases hE:x∈tsupport ψ
   · rw [norm_mul,mul_comm ‖ψ x‖]; exact mul_le_mul_of_nonneg_right (h x hE _) (norm_nonneg _)
   rw [image_eq_zero_of_notMem_tsupport hE]; simp

omit H P
section duet
variable {D:ℕ}
-- fixed-cost test list in normalized shape geometry.
structure Stud (C:Family G)(D:ℕ) where
    weight : Free C D
    test : Test 2
    fits : tsupport test⊆ conf 2

def Stud.twins (T:Stud C D)(v:Slot C D) : Fin 2→ Slot C D:= ![v,.inr T.weight]
abbrev pair (T:Stud C D)(x:S.Field D)(r:ℝ) : Labels S (fun _:Fin 2=> D):= ![x,L.frame D r T.weight]

variable (T:Stud C D) (r:ℝ)
private def boardValid (hr:0<r) : S.Field D→ₗ[ℂ]ℂ where
    toFun x:= measured F (pair L T x r) r none T.test
    map_add' x y := by
       have e(v:S.Field D):pair L T v r= update (β:=fun _=> S.Field D) (pair L T x r) (0:Fin 2) v:=funext fun i=>by fin_cases i <;> simp [pair]
       unfold measured Test.applyTo
       rw [← MeasureTheory.integral_add (main_int (pair L T x r) (F:=F) none hr _ T.fits) (main_int (pair L T y r) (F:=F) none hr _ T.fits)]
       apply integral_congr_ae; filter_upwards with a
       have hv(z:S.Field D):= congr_arg (Orbits.moment (S:=S) S (posed r a) (d:=fun _:Fin 2=>D)) (e z)
       change T.test a*Orbits.moment S _ (pair L T (x+y) r) = T.test a*Orbits.moment S _ _ + T.test a*Orbits.moment S _ (pair L T y r)
       rw [hv (x+y),MultilinearMap.map_update_add, mul_add, ← hv x, ← hv y]
    map_smul' c x := by
       let M(a:Points 2):= Orbits.moment (S:=S) S (posed r a) (d:=fun _:Fin 2=>D)
       have e(v:S.Field D):pair L T v r= update (β:=fun _=> S.Field D) (pair L T x r) (0:Fin 2) v:=funext fun i=>by fin_cases i <;> simp [pair]
       change (∫ a:Points 2,T.test a * M a (pair L T (c•x) r))= c*(∫ a:Points 2,T.test a*M a (pair L T x r))
       rw [← MeasureTheory.integral_const_mul]; apply integral_congr_ae; filter_upwards with a
       rw [e (c•x),MultilinearMap.map_update_smul,← e x]; ring -- smul

def board : S.Field D→L[ℂ]ℂ:= if hr:0<r then LinearMap.toContinuousLinearMap (boardValid L T r hr) else 0
lemma board_apply (hr:0<r)(x:S.Field D):board L T r x = measured F (pair L T x r) r none T.test :=by rw [board,dif_pos hr]; rfl

def panel (T:Stud C D)(r:ℝ) : Free C D→L[ℂ]ℂ:= (board L T r).comp (L.frame D r).toContinuousLinearEquiv.toContinuousLinearMap
lemma seated {v:Slot C D}: pair L T (input L r D v) r= stems L (T.twins v) r:=by funext i; fin_cases i <;> rfl
include H P
lemma rawBoard (hL:Located L)(v:S.Field D) :RateLE home ρ (fun r=> board L T r v) D := by
    let c: Fin 2→ℝ:= ![(D:ℝ),0]
    have he:GradePrice P (fun _:Fin 2=>D) (fun r=>pair L T v r) c:=by
        intro i j; fin_cases i
        · change RateLE home ρ (fun _=> P.cutTest j D v) _
          by_cases hx:D<j
          · simpa only [P.kills_lower _ _ hx] using! RateLE.zero home ρ _ (X:= S.Field j)
          apply (RateLE.const _ ageLarge).mono; change 0≤ -(j:ℝ)+D; have hh:j ≤ D:= Nat.le_of_not_gt hx; have hz: (j:ℝ) ≤ D:=Nat.cast_le.mpr hh; linarith
        change RateLE home ρ (fun r=>P.cutTest j D (input L r D (.inr T.weight))) (-(j:ℝ)+0)
        rw [add_zero]; exact inputUpper P L H hL _ _ _
    have hx:= costOfMoment P H he (fun _=> none) T.test T.fits
    rw [Fin.sum_univ_two,show c 0+c 1= (D:ℝ)+0 from rfl, add_zero] at hx; exact hx.congr (positiveLength.mono fun r hr=> (board_apply _ _ r hr v).symm)
end duet
end YM.RG17
