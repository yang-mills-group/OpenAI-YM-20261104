import YM.Qlocal.Scale
/-! Extra lease on any prescribed height with no rank limit
 at the step height. Recover factors and estimate at ANY location. K remains
 flat beyond needed power even after undoing prescribed product costs (H k
 can be chosen/lifetime to cover those). Invoke with ζ when accumulating on
 close intervals.Estimate local asserts real and growth T.Back.S.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Scale
open Filter Function Set Lattice Wilson RG Pressure Tree Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open PhysicalNext PhysicalNext.Repeat AnalyticBridge VerifiedReset Extra.Iteration Song
open Collection Quotes Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Roost
open RGComparison01 RGComparison01.Pledge RGComparison01.Pledge.Holdings
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge}{m n p : ℕ}{M : Metals G} {D:Rolls M.p}{u t ζ b: ℝ}{L:Side}
open Clock Instrument
open Leasing Schedule
section earning
variable {s:Sheet G}{K:MapPrices}{C: Targets s K}{D:Rolls s}(E:Expenses C)
    {t:ℕ→ℝ}{w:Return.Wages}(Y:PhysicalNext.Repeat.Register D E w t) {F:ℕ→ℕ→Postage}(S:Time.Scouts (F:=F))
    {P:Protection D}

def blade (S:Stage) (L:Side):= (L.val:ℝ)^4*Real.exp (S.supportExponent*Footprint.preCost 0)
lemma bladeCap(S:Stage)(L:Side): 0 ≤ blade S L:=by unfold blade; positivity
/-- constant post-L plus Geo height for any µ; spend BEFORE selecting occupants. -/
def surf (L:Side) (B₀:Holdings.Bauble G L) (S:Stage)(x:ℝ) := 1+blade S L + |B₀.roi x|+4*|B₀.invZ x|
lemma surfing (L: Side)(B₀:Holdings.Bauble G L)(S:Stage): Geo G L (surf L B₀ S) := ((Geo.fixed (1+blade S L)).joins (Geo.mean B₀.revenue)).joins ((Geo.fixed 4).times (Geo.mean B₀.positive))
variable (η:ℕ→ℝ)(H T:ℕ→ℕ)
namespace Lease
local notation "ℬ"=>Bauble
structure Harbor (m k k' j:ℕ)(h:4 ≤ j) (x:ℝ)(B:Bauble G (D.L j)):Prop where
 juvenile : Juvenile E Y S m j h B k k' (η j) x
 amplitude : surf (D.L j) B (s.profile m) x≤drawer (betaF G x (D.L j))
 quoteP : let y := betaF G x (D.L j)
          ∀ β,inBand y β→ Real.exp (-Payments.Pairing.kGoal (F j m) y β) ≤ Instrument.plain.w x*y^(-((T j:ℕ):ℝ))

lemma chooses (_u:Delays P){m j h:ℕ}(hi:StepStages j m)(hh:4≤j)(hP:Pocket Y S)
    (ht: ∀ i j,StepStages j i → qualify E i j (D.L j).val)(hz:∀ i,0 < η i) :∃ k' B,∀ᶠ x in atTop, Harbor E Y S η T m h k' j hh x B:= by
 obtain ⟨l,B₀,h₀⟩:= negotiable E Y S ht η hz m j hh hP hi h; refine ⟨l,B₀,?_⟩
 filter_upwards [h₀,saves (D.L j) _ (surfing _ B₀ _), after_bill G (F j m) (-((T j:ℕ):ℝ)) (D.L j)] with x hx hv hy; exact ⟨hx,(le_abs_self _).trans hv, hy⟩

structure Dials (V:Delays P) : Prop where
 pays (i j:ℕ)(he:StepStages j i)(h:4≤j) (k:ℕ) : k ≤ H j → ∃ k' B,∀ x≥ V.betaEntry j, Harbor E Y S η T i k k' j h x B
-- combine monot future.
lemma promotes (hp:Pocket Y S)(ht:∀ i j,StepStages j i → qualify E i j (D.L j).val)(hz:∀ i,0 < η i) (V:Delays P) : ∃ W: Delays P,DelayLe V W ∧ ∀ V', DelayLe W V' → Dials E Y S η H T V':= by
 let p v j i:=∀ h:4≤j,∀ k≤ H j,∃ k' B,∀ x≥v,Harbor E Y S η T i k k' j h x B
 have he j i (hx:StepStages j i): ∀ᶠ x in atTop,p x j i:= by
    by_cases h₁:4≤j; swap; · exact Eventually.of_forall fun x h=> (h₁ h).elim
    have h(k:ℕ): ∀ᶠ x in atTop,∃ k' B,∀ y≥ x,Harbor E Y S η T i k k' j h₁ y B:= by
       obtain ⟨k',B,h⟩:= Lease.chooses E Y S η T V (h:=k) hx h₁ hp ht hz; obtain ⟨z,hZ⟩:= eventually_atTop.mp h; exact (eventually_ge_atTop z).mono fun t ht=> ⟨k',B,fun i hi=> hZ _ (ht.trans hi)⟩
    filter_upwards [(eventually_all_finset (I:=Finset.range (H j+1))).2 (fun k hk=> h k)] with i hx; exact fun _ k hk=>hx k (mem_range.mpr (by omega))
 obtain ⟨x,-,hx,hy⟩:= collect_upper V.betaEntry _ (fun j=> eventually_transitions j _ _ (he j))
 exact ⟨{V with betaEntry:=x}, ⟨hx,le_rfl,le_rfl,le_rfl⟩,fun _ h=>⟨fun i j h₁ hf k hk=> hy _ _ (h.beta j) i h₁ hf k hk⟩⟩
end Lease

def era : Goal G:= fun _ _ A F=> Lease.Dials F.expense F.shape F.scout η H T A.delay -- fix
open ThroughLaunch
lemma widely (he:∀ i,0 < η i): Obtainable (era (G:=G) η H T):= by
 intro s K C z R E ht; obtain ⟨j,hJ⟩:=Leasing.clearance E; exact ⟨j, fun l hl D w u Z F S hκ p hϑ P Q V=> by
    obtain ⟨W,hW,hP⟩:= Lease.promotes (s:=ThroughLaunch.raise s l) E Z S η H T hκ (fun i j' hp=> hJ i j' hp _ ((hl j').trans (D.large j').need)) he V
    exact ⟨W,hW,fun Y hy C₀ K I p B hv hm _ _ _ _ _ _ _ hx_ ht_ hw' hy_=>hP Y hy⟩⟩
end earning
section receipt
variable {A: Alloy M D} (F:Factor A){η:ℕ→ℝ}{H T:ℕ→ℕ}(Y:era η H T M D A F)
local notation "J"=> A.B.a.clock.J (m+1)
local notation "I"=> A.B.a.clock.J m
local notation "a"=> A.B.a
local notation "L'"=>D.L (A.B.a.clock.J (m+1))
local notation "x₀"=> A.B.a.clock.hatBeta m
include Y
namespace Lease
variable {l k :ℕ}
structure Coupon (k k':ℕ) (B:Bauble G (D.L (A.B.a.clock.J (m+1)))) : Prop where
 spring : ∀ x≥ A.delay.betaEntry (A.B.a.clock.J (m+1)),Lease.Harbor F.expense F.shape F.scout η T (A.B.a.clock.J m) k k' (A.B.a.clock.J (m+1)) (A.B.a.clock.adm (m+1)) x B
lemma available (k:ℕ)(hi:k≤H J) : ∃ (l:ℕ) (B:Bauble G (D.L J)), Coupon F (η:=η) (T:=T) k l B:= by obtain ⟨l,B,h⟩:=(show Dials F.expense F.shape F.scout η H T A.delay from Y).pays _ _ (step_paid A.B.a m) (A.B.a.clock.adm _) k hi; exact ⟨l,B,⟨h⟩⟩
omit Y
variable (η T) (B:Bauble G (D.L (A.B.a.clock.J (m+1))))(hB: Coupon F (η:=η) (T:=T) k l B)
include hB
set_option quotPrecheck false
local notation "p₀"=> (a).budget m
set_option quotPrecheck false
local notation "u★" => surf L' B (M.p.profile I) x₀
local notation "Φ"=> (a).clock.hatBeta (m+1)
open Shoot
lemma actual : Opened F η k l m B ∧ 0<B.mass x₀ ∧
     (1≤u★ ∧ u★ ≤ drawer Φ ∧ (∀ β,β∈ band (a) (m+1)→ Time.quoteHard (a) m F.book β≤ (a).clock.forcedAllowance m * Φ^ (-((T J:ℕ):ℝ)))) ∧
     4*(u★)⁻¹ ≤ B.mass x₀ ∧
     (∀ p:ℕ,B.roi x₀+StageArt.cost ((a).clock.op m p) (p₀).supportExponent ≤ u★):= by -- syntax
 have ht i hi: Juvenile F.expense F.shape F.scout _ _ (A.B.a.clock.adm _) B k l (η J) i:= (hB.spring i hi).juvenile
 let W:= hB.spring x₀ (A.B.valid.pays m); have he:= ht x₀ (A.B.valid.pays m); have h1:= he.permission; have hq:0 < B.mass x₀:= h1.crucial; have hV:B.invZ x₀=(B.mass x₀)⁻¹:= h1.shores
 let A':= blade (M.p.profile I) L'; let b':= B.mass x₀; have hb':=inv_pos.mpr hq; have hP': 0≤ A':=bladeCap ..; let v:= u★; have hv : v=1+A' + |B.roi x₀|+4*b'⁻¹:=by unfold v surf; rw [hV, abs_of_pos hb']
 have hp: Φ=betaF G x₀ L':=PriceCompiler.beta_eq A.B.valid m
 have hv' : 1≤ v:=by rw [hv]; unfold b'; linarith [abs_nonneg (B.roi x₀)]
 refine ⟨⟨ht⟩,hq,⟨hv',W.amplitude.trans_eq (congr_arg drawer hp.symm), fun β he=>?_⟩,?_, fun p=>?_⟩
 · have hz:=W.quoteP β (hp ▸ trial_in he); unfold Time.quoteHard; rw [hp,Deployment.clock_eqns (a).clock m |>.2.2.2.2.1]; exact hz
 · change 4*v⁻¹≤_; rw [← div_eq_mul_inv]; rw [div_le_iff₀ (zero_lt_one.trans_le hv')]
   unfold b' at hv; rw [hv]; have hp:= mul_inv_cancel₀ hq.ne'; nlinarith [abs_nonneg (B.roi x₀)] -- expensive break
 change _ ≤ v
 let P:= M.p.profile I
 rw [hv]; refine le_trans (b:= |B.roi x₀|+A') (add_le_add (le_abs_self _) (le_of_eq (?_))) ?_ -- parentheses maybe
 · unfold A' blade StageArt.cost; rw [show ((a).clock.op m p).ratio.count=L' from PriceCompiler.block_eq A.B.valid m, show (p₀).supportExponent= P.supportExponent from congr_arg Stage.supportExponent (params_eq A.B.valid m)]
 unfold b'; linarith
end Lease
end receipt
end YM.Qlocal.Scale
