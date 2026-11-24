import YM.LocalLTE.Pond.Iris
import YM.LocalLTE.Slide.Athena
import YM.LocalLTE.Tile.Allot
import YM.LocalLTE.Tier.Dais
/-! # Sharp itinerary frequency
All labels common, support ball of E_q leaves specified only at epochs whose radius G design. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.East
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Match
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open Height LocalLTE.Fan Pastel -- namespace edit
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L : Side} {T₀ : Patch} {ℓ k j n: ℕ} {K : Teller G} {s a W U V g C' y A M K₀ r β δ q b v σ t w Λ γ: ℝ} {m : ℕ}
variable {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} (H : Cash W s a L X o U T R) {I: Cash W s a L X o U T R'} {χ : Chi}
local notation "B" => radiusB s
open Scarf Refrain Marlin Opera
variable {ε :ℝ}
variable (P:BudgetPoint)(χ:Chi) (p:ℝ)
-- T U O ASTOCK foreshorteners with defaulter. Ash already separated for true actual books on native labels.
variable (r₁:ℕ→ℕ)(J n:ℕ) -- analytic grade count; k'' tape ℓ stencil
    (k₂:ℕ)
local notation "ℒ"=> East.lectures H J n r₁
local notation "ℐ"=> East.window H (East.lectures H J n r₁) k₂
local notation "ℓ'"=> East.locker H (East.lectures H J n r₁) k₂
-- ASTER model ledgers occupancy, budgets K.almost
open LocalLTE.FrameBox
local notation "r₀"=> stagnate n X.halo*B
-- design axis function determined by SEAT and widened anchor (native). Never depends f.Prove linear across signage changes.Using Orbit.Period.Peels.
open Collection.Price -- edit
variable (κ:ℝ)
lemma seatBorn {I:Cash W s a L X o U T R'} (hp:R.path=R'.path) (he:R.activities.reg=R'.activities.reg)(hk:R.activities.forced=R'.activities.forced) (i:ℕ) : (pennant H i).1=(pennant I i).1:=by
   obtain ⟨u,c,⟨s,v,e1,k1⟩,p,b,t⟩:=R
   obtain ⟨U,C,⟨S,V,e2,k2⟩,P,bh,T₁⟩:=R'; cases hp; cases he; cases hk; rfl

def estuary (t z:ℕ)(ht:t < z)(hx:2 ≤ t) (i:Seat c) (x:RegularAddress c) (hv:x.support=neighbors z x.site) : Price.Art x z := {
    radius:=t
    grove:=by
       let u:= (StepData.sendSites i.1 i.2); let X:= Hall.transplanted i.1 i.2 (cane (u.symm x.site)); exact u.apply_symm_apply x.site ▸ X
    crisp:= hv
    bonus:= ht
    hearth:= hx
    }
lemma atEstuary (t z:ℕ)(ht:t< z)(hx:2 ≤ t) (i:Seat c)(x:RegularAddress c)(hv:x.support=neighbors z x.site)(j:Site c)(hj:x.site=StepData.sendSites i.1 i.2 j): HEq ((East.estuary t z ht hx i x hv).grove) (Hall.transplanted i.1 i.2 (cane j)):= by
   unfold estuary; dsimp only
   let p:= StepData.sendSites i.1 i.2
   have hh : p.symm x.site = j:= p.symm_apply_eq |>.mpr hj; subst j; exact eqRec_heq ..
variable {z t':ℕ}
-- mark using qualification by SUPPORT only. all anchors with huge support skip including EP=0.With live Ω polynomial guarantee.For continuity: forecasts finite despite marking infinite. projection myth of 0 yields 0.A.Ang.
def eyes (n m:ℕ)(hm:n ≥ 2)(ht:m > n) (X:Listing G c)(a:ℕ→Seat c) : Price.Tour X m:= fun i=> if hp: (X.reg i).support= neighbors m (X.reg i).site then .some (East.estuary n m ht hm (a i) (X.reg i) hp) else .none
abbrev dial (i:ℕ):=(Song.pennant H i).1
-- Porch sign
abbrev canvases (Z:ℕ) : Listing G c:= Scarf.diamond (Beam.marquee H P) (East.locker H (East.lectures H J n r₁) k₂) (Z*(radiusB s))
local notation "r'" => East.stagnate n X.halo *radiusB s
include H
lemma broad : 2≤ East.stagnate n X.halo* radiusB s:= by
   have h := Brim.paidB H; have he:Nat.succ 1 ≤ East.stagnate n X.halo:= by unfold East.stagnate East.ratioX; omega
   exact he.trans (Nat.le_mul_of_pos_right _ h)
lemma passport (hp: Reliable G κ t) (z:ℕ) (hz: East.stagnate n X.halo*radiusB s < z*radiusB s)(b m:ℕ) : Portrays (East.canvases H P r₁ J n k₂ z) (z*radiusB s) κ m (East.awardO H χ r₁ J n k₂ m b κ) (East.eyes (East.stagnate n X.halo*radiusB s) _ (East.broad H n) hz _ (East.dial H)):= by
   let Z:=z*radiusB s; let Q:= East.canvases H P r₁ J n k₂ z; let a₀:= East.strand H χ r₁ J n k₂ m b κ
   let v:= East.awardO H χ r₁ J n k₂ m b κ; let L:= East.eyes (East.stagnate n X.halo*radiusB s) Z (East.broad H n) hz Q (East.dial H)
   have he(i:ℕ)(hi:v i≠0): ∃ A: Price.Art (Q.reg i) Z, L i=Option.some A∧ Replicated A.grove A.radius κ (pie m+1) (v i):=by
       let p:=pennant H i; let s':=p.1; let x:= Q.reg i; let K:=p.2
       have he:a₀ K ≠0:=fun h=>hi (by change Rim c • (a₀ K ∘ s'.view)=_; rw [h,show (0:Config G c→ℝ)∘ Seat.view s'=0 from rfl,smul_zero])
       cases h:K with
       | inr q=> rw [h] at he; exact False.elim (he rfl)
       | inl q=>
         have hQ : v i=Rim c • (a₀ (.inl q) ∘ Seat.view s'):= by rw [← h]; rfl
         rw [h] at he
         unfold a₀ strand at he; dsimp only [Sum.elim] at he; split at he
         next hy=>
            let a':= (Beam.dashboard H q).site
            have hB:x= Song.line (leap Z a') s':= by
               have hm: East.page H P r₁ J n k₂ z (.inl q)=leap Z a':=if_pos hy.1
               change East.ledger H P r₁ J n k₂ z i=_; rw [pages]; change Song.line (East.page H P r₁ J n k₂ z K) _=_; rw [h,hm]
            have hX:x.support=neighbors Z x.site:= hB ▸ Scarf.normRange (s:=s') rfl Z -- edit
            have hh: x.site=StepData.sendSites s'.1 s'.2 a':= congr_arg RegularAddress.site hB
            let U:= estuary (East.stagnate n X.halo*radiusB s) Z hz (East.broad H n) s' x hX
            refine ⟨U,dif_pos hX,?_⟩; rw [hQ]
            let t:= East.stagnate n X.halo*radiusB s
            have hr: Replicated (cane a') t κ (pie m+1) (a₀ (.inl q)):=by
               change Replicated _ _ _ _ (if _ then _ else _); rw [if_pos hy]; unfold East.isolated; split
               · refine Price.rp_scale (cane a') _ ?_; exact ⟨_,rfl⟩
               exact Price.rp_zero _
            apply Price.rp_scale
            -- root transported equality
            let x₀:= Lattice.affine s'.1 s'.2 a'; let W':Grove x.site:= by rw [(show x.site=x₀ from hh)]; exact Hall.transplanted _ _ (cane a')
            have hp := Price.translatedPoly s' (cane a') t (show x.site=x₀ from hh) hp hr
            have heq: HEq U.grove (Hall.transplanted s'.1 s'.2 (cane a')):= East.atEstuary t Z hz _ _ x hX a' hh
            have he': U.grove= W':= eq_of_heq (heq.trans (?_)); swap
            · exact HEq.symm (cast_heq ..) -- edit
            rw [he']; exact hp
         next hy=> exact False.elim (he rfl)
   refine ⟨fun i hi=>not_not.mp fun hx=>by obtain ⟨A,h,hx⟩:= he i hx; exact absurd h (by rw [show L i=none from hi]; simp),fun i A h=> ?_⟩; by_cases hu : v i≠0
   · obtain ⟨V,hv,hX⟩:= he i hu; exact Option.some.inj (hv.symm.trans h) ▸ hX
   rw [show East.awardO _ _ _ _ _ _ _ _ _ _=0 from not_not.mp hu]; exact Price.rp_zero _
end YM.PhysicalNext.Repeat.East
