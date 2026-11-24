import YM.OPE.Compatible.Oasis.Fount
/-!
# One pulse calibration estimate. Upper.H.B only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.CardinalQ
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson
open scoped Topology BigOperators Classical
open Drift Stroke Yolk Pill Spells
open Next.Scheduling Clock
open Lass Lass.Zest Stroke.MatchZ
open Source Labels
variable {G:Gauge}{X E I:Type}{t s z V:ℝ}{k k' l j:ℕ}{T:Stage}
variable {A:Labels.Frame G l}{S:SectionData A}{H₀:Hol G}
open Precision Stationary
set_option quotPrecheck false
variable {v:I→ℝ}{f:Filter I} {K:Votive.Sponsor G}{P:Votive.Seasons K} {a:Axis}{K₀:ChartRatio G}
variable {H:LocalRatio K₀}{L:PriceBook H P} {hs:G.Simple}
open Next.Free FreeResolvent Silt Silt.Float MSbar.Tree MSbar.Tree.Resolvent Cascade Cascade.Paver
variable (N:Foyer L hs a l (k+6)){hz:highStage L hs a N≤ j}{p:Clip}
variable (Y:BankW L hs a N hz p)
local notation "χ"=> Cab P j p
local notation "ZT"=> N.pay.st
local notation "𝓔"=> Dial.BoxQ (dims N)
variable {he:highStage L hs a N ≤ j}
noncomputable def Patron (S:SectionData A)(x:ℝ)(V:Clip): ℕ:= Classical.choose (Demand N S x (he:=he) (p:=V)) -- `he` binder may undecl
variable {f:Filter I}{β:I→ℝ}(hp:Tendsto β f atTop)
variable {U:Hol G}(hV:S.Sound U) (R:Pad G) {n:I→ Side}{J:∀i,Rep G (n i)} {W:∀i,A.Coeff → Coefficient A (n i)}
variable (F:I→Cab P j p)(Q:∀i, Torch S U 0 (J i) (W i) k (salary (β i))) (hT:∀ᶠ i in f,SealK (β i) T S U (n i) (J i) (W i) (Q i))
variable (he':∀ᶠ i in f,Patron N S (β i) p (he:=hz) ≤ (n i).val)(hv: ∀ᶠ i in f, (F i).fees=capL s (β i)) (hh:l < k+6)
local notation "Λ"=>ClockVal N Y
include F he' hp Q hT hv hh hV
set_option maxHeartbeats 200000
lemma areaR (hg:0<t):∀ᶠ i in f, PhotoZ N Y R (β i) t (F i) S (n i) (Q i) :=by
       let A(j):=(F j).ℳ; let z:= N.pay.st.τ 0;
       let X(i):= ClockVal N Y (F i) S R (Q i) (Clock.gap (J i).beta)
       have hx: Wax β f (fun i=> (F i).fees) 0:=((CoinS hp s).pays (carth hp)).congr (hv.mono fun _ hi=>hi.symm)
       have hz' := fun i=> Classical.choose_spec (Demand N S (β i) (he:=hz) (p:=p)) (n i)
       have hq:=ClockFee hp Q (hT.mono fun i hi=>hi.1.TagQ) (hT.mono fun i hi=>hi.2); have hd:∀ᶠ i in f,∀ p∈ Hoard G (4*(Q i).B) (k+6) z,
           ‖boostS (rentV G (F i).ℳ.gear (hazard N hz) K.K (n i)) (1/2) z (k+6) p-boostS (atlasF G (F i).ℳ.gear (hazard N hz) K.K) (1/2) z (k+6) p‖≤ ages (-1) (β i)*‖p‖:= (hT.and he').mono (fun i hi x hx=>hz' i hi.2 (F i) x (hi.1.2.hue ▸ hx))
       obtain ⟨hy,U,hU,hΨ⟩:= eraW N Y _ _ Q _ hq (RateLE.exp (-1) (carth hp)) hp hx hV hh hd; filter_upwards [hy _ hg,hΨ,hU _ hg] with i hi hp hx; exact ⟨hi, U i,hp,hx⟩
open Score
omit F he' hp Q hT hv
include Y
lemma Cork (u:ℝ)(hx:0<u)(s:ℝ)(T:Stage):∀ᶠ x:ℝ in atTop,∃ b:ℕ,∀ (n:Side), b≤ n.val→ ∀ (F:Cab P j p)(P1:Rep G n)(W:A.Coeff → Coefficient A n)(T0:Torch S U 0 P1 W k (salary x)), SealK x T S U n P1 W T0 → F.fees=capL s x→ PhotoZ N Y R x u F S n T0:=by
       let Bad (i:ℝ):=∃ n:Side, Patron N S i p (he:=hz) ≤ n.val ∧ ∃ (f:Cab P j p)(T':Rep G n)(V:A.Coeff → Coefficient A n)(X:Torch S U 0 T' V k (salary i)), SealK i T S U _ T' V X ∧f.fees=capL s i ∧ ¬PhotoZ N Y R i u f S n X
       have h:∀ᶠ i:ℝ in atTop,¬Bad i:=by
              by_contra h; rw[not_eventually] at h; simp only [not_not] at h; choose g hF hg using fun i:ℕ=> frequently_atTop.mp h (i:ℝ); choose Q hQ f P F V' hP H hR using hg; have hp:=areaR N Y (show Tendsto g atTop atTop from tendsto_atTop_mono hF tendsto_natCast_atTop_atTop) hV R f _ (Eventually.of_forall hP) (Eventually.of_forall hQ) (Eventually.of_forall H) hh hx; obtain ⟨j,hh⟩:=hp.exists; exact hR _ hh
       refine h.mono fun i hi=>⟨Patron N S i p (he:=hz),fun n he a b w K he' hv=> ?_⟩; exact not_not.mp fun hm=> hi ⟨n,he,a,b,w,K,he',hv,hm⟩
end YM.OPE.CardinalQ
