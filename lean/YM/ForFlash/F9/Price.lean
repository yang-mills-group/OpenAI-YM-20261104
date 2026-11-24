import YM.ForFlash.F9.Seat
import YM.SignedWilsonExpansion.Purchase.Cadet
/-! # In the estimator clock, **before** boot orientation, F9 bulk terminal -> helper -> polynomial.
    As in GUIDE-SIGNED part III. Follows the indicated proofs with the extra geometry
    and price information of Room (for the "preQuote") and Seat / formal-regulator payment.
    Retains the very same canonical series and actual history budgets. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section

/- Derived from YM/SignedWilsonExpansion/F9/EvaluateQ.lean -/
namespace YM.SignedWilsonExpansion.Commission.TollQ
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Asymptotics
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open FVA2 FVA2.Arrival FVA2.Main FVA2.Scale FVA2.Position FVA2.Position.Axes
open scoped Topology ContDiff BigOperators Classical
open Lattice RG WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa WilsonCoeffUV.Mer.Xa.MarqueQ PorchK
open Method Epic MergeTrip MarqueQ.Crops Crops.Taught
open Source Gauge WardBin Wilson
variable {G:Gauge}{n d h u e k :ℕ}{ι:Type} {L:Filter ι}
variable {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{P' : Prescription (Press.portDeck G)}
variable {W':Initialize G}{V':Normalize.Store G}(K:Rose.Pick V') (M':Speed.Quoted W' K T P')
variable {V:∀ h,Rays G h W'.hol}{F:Labels.Frames G}{Ω:Council F}{E:Credit} {R:Realm G (e+1) E}
variable {VQ:Set (Points (n+1))}
variable (q:ι→ PorchK W' F V Ω R h k u)(pn:ι→Sample (n+1))(p:ι→Stage (n+1))(W0:ι→ℕ→Fin (n+1)→ Cover)(N:ι→ℕ)
variable {Y θ μ ν ε Uw:ι→ℝ}
variable (hQ:SeatsForFlash L pn p)
variable (KQ: FrontQ q L Y θ μ ν) (pτ:ι→ ℝ) (pt: TimeQ L θ pτ)(w:∀ᶠ i in L,0< θ i)
variable (St:∀ i≤e, Across L Y ℂ (fun j=>(q j).toEpic.tenor W' V' i))(U':RateQ.Costy L Y (fun i=>(q i).toEpic.voice W' K) e)
variable {τ₀: Hol G}{d':Fin (n+1)→ℕ} (S:∀ i:Fin (n+1),SectionData (F.level (d' i))) (pS:∀ i,(S i).Sound τ₀)(hS:∀ i,Bid.pop (S i))(h₀:∀ i,d' i≤h)(Z':ι→ (i:Fin (n+1))→(F.level (d' i)).Coeff) (tZ:∀ i,SizeW L μ (F.level (d' i)) (fun j=> Z' j i))
local notation "Tᵥ"=> Measure.start W' K h
variable {U1 U2 V0:Credit} (hp: Dormitory R ((n+1)*k) 0 U1)(hp': Dormitory R k u U2)(hϑ:SpringD R ((n+1)*k) 0 u V0){δ:ℝ}
variable (pF:PoseW δ q pn W0 L Uw N)(sale: Cheap q n L μ Uw ε)
variable (reg: Wage L μ ε (Speed.chip ∘ grab ∘ pn))
include KQ M' pτ pt w hQ St U' pS hS h₀ tZ reg
lemma estimateForFlash : charge e L μ ((fareU q d') * ε) ( fun i=> pupils q V' K d' S Z' pn i- trialU K q p S Z' i):=by
     let B(i:Fin (n+1))(j):=(q j).billSize (d' i); let A(i s):= account V' (q i) (S s) (Z' i s); let X(i):= (q i).χ V' K; rw [payFare]; refine warp_margin KQ.inside_ B (Z:=X) (fun i=> (q i).Kconst ..) (τfit q V' K U' KQ w pτ pt) (T:=fun i=>numeral W' K (pn i) h) (S:=view (W':=W') K p) (?_) (a:= fun i j w'=> account_full q V' (Z:=fun j=> Z' j i) (pS i) (hS i) (h₀ i) KQ St (tZ i) j w')
     intro a k hk; simp only [map_sub,Tape.archive, coeff_mk]; refine Wage.rel reg ( ?_ ); exact ( TollQ.priceForFlash R.hG W' K T P' 0 M' pn p hQ a k ).1
include hp hp' hϑ pF sale
lemma earnedForFlash : charge e L μ ((fareU q d') * ε) ( fun i=> trialU K q p S Z' i-staffing q d' S Z' N W0 i):=by
     rcases isEmpty_or_nonempty ι with h|e'; · exact fun i _=> Wage.enroll (IsBigO.of_bound' (Eventually.of_forall fun i=> isEmptyElim i))
     have vR:h ≤ k:= ((q ( Classical.choice e')).canv.reserve W'.hol).order
     choose C c using fun i:Fin (n+1)=>pupilPrice (iℓ:=Unit) (e:=e) (u:=u) (S i) (pS i) (hS i) ( (h₀ i).trans vR )
     have hv:= MarqueQ.PorchK.earning q V' K KQ d' S C Z' tZ N pn W0 U1 hp U2 hp' V0 hϑ pF sale c
     -- parameters explicitly if not ...
     have ht:= estimateForFlash K M' q pn p hQ KQ pτ pt w St U' S pS hS h₀ Z' tZ reg
     intro i p'; exact Wage.fix (Wage.minus KQ.inside_ (hv i p') (ht i p')) (Eventually.of_forall fun i=> by dsimp only; simp only [map_sub]; abel) (.refl ..)
omit hp hp' hϑ pF sale reg
lemma looksForFlash (ℓ:ℕ)(p₀:ℓ≤e):
    let t(i:ι):= (pτ i:ℂ); let V(i:ι):=(q i).earns0 V' K ℓ (pτ i); Taught L μ θ (fareU q d') t ℓ (trialU K q p S Z') (fun i=> invoke (view (W':=W') K p i) ℓ (V i) (fun j=> citeS ℓ (t i) (account V' (q i) (S j) (Z' i j)))):=by
     intro t V; rw [payFare]; refine Taught.manifests KQ.inside_ (smallG q KQ) _ (TimeN w pτ pt) (view (W':=W') K p) (fun i x=>(q x).billSize (d' i)) _ (setting q V' K U' KQ w pτ pt ℓ p₀) (fun i=> (q i).Kconst ..) ?_ (fun i j v=> account_full q _ (pS i) (hS i) (h₀ i) KQ St (Z:=fun j=> Z' j i) (tZ i) j (v.trans p₀))
     intro a k p; simp_rw [Tape.archive, coeff_mk]; exact Wage.enroll ( TollQ.priceForFlash R.hG W' K T P' 0 M' pn _ hQ a k ).2
-- Output cash for q ∈ simultaneous grants. At least M fixed requested p', permit ζ.Size.Can be chosen pure.T
include hp hp' hϑ pF sale reg
-- crop e = the max offered (p₀ denotes uptake varying later). evaluate any later crop k' at pτ in comparison.H!
variable (εp: Wage L μ 1 ε)
include εp
lemma survivingForFlash (p' p'' A:ℕ)(h0:p' ≤ p'')(he:p'' ≤ e)
       (wT:∀ d:ℕ,(fun i=> μ i^d * (fareU q d' i * ε i))=o[L] (θ^A))(v':∀ d:ℕ,(fun i=> μ i^d*(fareU q d' i*θ i^(p'+1)))=o[L] (θ^A)) :
       (fun i=> Pointer (d:=p'') q W0 N pτ S Z' i - invoke (view (W':=W') K p i) p' ((q i).earns0 V' K p' (pτ i)) (fun j=> citeS p' (pτ i) (account V' (q i) (S j) (Z' i j))))=o[L] (θ^A):=by
     let A₀(i):=trialU K q p S Z' i; let K₀(i):=staffing q d' S Z' N W0 i; let θ'(i):=(pτ i:ℂ); have vK:= (looksForFlash K M' q pn p hQ KQ pτ pt w St U' S pS hS h₀ Z' tZ e le_rfl).price; have hx:= earnedForFlash K M' q pn p W0 N hQ KQ pτ pt w St U' S pS hS h₀ Z' tZ hp hp' hϑ pF sale reg; let B:= clockQ.chooseOne KQ.inside_ (smallG q KQ) θ' (TimeN w pτ pt) (fun i=> A₀ i-K₀ i) hx p'' he; have ht:= looksForFlash K M' q pn p hQ KQ pτ pt w St U' S pS hS h₀ Z' tZ p' (h0.trans he); have hv:= clockQ.dropFee KQ.inside_ (smallG q KQ) θ' ( TimeN w pτ pt ) A₀ vK p' p'' h0 he; have hp:= Wage.spend ht.bill v'; refine ((IsLittleO.sub (( Wage.spend hv v' ).sub (Wage.spend B wT)) hp )).congr_left (fun i=>?_); simp only [map_sub]; unfold Pointer θ'; unfold A₀ K₀; abel
end YM.SignedWilsonExpansion.Commission.TollQ

/- Derived from YM/SignedWilsonExpansion/Purchase/Cadet.lean -/
namespace YM.SignedWilsonExpansion.Purchases.HalfRoof.Cooking
open Wilson Gauge RG Asymptotics Lattice Set Filter Function Real Next.Rank Perch Commission WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa UVClock Schedules Metric Laurent
open XSpace XSpace.Cirrus XSpace.Expense Ticket Cosmos Cosmos.Polestar Source MarqueQ Method Stair FVA2 FVA2.Scale
open Minty WardBin FVA2.Arrival FVA2.Main FVA2.Position FVA2.Position.Axes
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology Classical BigOperators
variable {G:Gauge}{S:Schedule}{M:Levels G}{e n h d k u K:ℕ}{T:Initialize G}{ι J:Type}
variable {l c m b v z r N:ι→ℕ}{A Y U B ρ:ι→ℝ}{L:Filter ι}{Ñ:Precision.ChartRatio G}
variable {W':ℕ} {X:Hol G}{F:Labels.Frames G}{Ω:Council F}{Wn:Normalize.Store G}
variable (R:Realm G (e+1) Credit.leanC) (p₁:∀ i,(Ω i).Sound X)(p₂:∀ i,Bid.pop (Ω i)) (P:Install X (Master.mk F.level Ω p₁ p₂) R K)
variable (Kn:Rose.Pick Wn){S':MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {T':Prescription (Press.portDeck G)} (M':FVA2.Speed.Quoted T Kn S' T')
variable (Q:∀ h,Rays G h T.hol) {p_ q' A':ℕ}
variable (p:∀ i,0<ρ i)(Z:ι→ PorchK T F Q Ω R h k u)(H':BarrelP U L Q F Ω e k h u R l m b v c r Y B p Z)
open Epic TollQ
-- Lantern exists for any realized horizon.Cam harvest. Height can choose large.
variable (ha:h≤k)(V:6≤h)(hk:k+e ≤ K)(pV:u≤ K)
variable {α:Axis}(vZ: (bankSize G T Kn M' R.hG α h V)*h ≤ u) (hZ:(bankSize G T Kn M' R.hG α h V)*k ≤ K)
include P H'
include ha V pV vZ hZ hk
-- curvature of receipt approximation + Jacobian.K.Adv. Reader.Clock.T. Crop.A ledger fee.
open Minty PorchK MarqueQ.Crops MarqueQ.Crops.Taught
variable {C₀:ℝ} (A₀: Angles e R h u ρ l b v r c L B C₀)(pD: Wage L ( dollar B ) ( payD B (-C₀)) (FVA2.Speed.chip ∘ fun i=> ( roof R.draws (l i) (c i) (ρ i) (p i))))
variable {Δ : Fin (n+1)→ℕ}{VQ:Set (Points (n+1))}{z':Fin (n+1)→ℕ}
variable (Cϑ:0≤C₀)(x:ι→Fin (n+1)→ Cover)(Q':ι→(i:Fin (n+1))→(F.level (Δ i)).Coeff)
local notation "S•"=> (mark B)
local notation "§"=> (picture l c b x R.draws p)
include P
variable (t:(n+1)*k≤K)(h0:(n+1)*h≤u)(d₀:∀ i,Δ i≤ h)(d₂: RoomForFlash R L B l c ρ p T Q F h k)(d': MovesIn L B (fun i=> Garden ( hereD R.draws ρ b i ) (x i)))(w0:c≤ᶠ[L] N)(y:ι→ Stage (n+1))(j0:∀ᶠ i in L,(y i).val= Garden ( hereD R.draws ρ b i ) (x i))(B_:∀ i:Fin (n+1), PorchK.SizeW L ( dollar B ) ( F.level (Δ i) ) (fun j=> Q' j i))
include t h0 d₀ d₂ d' w0 j0 B_ Cϑ A₀ pD
lemma surfeitForFlash (β:ℝ)(z:0<β)(iG:payD B (-β) ≤ᶠ[L] hereD R.draws ρ v)(D:ℕ)(u_: (∑ i,Δ i)≤ D)(pW:p_ ≤ q')(hp:q'≤e)(j1:D*β+-C₀< A'*(-1/2:ℝ))(j2:D*β+(p_+1:ℝ)*(-1/2)<A'*(-1/2)) (t₁:ι→ℝ)(clock: TimeQ L (mark B) t₁) :
    (fun i=> Pointer (d:=q') Z (shapeO b x R.draws) N t₁ (fun i=> Ω (Δ i)) Q' i - invoke (view (W':=T) Kn y i) p_ ((Z i).earns0 Wn Kn p_ (t₁ i)) (fun j=> citeS p_ (t₁ i) (account Wn (Z i) (Ω (Δ j)) (Q' i j))))=o[L] ((mark B)^A'):=by
    let hp0:= H'.timeRise; let v_:= rentShape R p₁ p₂ P Kn M' Q p Z H' ha V hk pV vZ hZ -- binder p shadow
    let ts:= H'.yonderK; let Q:= Q; let S:= shapeO b x R.draws; have hL:∀ᶠ i in L, l i≤ c i∧ b i≤ c i:= ( ts.spectrum Q p Z ).mono fun i ⟨a0,v,p,h,_,_⟩=> by omega
    let seats:= Minty.artForFlash p Q hp0 H'.meshP d₂ (hL.mono fun i hi=> hi.1) y ( hL.mono fun i hi=> hi.2 ) x d' j0
    obtain ⟨δ,v',portrait_⟩:= poseStampForFlash p Q Z ts hp0 H'.meshP d₂ ha h0 x d' N w0; obtain ⟨C,H⟩:= CheapAngles (n:=n) p Q Z ts hp0 A₀ H'.prospect; have hw:∀ᶠ i in L,0< UVClock.mark B i:=( hp0.eventually_gt_atTop 0 ).mono fun i hi=> inv_pos.mpr (sqrt_pos.mpr hi)
    have he:= savings p Q Z ts hp0 Δ iG u_ z j1 j2
    exact survivingForFlash Kn M' Z § y S N seats H'.display t₁ clock hw v_.2 v_.1 (fun i=> Ω (Δ i)) (fun i=> p₁ ( Δ i )) (fun i=> p₂ _) d₀ Q' B_ (P.bed _ t _ (Nat.zero_le _)) (P.bed _ (Nat.le_trans (Nat.le_add_right ..) hk) _ pV) (P.lamp _ t _ (Nat.zero_le _) _ pV) (portrait_ C) H pD (O_angle hp0 Cϑ ) p_ q' A' pW hp he.1 he.2
end YM.SignedWilsonExpansion.Purchases.HalfRoof.Cooking

end
