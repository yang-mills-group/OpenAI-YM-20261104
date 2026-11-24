import YM.SignedWilsonExpansion.F9.Bench
/-!
# Linear expansion and payout on path in WCU cover quotation
 Orders through fixed p from posed pantry. ζ timetable common.Mark.Owner Projection later rest.
 At each physical reporter node & proper faces, including for varying crops. Expert Witness can invest here even before meeting actual epoch requirements.Anchor.Bounds in physical workplaces.
-/
set_option autoImplicit false
set_option maxHeartbeats 145000
noncomputable section
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
variable (hQ:Seats L pn p VQ)
variable (KQ: FrontQ q L Y θ μ ν) (pτ:ι→ ℝ) (pt: TimeQ L θ pτ)(w:∀ᶠ i in L,0< θ i)
variable (St:∀ i≤e, Across L Y ℂ (fun j=>(q j).toEpic.tenor W' V' i))(U':RateQ.Costy L Y (fun i=>(q i).toEpic.voice W' K) e)
variable {τ₀: Hol G}{d':Fin (n+1)→ℕ} (S:∀ i:Fin (n+1),SectionData (F.level (d' i))) (pS:∀ i,(S i).Sound τ₀)(hS:∀ i,Bid.pop (S i))(h₀:∀ i,d' i≤h)(Z':ι→ (i:Fin (n+1))→(F.level (d' i)).Coeff) (tZ:∀ i,SizeW L μ (F.level (d' i)) (fun j=> Z' j i))
local notation "Tᵥ"=> Measure.start W' K h
abbrev view (i:ι): Tape.Table ( Normalize.Sec G h ) (n+1):= Tᵥ (n+1) ( p i )
def trialU (i:ι):= fadedSlip q V' K d' S Z' (P:=view (h:=h) (W':=W') K p) i
variable {U1 U2 V0:Credit} (hp: Dormitory R ((n+1)*k) 0 U1)(hp': Dormitory R k u U2)(hϑ:SpringD R ((n+1)*k) 0 u V0){δ:ℝ}
variable (pF:PoseW δ q pn W0 L Uw N)(sale: Cheap q n L μ Uw ε)
variable (reg: Wage L μ ε (Speed.chip ∘ grab ∘ pn))
abbrev Pointer (i:ι):= (calcT (pτ i) d ( staffing q d' S Z' N W0 i )) -- d eventual binder
lemma payFare (q:ι→PorchK W' F V Ω R h k u): fareU q d' = (∏ i:Fin (n+1), (fun j=>(q j).billSize (d' i))):=by ext1 j; rw [Finset.prod_apply]
-- farm fixed literal price since basis finite.Auth may ask via weight rank cap.Supply c. Guaranteed across if v₀≤k. separately.
lemma pupilPrice {iℓ:Type}[Fintype iℓ][ Nonempty iℓ]{S:Hol G}{d₀:ℕ}(S':SectionData (F.level d₀))(p:S'.Sound S)(h':Bid.pop S') (hK:d₀≤k): ∃ C:ℝ,∀ i, Mer.Xa.Respect k e u 1 ( Looms.literal S' i) C:=by
    choose C c using fun i:(F.level d₀).Index=> MarqueQ.Respect.allRank (Looms.strength (x:=i) S' h' p hK) e u
    exact ⟨∑ i,C i, fun i=> (c i).rise (Finset.single_le_sum (s:=Finset.univ) (f:=C) (fun j _=>(c j).nn) (Finset.mem_univ _))⟩ -- iℓ extraneous
include KQ M' pτ pt w hQ St U' pS hS h₀ tZ reg
lemma estimate : charge e L μ ((fareU q d') * ε) ( fun i=> pupils q V' K d' S Z' pn i- trialU K q p S Z' i):=by
     let B(i:Fin (n+1))(j):=(q j).billSize (d' i); let A(i s):= account V' (q i) (S s) (Z' i s); let X(i):= (q i).χ V' K; rw [payFare]; refine warp_margin KQ.inside_ B (Z:=X) (fun i=> (q i).Kconst ..) (τfit q V' K U' KQ w pτ pt) (T:=fun i=>numeral W' K (pn i) h) (S:=view (W':=W') K p) (?_) (a:= fun i j w'=> account_full q V' (Z:=fun j=> Z' j i) (pS i) (hS i) (h₀ i) KQ St (tZ i) j w')
     intro a k hk; simp only [map_sub,Tape.archive, coeff_mk]; refine Wage.rel reg ( ?_ ); exact ( TollQ.price R.hG W' K T P' 0 M' VQ pn p hQ a k ).1
include hp hp' hϑ pF sale
lemma earned : charge e L μ ((fareU q d') * ε) ( fun i=> trialU K q p S Z' i-staffing q d' S Z' N W0 i):=by
     rcases isEmpty_or_nonempty ι with h|e'; · exact fun i _=> Wage.enroll (IsBigO.of_bound' (Eventually.of_forall fun i=> isEmptyElim i))
     have vR:h ≤ k:= ((q ( Classical.choice e')).canv.reserve W'.hol).order
     choose C c using fun i:Fin (n+1)=>pupilPrice (iℓ:=Unit) (e:=e) (u:=u) (S i) (pS i) (hS i) ( (h₀ i).trans vR )
     have hv:= MarqueQ.PorchK.earning q V' K KQ d' S C Z' tZ N pn W0 U1 hp U2 hp' V0 hϑ pF sale c
     -- parameters explicitly if not ...
     have ht:= estimate K M' q pn p hQ KQ pτ pt w St U' S pS hS h₀ Z' tZ reg
     intro i p'; exact Wage.fix (Wage.minus KQ.inside_ (hv i p') (ht i p')) (Eventually.of_forall fun i=> by dsimp only; simp only [map_sub]; abel) (.refl ..)
omit hp hp' hϑ pF sale reg
lemma looks (ℓ:ℕ)(p₀:ℓ≤e):
    let t(i:ι):= (pτ i:ℂ); let V(i:ι):=(q i).earns0 V' K ℓ (pτ i); Taught L μ θ (fareU q d') t ℓ (trialU K q p S Z') (fun i=> invoke (view (W':=W') K p i) ℓ (V i) (fun j=> citeS ℓ (t i) (account V' (q i) (S j) (Z' i j)))):=by
     intro t V; rw [payFare]; refine Taught.manifests KQ.inside_ (smallG q KQ) _ (TimeN w pτ pt) (view (W':=W') K p) (fun i x=>(q x).billSize (d' i)) _ (setting q V' K U' KQ w pτ pt ℓ p₀) (fun i=> (q i).Kconst ..) ?_ (fun i j v=> account_full q _ (pS i) (hS i) (h₀ i) KQ St (Z:=fun j=> Z' j i) (tZ i) j (v.trans p₀))
     intro a k p; simp_rw [Tape.archive, coeff_mk]; exact Wage.enroll ( TollQ.price R.hG W' K T P' 0 M' VQ pn _ hQ a k ).2
-- Output cash for q ∈ simultaneous grants. At least M fixed requested p', permit ζ.Size.Can be chosen pure.T
include hp hp' hϑ pF sale reg
-- crop e = the max offered (p₀ denotes uptake varying later). evaluate any later crop k' at pτ in comparison.H!
variable (εp: Wage L μ 1 ε)
include εp
lemma surviving (p' p'' A:ℕ)(h0:p' ≤ p'')(he:p'' ≤ e)
       (wT:∀ d:ℕ,(fun i=> μ i^d * (fareU q d' i * ε i))=o[L] (θ^A))(v':∀ d:ℕ,(fun i=> μ i^d*(fareU q d' i*θ i^(p'+1)))=o[L] (θ^A)) :
       (fun i=> Pointer (d:=p'') q W0 N pτ S Z' i - invoke (view (W':=W') K p i) p' ((q i).earns0 V' K p' (pτ i)) (fun j=> citeS p' (pτ i) (account V' (q i) (S j) (Z' i j))))=o[L] (θ^A):=by
     let A₀(i):=trialU K q p S Z' i; let K₀(i):=staffing q d' S Z' N W0 i; let θ'(i):=(pτ i:ℂ); have vK:= (looks K M' q pn p hQ KQ pτ pt w St U' S pS hS h₀ Z' tZ e le_rfl).price; have hx:= earned K M' q pn p W0 N hQ KQ pτ pt w St U' S pS hS h₀ Z' tZ hp hp' hϑ pF sale reg; let B:= clockQ.chooseOne KQ.inside_ (smallG q KQ) θ' (TimeN w pτ pt) (fun i=> A₀ i-K₀ i) hx p'' he; have ht:= looks K M' q pn p hQ KQ pτ pt w St U' S pS hS h₀ Z' tZ p' (h0.trans he); have hv:= clockQ.dropFee KQ.inside_ (smallG q KQ) θ' ( TimeN w pτ pt ) A₀ vK p' p'' h0 he; have hp:= Wage.spend ht.bill v'; refine ((IsLittleO.sub (( Wage.spend hv v' ).sub (Wage.spend B wT)) hp )).congr_left (fun i=>?_); simp only [map_sub]; unfold Pointer θ'; unfold A₀ K₀; abel
end YM.SignedWilsonExpansion.Commission.TollQ
