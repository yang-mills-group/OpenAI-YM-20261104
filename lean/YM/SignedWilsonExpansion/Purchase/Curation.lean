import YM.SignedWilsonExpansion.Dancer.Supper
/-!
# Exact Ward-coefficient face pricing, available *before* the FVA2 reference scale quote

Expose the three different prices of the panorama on its one Treasury (visual placement + period
phase along a rotating short distance calendar). The first coefficientwise estimates WITHOUT ANY
quote on this face, relying instead on the admitted regulator/purchase bounds and exact coefficient
matching with THESE helper books. The later quote spends its familiar `(pn,v)` exactly from the
same commissioner, so no silent reset of nodes / resampling of period phase / shorter horizon.
In particular, the first price is **meaningful for order two**. Bill cost to requested `a`,
not the helper worker `(n+1)*h`. See also `Bench`, `TollQ.estimate` and `Cadet.surfeit`
for the warp margins before truncation and the final clock reset.
-/
set_option autoImplicit false
set_option maxHeartbeats 720000
noncomputable section
namespace YM.SignedWilsonExpansion.Dancer
open XSpace XSpace.Cirrus XSpace.Structure1 Normalize Future Gauge Filter Function Matrix
open WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa MarqueQ Stair PorchK
open Purchases Asymptotics Shell Lights Fort Coats Commission Maxwell Maxwell.Free Maxwell.Wick
open Precision Wilson Source WardBin Labels FVA2 FVA2.Dframe
open FVA2.Scale MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open RG Lattice UVClock Schedules HalfRoof HalfRoof.Minty HalfRoof.Cooking PowerSeries
open scoped BigOperators Topology Classical
variable {G:Gauge} {d h t w n e k u K b a v:ℕ}{ι:Type}{L:Filter ι}
namespace Supper
open Drawing Method Method.Epic
open WilsonCoeffUV.Cosmos.Polestar
variable {R:Realm G (e+1) Credit.leanC}{F:Labels.Frames G}{Ω:Council F}
variable (X:Hol G)(p₁:∀ i,(Ω i).Sound X)(p₂:∀ i,Bid.pop (Ω i))(P: Install X (Master.mk (F.level) Ω p₁ p₂) R K)
variable {W':Initialize G}{Q:∀ h,Rays G h W'.hol}
variable (V:Normalize.Store G)(Kb: Rose.Pick V){Y':MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{S':Prescription (Press.portDeck G)}(M:Speed.Quoted W' Kb Y' S')
variable (z:ι→ PorchK W' F Q Ω R h k u){B Y r T τ:ι→ℝ}{l m f j c o N:ι→ℕ}(p:∀ i,0<r i)
variable {δ β:ℝ}{D:Axis} (C: Club V Kb R z L l m f j c o B Y r T τ p a d b K β δ M D )
local notation "M₀"=> (mark B)^a
variable {ξ:ℕ} (w: Fin (n+1)→ℕ)(c₁:(n+1)*h≤u)(c₂:(n+1)*k≤K)(c₃: (∑ i:Fin (n+1),w i) ≤ ξ) (d₀:∀ i,w i ≤ h)
    (h₁: (ξ:ℝ)*β+-δ < a*(-1/2:ℝ)) (h₂: (ξ:ℝ)*β+(b+1:ℝ)*(-1/2)<a*(-1/2) )
open MarqueQ.Crops Crops.Taught TollQ
variable (hs:c ≤ᶠ[L] N) (x:ι→Fin (n+1)→ Cover)(y:ι→Stage (n+1))(q:ι→ (i:Fin (n+1))→(F.level (w i)).Coeff) (vU:Set (Points (n+1)))(v₁:IsCompact vU)(v₂:vU⊆ conf _) (v₃:∀ᶠ i in L,(y i).val= Garden ( hereD R.draws r f i ) (x i) ∧ (y i).val ∈ vU)(v₄:∀ i,SizeW L ( dollar B ) ( F.level ( w i ) ) (fun j=> q j i))
local notation "§"=> ( picture l c f x R.draws p )
local notation "⌂"=> ( shapeO f x R.draws )
local notation "τW"=> (staffing z w ( fun i=> Ω (w i)) q N ⌂ )
local notation "ΠW"=> (pupils z V Kb w ( fun i=> Ω (w i)) q § )
local notation "U∘"=> (trialU Kb z y ( fun i=> Ω (w i)) q )
local notation "℡"=> (fareU z w )
local notation "⋈"=> (℡*payD B (-δ))
local notation "μ"=> ( dollar B )
/- Field names after tariff:
  columns of ℓ..c through the actual TOP program on poseStamp and its budget as distinct from
  booked faces at l..v; Warp on that *one* normalization, with SAME samples; evaluation after
  translation back to ℓ₁ credentials. -/
structure PriceList : Prop where
    seated : Seats L § y vU
    openLens : ∃ t:ℝ, 0<t ∧ ∀ X:ℝ, PoseW t z § ⌂ L ( payD B (-X)) N
    quoted : ∃ t:ℝ, Cheap z n L μ (payD B (-t)) (payD B (-δ))
    staff : charge e L μ ((fareU z w)*payD B (-δ)) ( fun i=> ΠW i -τW i )
    receipt : ∀ k≤e,(fun i=> coeff k (ΠW i- τW i))=o[L] M₀
    follow : charge e L μ ((fareU z w)*payD B (-δ)) ( fun i=> ΠW i-U∘ i )
    redeem : ∀ k≤e,(fun i=> coeff k (ΠW i-U∘ i))=o[L] M₀ -- PowerSeries.coeff difference, includes heights
include P C c₁ c₂ c₃ d₀ h₁ h₂ hs v₁ v₂ v₃ v₄
lemma priced : PriceList V Kb z p w x y q vU (L:=L) (N:=N) (δ:=δ) (l:=l) (f:=f) (c:=c) (B:=B) (a:=a) :=by
    have hp0:= C.camp.timeRise
    have ts:= C.camp.yonderK
    have hL:∀ᶠ i in L, l i≤ c i∧ f i≤ c i:= ( ts.spectrum Q p z ).mono fun i ⟨a0,v,p,h,_,_⟩=> by omega
    have hc:∀ᶠ i in L, Garden ( hereD R.draws r f i ) ( x i ) ∈ vU := v₃.mono fun i hi=> hi.1 ▸ hi.2
    have seats:= Minty.art p ( hL.mono fun i hi=> hi.1 ) C.camp.meshP y v₁ v₂ ( hL.mono fun i hi=> hi.2 ) x hc ( v₃.mono fun i h=>h.1 )
    have sm := C.camp.progeny n _ v₁ _ (show ∀ᶠ i in L,Garden ( hereD R.draws r c i ) ( ⌂ i ( c i ) ) ∈ vU from ((hL.and hc).mono fun i hi=>by unfold shapeO Garden hereD; rw [ stamp_pine _ _ (p i) hi.1.2]; exact hi.2))
    obtain ⟨t,ht,P'⟩:= poseStamp p Q z ts C.camp.meshP v₁ v₂ C.rank c₁ x hc sm N hs
    obtain ⟨E,H⟩:= CheapAngles (n:=n) p Q z ts hp0 C.budget C.camp.prospect
    choose V' c' using fun i:Fin (n+1)=> pupilPrice (iℓ:=Unit) (e:=e) (u:=u) (Ω ( w i )) (p₁ _) (p₂ _) ((d₀ i).trans C.rank)
    have hw:= ( savings p Q z ts hp0 w C.needed c₃ C.positive h₁ h₂ ).1
    have hp:= PorchK.earning z V Kb C.camp.display w ( fun i=> Ω ( w i ) ) V' q v₄ N § ⌂ Credit.leanC (P.bed _ c₂ _ (Nat.zero_le _)) Credit.leanC (P.bed _ (Nat.le_trans (Nat.le_add_right ..) C.depth) _ C.stamp) Credit.leanC (P.lamp _ c₂ _ (Nat.zero_le _) _ C.stamp) (P' E) H c'
    have hs:= surprise X p₁ p₂ P V Kb M z p C
    have he:= estimate Kb M z § y seats C.camp.display τ C.clock (Occupation X p₁ p₂ P V Kb M z p C) hs.2 hs.1 ( fun i=> Ω ( w i )) (fun i=> p₁ ( w i )) (fun i=> p₂ _) d₀ q v₄ C.hV
    exact ⟨seats,⟨t,ht,P'⟩,⟨E,H⟩,hp,fun i h=>Wage.spend ( hp i h ) hw,he,fun i h=> Wage.spend ( he i h ) hw⟩
-- expose optional Eval? later
end Supper
end YM.SignedWilsonExpansion.Dancer
