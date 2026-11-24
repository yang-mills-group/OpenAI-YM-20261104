import YM.FVA2.ZeroMode
import YM.FVA2.InField

/-!
# Source canonical change is not an exact `Endμ` identification

Unmarked field scaling is passed on BOTH exponents and sources exactly. A
second comparison (with Score=motto added to rent) DOES carry a residual; not
proving via explicit evaluation of one-generator-at-infinity but by the
alternative bulk calculus in the supplied Lean. Here expose quantitative
version directly between the finite `Endμ`'s (and to a standard Wilson reading)
along one arbitrarily given admissible joint schedule. Retain also the budget
for image transport of both corresponding correlated exponent lifts, not just
assert convergence at the end. Use `PeakT any_power`, cost uniform on the Trial
and all sufficiently deep cutoffs. This shows the `motto` insertions can be
dropped; no claim their cuts vanish identically on-quotient or at given finite
volume, and not promising geometric-position derivatives of scalar limits.

For scope of the differentiated kernel statements retained: YM/MS/Vista/ClosingV,BranchC,Folk etc.
They are in the *supplied MS momentum/belt/clock norms*. On same-sign and
inverted branch of massless Kernels, period discrepancy carries differential
`Lease`: all E:NT space and Wire in the permitted ranks/KCourse constraints, `Here`
 on price (involves ContDiff(along lifted wire) jet bounds through Cost). `ΔMark` and
 `Period` encode such bounds for both finite-period and infinite-period
 preclosure. Not stating additional heat-kernel pointwise maxima or using the
 manuscript's stronger/similar particular localized inequality on generators at
 finite period. We prove the **net effect** estimate, more useful in the
comparison. Bounds hold at all marks/orders with the same clocks.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
/- Again on exact topW, see also non-top from ZeroMode. -/
namespace YM.FVA2.PeriodCost
open Set Function Filter Finset Metric MeasureTheory Real
open MS Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native
open Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit Cog
open Vane Rake.Geo Land Program Wind Menus Orbit.LogReal
open Puff Puff.Actors Puff.Engine Puff.Mom Vista High High.Knobs SpaceOut Fleet
open Tide Swirl Swirl.Near MixedStory Canonical
open scoped Topology ContDiff Interval
variable {G:Gauge}{I W:Type}[LinearOrder W] {O:Local.Physical.Deck G} {R:Booked O}{S:MS_Data G R}
variable (p:Dial.Trial I W)(V:Visa I) (φ:Warehouse G)(A:Land.Prescription O)(w:W→Label O)
local notation "L"=> (p.side)
local notation "xZ"=> (p.profile)
local notation "η"=> (p.profile.η)
local notation "ϕ"=> (p.head)
local notation "δ"=> (A.team)
local notation "Ψ"=> (Scope G (skyline G A.team) p.profile.η)
local notation "σ"=> Orbit.uniform G I
local notation "ν"=>TokenB G A.team p.profile.η
local notation "Ω"=> enterV L true
local notation "ΨF"=> lampV G L
local notation "Ξ"=> Mid V p.side
local notation "Wκ"=> Wilsonian.Actor G
-- any Q from single F.Portrait.Ties to End
local notation "Fκ"=> (ApplyMM (φ.native O) A.team A w)
local notation "Gκ"=> (PortEntryM (φ.native O) A ∘ w)
local notation "κA"=> (ApplyMM (φ.native O) (Stripped A.team) A w)

variable {μ:ℝ}{l:Filter I}(hW:WidthW V p.profile.η p.off)(u:Dial.Uses p l μ) -- need autoImplicit ℝ,l
include hW
variable (J:Seeds G I W)
include u
lemma expand_field (h:FlowSet V J)(Kp:TaylorOKM S (φ.native O) A)
   (Y0:Rake.Dance G I W)(hY:Circuit (outside L) σ ν ϕ J Ψ 0 Y0)(h0:SpaceOut.Folio Y0 V L)
   (S:Rake.Site G I)(D:H_defect G I)(Y:Rake.Dance G I W)(hF:Circuit Ω ΨF ν ϕ J S D Y): ImageCost p V A J Y0 Y:= by
    have ht:=u.clear; have hz:=u.wind; let U:= ΨF; have hU:=health G L; have hm:=Doors G V L
    let T (p0: I):=Vision L true Y p0 p.head; have hv(i:I): Portrait G η δ ϕ L true J i ( Valve L true S D i ) ( T i ) := by unfold Portrait LedgerB; rw [← traveller G L true i ]; exact C_to i hU hF (guarding G δ η L i)
    let X0:= Sedona (b:=true) ht hz V; have hx: Vista.Gate V Ψ J := ⟨ sky_budget hW.proper ( skyPC G δ) Kp.bulk,fun i=> (h i).2⟩; have he:∀ s:Finset W,s.Nonempty→∀ n,FinalScore V L ( Y s n )∧ FinalScore V L ( Y0 s n )∧ cash_out V L ( Fleet.toZ Y s n-Fleet.toZ Y0 s n ) := fun s hs n=> signal hY hF hx hm X0 s hs n
    exact ⟨ hY,⟨ S,D,hF, μ_maker hY hF hx hm X0, last_m hY hF hx hm X0, hv⟩, ζ_cover hY hx hm,fun s hs n=> ⟨ Peak hY hF hx hm X0 hs n,( he s hs n ).2.2⟩,⟨ fun s hs n=>( he s hs n ).1,h0 ⟩, ⟨ X0,hm⟩ ⟩

set_option maxHeartbeats 220000 in
lemma periods (h:FlowSet V J)(Kp:TaylorOKM S (φ.native O) A) : ∃ Y X:Rake.Dance G I W, ImageCost p V A J Y X:= by
    have ht:=u.clear; have hz:=u.wind; let U:= ΨF; have hU:=health G L; have hm:=Doors G V L
    obtain ⟨S0,H0,Y0,hY,h0⟩:= HarborStory Kp.bulk h hW.proper p.head L; have hb : H0=0:= deadD rfl hY.defect; subst H0 ; have hh : S0= Ψ:=soloB hY.action (dawnG η L ( skyPC G δ)); subst S0
    obtain ⟨S,D,Y,hF⟩:= CorΦ (K:=U) Ω ϕ hU (tokenCaps δ η G) (fun z=>(h z).1);
    exact ⟨ Y0,Y, expand_field p V φ A hW u J h Kp Y0 hY h0 S D Y hF ⟩

omit J hW u
variable (μ l)

section extract
local notation "Yκ"=> (MixedStory.connected φ p A μ w)
local notation "Pκ"=> Master G ( dimT p.side i ) true -- i scope in usage?
local notation "↧F"=> fare ( Label.h ∘ w ) p.profile

-- expose separation.Meromorphic.Use clock pointwise.Both Endν taken on same gauge Team on each side before undo. Exact linear rescaling on Full Fκ.
structure Estimate : Prop where
      visa : WidthW V p.profile.η p.off ∧ NearPlan l p.profile V p.side μ
      kernels : ∃ (U Y Ur Yr:Rake.Dance G I W),
           ImageCost p V A (goalsK p.off η Fκ) U Y ∧ ImageCost p V A (goalsK p.off η Gκ) Ur Yr ∧ Fleet.toZ Y=Yκ∧
           caseV p A Fκ Yκ ∧ caseV p A Gκ ( Fleet.toZ Yr )
           ∧ (∀ n s,Fleet.toZ Ur s n=ᶠ[l]Fleet.toZ U s n) ∧
           -- net effect of source-dependent canonical change.Mass. after rescaling.N.
           ∀ s n (N:ℝ), PeakT l p.profile N ( ↧F (Fleet.toZ Yr ) s n- ↧F Yκ s n ) ∧ PeakT l p.profile N (↧F (PeakT.ordZ (Fleet.toZ Yr)) s n-↧F (MixedStory.ordinary φ p A μ w) s n)

lemma blankF {Q:Seeds G I W}{X Y:Rake.Dance G I W} (h:ImageCost p V A Q X Y) : Fleet.toZ Y ∅=0:= by obtain ⟨_,_,h,B⟩:=h.lifted; exact Tide.zeroZ h.crew.1
private lemma net (hz:NearPlan l p.profile V L μ){U Y X D:Rake.Dance G I W} (hu:ImageCost p V A (goalsK p.off η Fκ) U Y)(hv:ImageCost p V A (goalsK p.off η Gκ) X D)(h:∀ n s,Fleet.toZ X s n=ᶠ[l]Fleet.toZ U s n)(s:Finset W)(n:ℕ)(k:ℝ) : PeakT l p.profile k (↧F (Fleet.toZ D) s n - ↧F (Fleet.toZ Y) s n ):= by
    rcases eq_empty_or_nonempty s with rfl|he; · unfold Tide.fare; rw [blankF p V A hu,blankF p V A hv,sub_self]; exact PeakT.zero
    rw [Tide.fare, Tide.fare,← mul_sub]; apply Tide.significant; let P:=p.profile; let b:ℝ:= (Vane.charge ( Label.h ∘ w ) s:ℝ)+k;
    have hm : cash_out V L ( (Fleet.toZ D s n-toZ X s n)-(Fleet.toZ Y s n-toZ U s n) ) := Vista.cash_sub ( hv.period s he n |>.2 ) ( hu.period s he n |>.2 ); refine PeakT.fromζ ( hz.costG hm b ) ( ( h n s ).mono (fun i hx=>?_ ) ); rw [ Pi.sub_apply,Pi.sub_apply,Pi.sub_apply,Pi.sub_apply,hx ]; ring

-- nonlinear comparison retains arbitrary powers on common torus family since input cover functions at these orders are bounded by continuum comparison.
private lemma netOrd {F Y:Fleet.Terrify W I}(h:∀ s n (N:ℝ), PeakT l p.profile N (F s n-Y s n))(he:∀ s n, PeakT l p.profile 0 (Y s n))(s:Finset W)(n:ℕ)(N:ℝ): PeakT l p.profile N (PeakT.ordZ F s n-PeakT.ordZ Y s n) := by
    let t := max 0 N; let u (F:Terrify W I) i s n:= F s n i; exact PeakT.downs (le_max_right _ _) ( PeakT.powT ( H:=u Y ) ( X:=u F ) (Puff.SplitP.marked W) (le_max_left 0 N) (fun i n=>⟨ he i n,h i n t⟩) s n |>.2 )

include u
theorem residual (hG:G.Simple)(B:AllProfiles S φ A) : ∃ V:Visa I, Estimate p V φ A w μ l:= by
    have hx : Dial.Uses p l μ:=u
    obtain ⟨V,hW,hz⟩:= qualifies p.off hx.total hx.reality hx.upright hx.super; refine ⟨ V,⟨ hW,hz⟩,?_⟩; obtain ⟨hK,hP,H,hmenu⟩:= billMenusM w (φ:=(φ.native O)) (A:=A) hG; obtain ⟨ U,Y,hU⟩:= periods p V φ A hW hx _ (moneyM p.off hW (fun i=>⟨ false,0,hK.badge i ⟩)) B.1; obtain ⟨ Ur,Yr,hV⟩:= periods p V φ A hW hx _ (moneyM p.off hW (fun i=>⟨ false,0,hP.badge i ⟩)) B.1
    have hv : Dial.CutoffM (φ.native O) w p μ true A ( Fleet.toZ Y ):= fun i s=> hx.reality i ▸ κglyph p.off i hK.badge ( ImageCost.readsCC p V A hU ) ( Track.request_friendly φ _ (Matched.tFees A w) _ ) H
    have ht:= MixedStory.treeCost φ p A μ w hv (blankF p V A hU)
    have hQ :∀ n s,Fleet.toZ Ur s n=ᶠ[l]Fleet.toZ U s n:= by
         intro n s; let a i s n:= toZ Ur s n i; let b i s n:= toZ U s n i; refine peaks ( l:=l ) ( X:=a ) ( Y:=b ) (Puff.SplitP.marked W) Toy (pointed _ (zeroZ hV.cover.crew.1)) (fun _ _ _ _ _=> Submodule.mem_top) (pointed _ (zeroZ hU.cover.crew.1)) (fun _ _ _ _ _=> Submodule.mem_top) ?_ s n; intro i n; exact Echo.quote (payTune p.off u.knit u.upright) hP hK B.1.bulk hG hmenu hV.cover.crew hU.cover.crew n i
    have hn s n: PeakT l p.profile 0 ( ↧F ( Fleet.toZ Y ) s n ):= ht.1 ▸ ( PeakT.retain (accuracy S φ p A μ w l B u s n|>.1) (mild_p.le))
    refine ⟨ U,Y,Ur,Yr,hU,hV,ht.1.symm, ht.1.symm ▸ isEnd p A hK.badge ( ImageCost.readsCC p V A hU ), isEnd p A hP.badge ( ImageCost.readsCC p V A hV ), hQ, fun s n N=>?_ ⟩ ; rw [ht.2,ht.1]; have ho(X:Terrify W I): ↧F (PeakT.ordZ X) s n= PeakT.ordZ (↧F X) s n := funext fun i=> ( PeakT.ν_norm (Label.h ∘ w) i _ ).symm
    constructor; exact net p V φ A w μ l hz hU hV hQ s n N; rw [ho,ho]; exact netOrd p l (net p V φ A w μ l hz hU hV hQ) hn s n N
end extract
end YM.FVA2.PeriodCost
