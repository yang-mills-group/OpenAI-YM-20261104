import YM.FVA1.BinPrism
import YM.LocalTaylorR2.Orbit.Clocked
set_option autoImplicit false
noncomputable section
namespace YM.FVA1
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Control Window Coat Footprint Raw Matter
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Stained Shield
open PhysicalNext PhysicalNext.Repeat Height Greenbelt
open Gas Ursell Trees RG.Supply Org Roost Opera
open Input Testing PriceCompiler
open AnalyticBridge VerifiedReset Collection Extra.Iteration Match Song Refrain Geo Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat.Daisy.Charity.RG12
open YM.RG01.Survive
open YM.ConnectedActivityE6.Blaze.Thermal1020
open YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
open UVExtension Spire Orchard Mast Oasis Progress.DirectedRecipe Mallow YM.RG12 OPE
open GridApprox.Nil Marker Merge MergeProof Accent
open YM.Overlay.GapsLocal GapsLocal Full Menu
variable {G:Gauge}
open UVNext.CouplingReset
variable (g:G.Simple) {X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Factor A}{L:Side}{m n N M k a b d: ℕ}{l v:ℝ}{Q: In A.B.a m n} (H: Spring R N m n l v Q)(x:Set.Icc l v)
set_option quotPrecheck false
local notation "j0" => A.B.a.clock.J m
local notation "i0" => A.B.a.clock.J (m+1)
local notation "s0" => A.B.a.clock.hatBeta m
local notation "k0" => Real.sqrt (A.B.a.clock.forcedAllowance m)
local notation "S'" => A.B.a.clock.op m n
local notation "W0" => Mallow.houseS H x
local notation "T0" => X.p.profile j0
local notation "Z" => horizonRadius G (D.L i0) s0
local notation "Cμ" => (R.shape.μ i0 j0)
variable {T ι V:Type}[Fintype ι][Fintype V][Nonempty ι][Nonempty V][DecidableEq V]{E':Marker.Census V}
variable (q:ι→Menu.Hat E' (Q x.val))(w:V→ℝ)(o: Positions V (A.B.a.S.side (m+1) n))
variable (read:ι→(V→T)→ℂ)(header:V→(V→T)→ℂ)
local notation "σ"=>shade w (shadowFactor G (D.L i0) s0 a)⁻¹
local notation "X₀"=> R.expense i0 j0
local notation "c0"=> A.B.a.budget m
local notation "c1"=> A.B.a.budget (m+1)
local notation "β"=> betaF G s0 (D.L i0)
local notation "βq"=> (Q x.val).beta
local notation "μs"=> straw Cμ (D.L i0) G s0
local notation "gP" p:max=> (Real.sqrt 2*Vacuum.nativeG βq)^(p+1)
local notation "α"=> fun i=> (Menu.heap q i).M
local notation "src"=> fun i=>sumFee (Menu.heap q i) σ
local notation "K!"=> Many.pupilK H x α src

set_option quotPrecheck false
abbrev docket (v b:ℕ)(θ:ℝ) := let _:=v; θ^b
-- a implicit captured in σ: must used parameters
local notation "D!" P:max => FVA1.cards (χ:=Chi.canonical) α src W0 K! (Full.target a b d) P
local notation "U₁"=> D! (fun _=>True)
local notation "U₂"=> D! (fun p:ℕ=>¬ Full.target a b d +1≤p)
local notation "U₃"=> D! (fun p:ℕ=>Full.target a b d+1 ≤p)
local notation "ch"=> (shadowFactor G (D.L i0) s0 a)
local notation "E0"=> H.result x
include g
-- full split on the masks of the constructed pressure. Calendar eventually supplies purchase premises.
omit [Nonempty V] in
set_option maxHeartbeats 480000 in
lemma ballot (hS:Mallow.RG12.Earned (markerBudget G) R.shape A.delay) (hPu:Pungent R.shape A.delay) (h:m<N) (hs:Arrives R.shape A.delay)
   (he:100 ≤ (c1).supportExponent)(he':100 ≤ (c0).supportExponent)(hM:Full.target a b d≤ i0)
   (hw:Extra.Multi.Occupancy ((S').ratio.parent ∘ o.origin) i0)(hQ: Menu.Offer o.origin q w (Q x.val).p.B ((Q x.val).p.supportExponent-4) (Z^a))(hE:∀ i,0<w i):
    let J:=Full.target a b d
    let X:=((Z)^(J+1))⁻¹
    let σ':=(c0).supportExponent+1
    Ran q (S') (H.result x) (U₁) (U₂) (U₃) σ 1 X (μs) σ' ∧ (ch^b)*X ≤ gP d ∧ μs ≤ X*k0 ∧ 1≤ch:=by
    intro J V' e
    obtain ⟨htC,C,d',v0,Y,a',b',r',B,q',k',N',H'⟩:= Vacuum.Markets.certified (H:=W0) (R:=R) (N:=N) h hS J hM
    -- matches Wear.wear. now retain full marker variables, independent of actual V labels.
    let t:= htC.enough
    have ht:A.B.a.clock.hatBeta (m+1)=β:= Push.PriceCompiler.beta_eq A.B.valid m
    have hb:1≤ β:= ht ▸ A.B.a.fits.delayed (m+1)|>.le; have hZ:1≤Z:= Real.one_le_rpow hb (by norm_num [Thermal1020.ray])
    have hB:1≤ch:=one_le_pow₀ hZ; have hy:0<ch⁻¹:=by positivity
    have hX: (Q x.val).p=c1:= (H.knows _ x.property).1.point; have hXO: 100 ≤ (Q x.val).p.supportExponent:= by rw [hX]; exact he
    have hT := Full.deckPrice t hb q hE hQ (by linarith)
    have h' : (H.result x|>.p.supportExponent)+3 ≤ (X₀).earn:=by change (c0).supportExponent + 3 ≤_; rw [(Rain.jersey (A:=A) (m:=m)).2.2.1]; exact R.pledging.agenda _ _ (step_paid A.B.a m)|>.1
    have H_rev:4 ≤ (R.target i0 j0).relative:= by
      change 4 ≤ (R.target i0 j0).exp+_+_; change 100 ≤ (E0).p.supportExponent at he'; linarith only [he',h',(X₀).worth,(X₀).first,(X₀).second,(R.target i0 j0).usable,(R.target i0 j0).pos]
    obtain ⟨hU,-⟩:= Full.feasible (w:=σ) W0 (heap q) hT hw t.shipping H_rev hXO htC.flock (by rw [(W0).laws.intake.sizes,(W0).laws.data.funds.length_eq]; exact H'.book.covers) (shade_pos w hE hy) t.nonneg
    let hP0:=Many.usable g h H x α src N' hs H'.book (Palette.Thermal.allows _ _ _ hU)
    have hP(i:Mound q):((α) i).crest.Nonempty:= ((heap q i).shiny.image o.origin).mono (hT.sites i)
    -- macro `((α) i)` fails. paren
    have hdr: (E0).p.order=(T0).order:= Rain.jersey (A:=A) (m:=m)|>.1
    have hpow : (E0).p.power=(T0).power:= Rain.jersey (A:=A) (m:=m)|>.2.1
    have he':= Many.crowd2 g h H x α src N' hPu H'.book (Palette.Thermal.allows _ _ _ hU)
    have room (f:ℕ→Prop): (D! f).Room (E0):= room_at α src W0 (E0) K! J f N' hP0 hU H' hP rfl hdr.le
    have lent (f:ℕ→Prop)(p:ℕ)(hp:∀ i,f i → p ≤ i): (D! f).Lent (E0) 1 e ((Z^p)⁻¹) μs:=
      margin_loan α src W0 (E0) K! J f N' hP0 hU H' p hp rfl hdr.le hpow (by linarith only [h']) he'
    refine ⟨⟨cash_fused α src W0 (E0) K! J N' hP0 hU H' hP rfl hdr.le hpow (by linarith only [h']), A.B.a.transition_mass .., ?_,⟨room _,?_⟩, ?_,?_,?_,?_,?_⟩,?_ ,Blush.glyph_eq (A.B.a) m ▸ H'.forceCredit,hB⟩ -- type
    · exact ⟨_,_,_,_,_,(W0).laws.intake.cap⟩
    · exact ⟨room _,room _⟩
    · exact ⟨rfl,rfl,rfl,rfl⟩
    · intro i z; change (if z=(FreeCensus _).quiet then _ else _)=_ ; split
      next hz=> change (0:Config G _→ℂ)=(if _ then _ else _)+(if _ then _ else _); simp only [if_pos hz,add_zero]
      next hz=> change _=(if _ then _ else _)+(if _ then _ else _); rw [if_neg hz,if_neg hz]; exact (forecastAll _ _ _ _ _ _ (fun i=>J+1 ≤ i)).trans (add_comm ..)
    · exact ⟨rfl,rfl⟩
    · rfl
    · refine ⟨?_,?_,lent _ (J+1) (fun _ he=>he)⟩
      · simpa only [pow_zero,inv_one] using lent (fun _=>True) 0 (fun _ _=> Nat.zero_le _)
      simpa only [pow_zero,inv_one] using lent (fun i=> ¬ J+1 ≤ i) 0 (fun _ _=>Nat.zero_le _)
    unfold V'; rw [show J+1=(a+5)*b+2*(d+1) from (by unfold J Full.target GapsLocal.Vacuum.targetM; omega),pow_add,_root_.mul_inv_rev,Full.shadowFactor,←pow_mul,mul_left_comm,mul_inv_cancel₀ (by positivity),mul_one]
    have hp:=(H.knows _ x.property).2
    refine GapsLocal.Vacuum.radiusBill _ ?_ hp.2 _
    have hb:A.B.a.clock.hatBeta (m+1)>1:= A.B.a.fits.delayed _; linarith [hp.1]
end YM.FVA1
