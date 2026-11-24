import YM.Gaps1020.Local.Feasibility
set_option autoImplicit false
noncomputable section
namespace YM.GapsLocal.Full
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
open YM.Overlay.GapsLocal
variable {G:Gauge}
section keystone -- define independent of analytic buys, in for Q, any clip/path/testing etc. no assumptions.
variable {ι V:Type}[Fintype ι] [Fintype V][DecidableEq V]{E':Marker.Census V}{f c:Side}{R:RG.Rep G f}
variable (q:ι→Menu.Hat E' R)(i:V→ℂ)(S:StepData c f){w:V→ℝ}
def given (U:Config G f) : Poly E':= Poly.pass (Accent.Mach E' i)*((Real.exp (R.exponent U):ℂ) • (Poly.pass (∑ j,Menu.odour (q j) U) * field (fun p=> Accent.bar R.activities E' U p+∑ j, Menu.fragrance (q j) U p) (RG.flags R.p.threshold U)))
-- want form without `field`, true labels (Kunt/admissible), universal selected test proof. connect to consumer definition.
lemma fragrant {a b c' d e:ℝ}(h:R.Lawful a b c' d e)(ht:∀ i,0<w i) :
    let v:= Menu.heap q; let r:=fun i=>Menu.sumFee (v i) w; let s:= fun i=>Menu.sing (v i) w
    given q i= litGiven (S:=S) (fun i=>(v i).M) r s i:= by
   intro v r s; funext U; unfold given v litGiven
   rw [Menu.passIn (h:=h) (S:=S) _ ht U] -- heap not unfolded in r? stepData etc
   rw [Menu.golden, Menu.banded, Menu.perfumes]; simp_rw [Menu.patron]
end keystone
section spring
open UVNext.CouplingReset
variable (g:G.Simple) {X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Factor A}{L:Side}{m n N K k a b d: ℕ}{l v:ℝ}{Q: In A.B.a m n} (H: Spring R N m n l v Q)(x:Set.Icc l v)
local notation "j0" => A.B.a.clock.J m
local notation "i0" => A.B.a.clock.J (m+1)
local notation "s0" => A.B.a.clock.hatBeta m
local notation "k0" => Real.sqrt (A.B.a.clock.forcedAllowance m)
local notation "S'" => A.B.a.clock.op m n
local notation "W0" => Mallow.houseS H x
local notation "T0" => X.p.profile j0
local notation "Z" => horizonRadius G (D.L i0) s0
local notation "ρ" => shadowFactor G (D.L i0) s0 a
variable {ι V:Type}[Fintype ι][Fintype V][Nonempty V][DecidableEq V]{E':Marker.Census V}
variable (q:ι→Menu.Hat E' (Q x.val))(w:V→ℝ)(i:V→ℂ)(v':V→Site (A.B.a.S.side (m+1) n))
variable {e:ℝ}
open Mallow
local notation "ψ" => Menu.heap q
abbrev target (a b d:ℕ):ℕ:=Vacuum.targetM d+(a+5)*b
local notation "M'" => target a b d
local notation "P₀"=>A.B.a.budget m
local notation "Q₀"=>A.B.a.budget (m+1)
local notation "W'"=>shade w ρ⁻¹
set_option quotPrecheck false
local notation "S''" => (S').ratio.parent ∘ v'
local notation "G!"=> Vacuum.nativeG (Q x.val).beta
structure Outfit (a b d:ℕ)(Z₀: RG.Rep G (A.B.a.S.side m n)) (u:ℝ): Prop where
  adapted : let M'':=ψ; let ψ' :=shade w ((shadowFactor G (D.L i0) s0 a))⁻¹; let rA:=fun i=> Menu.sumFee (M'' i) ψ'; let g':=fun i=>Menu.sing (M'' i) ψ'; let f:=fun i=>(M'' i).M; given q i= litGiven (S:=S') f rA g' i ∧ Claim W0 Z₀ f rA g' (Many.pupilK H x f rA) S'' i (target a b d) w u ((Real.sqrt 2*G!)^(d+1)) ((shadowFactor G (D.L i0) s0 a)^b) k0
  equals : Z₀=H.result x
include g
local notation "X!"=> R.expense i0 j0
local notation "β" => betaF G s0 (D.L i0)
local notation "Z₀" => (Q x.val)
lemma wear (hS:Mallow.RG12.Earned (markerBudget G) R.shape A.delay) (hm:m < N)(h:Mallow.Arrives R.shape A.delay)(hv:(Q₀).supportExponent≥100) (hj:(P₀).supportExponent≥100)
      (hM:target a b d ≤ i0) (hw:Extra.Multi.Occupancy ((A.B.a.clock.op m n).ratio.parent ∘ v') i0)
      (hQ: Menu.Offer v' q w (Q x.val).p.B ((Q x.val).p.supportExponent-4) (Z^a)) (hE:∀ i,0<w i)(hx:∀ j,w j*‖i j‖≤e)(he:∀ i:E'.Mode,i.val.card ≤ b) :
    Outfit H x q w i v' a b d (H.result x) e:=by
   obtain ⟨htC,C,d',v0,Y,a',b',r',B,q',k',N',H'⟩:= Vacuum.Markets.certified (H:=W0) (N:=N) hm hS (target a b d) hM
   -- recognition: (same receipt/remainder, repricing can change units)
   let t:= htC.enough
   have ht:A.B.a.clock.hatBeta (m+1)=β:= Push.PriceCompiler.beta_eq A.B.valid m
   have hb:1≤ β:= ht ▸ A.B.a.fits.delayed (m+1)|>.le; have hZ:1≤Z:= Real.one_le_rpow hb (by norm_num [Thermal1020.ray])
   have hB:1≤ρ:=one_le_pow₀ hZ; have h0:0<ρ⁻¹:=by positivity
   have hX: (Q x.val).p=Q₀:= (H.knows _ x.property).1.point; have hXO: 100 ≤ (Z₀).p.supportExponent:= by rw [hX]; exact hv
   have hT := deckPrice htC.enough hb q hE hQ (by linarith); have H_rev :4 ≤ (R.target i0 j0).relative:= by
      have he : (P₀).supportExponent+3 ≤ (X!).earn :=by rw [Rain.jersey (A:=A) (m:=m)|>.2.2.1]; exact (R.pledging.agenda _ _ (step_paid A.B.a m)).1
      change 4 ≤ (R.target i0 j0).exp+_+_; linarith only [he,hj,(X!).worth,(X!).first,(X!).second,(R.target i0 j0).usable,(R.target i0 j0).pos]
   let M1(i):=(ψ i).M; let b1(i):=Menu.sumFee (ψ i) W'; let z1(i):=Menu.sing (ψ i) W'
   have hVV:= shade_pos w hE h0
   obtain ⟨hU,hL⟩:= feasible (w:=W') W0 ψ hT hw t.shipping H_rev hXO htC.flock (by rw [(W0).laws.intake.sizes,(W0).laws.data.funds.length_eq]; exact H'.book.covers) hVV t.nonneg
   let U:=W';
   have hUI(j): U j*‖i j‖ ≤e:= by unfold U Overlay.GapsLocal.shade; rw [mul_assoc]; apply le_trans _ (hx j); refine mul_le_of_le_one_left (mul_nonneg (hE _).le (norm_nonneg (i j))) ?_; rwa [inv_le_one₀ (by linarith)]
   have he':= bud g H x M1 b1 z1 U i S'' hS hm (target a b d) hM h hU (fun i=> (Menu.virtue ..).2) hVV (fun i=> Menu.paid _ hVV) hL (fun i=>(Menu.virtue ..).1) hUI
   refine ⟨⟨fragrant q i S' (W0).laws.intake.cap hVV,widenClaim W0 (H.result x) M1 b1 z1 (Many.pupilK H x M1 b1) S'' i he' (fun i=> curveCost w i hE (he i) hB) (by positivity) ?_ (by rw [mul_one]) hE hx⟩,rfl⟩
   have ha:((target a b d)+1)= (a+5)*b+2*(d+1):= by unfold target Vacuum.targetM; omega
   have ht' := (H.knows _ x.property).2
   rw [ha, pow_add,_root_.mul_inv_rev, shadowFactor,← pow_mul, mul_left_comm, mul_inv_cancel₀ (by positivity),mul_one]; apply Vacuum.radiusBill
   · have h := A.B.a.fits.delayed (m+1); linarith only [h,ht'.1]
   exact ht'.2
end spring
end YM.GapsLocal.Full
