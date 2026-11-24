import YM.Gaps1020.Local.Local
import YM.RG12.Burst.Cotton
set_option autoImplicit false
noncomputable section
namespace YM.GapsLocal.Vacuum
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
variable {G:Gauge} {X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Factor A}{L:Side}{m n N K k : ℕ}
variable {u: RG.Rep G (A.B.a.S.side (m+1) n)} (H : Guide A.B R.shape N m n u) (O:Return.Wood A.B m n)

local notation "s0" => A.B.a.clock.hatBeta m
local notation "j" => A.B.a.clock.J m
local notation "i" => A.B.a.clock.J (m+1)
local notation "σ" => X.p.profile j
local notation "Q0" => R.target i j
local notation "o0" => R.shape.o i j
local notation "Γ" => R.expense i j
local notation "χ!" => Chi.canonical
local notation "Z!" => horizonRadius G (D.L i) s0
local notation "PX" => A.B.a.budget m
local notation "F" => RG01.Survive.standard H
local notation "B!" => Thermal1020.basis H Chi.canonical K

abbrev keep (M:ℕ):= (logAt (R:=R) H M (Thermal1020.basis H Chi.canonical M) true)
abbrev err (M:ℕ):= (RG01.Survive.fusedError (R:=R) (x:=Thermal1020.basis H Chi.canonical M))
abbrev original : Collection.Source G (A.B.a.S.side m n) := (plusone H (identityX H) χ! (A.B.kin.alpha N m))
abbrev nativeG (β:ℝ):=(Real.sqrt β)⁻¹
-- Separate normalized path `earlyValue`, scalar Share, exponent, and force.
structure Report (K:ℕ) (cost : ℝ) : Prop where
  completeE : (original H).logRead=(keep H K).logRead+(err H K).logRead
  hardSameKeep : (original H).hardRead=(keep H K).hardRead
  hardSameErr : (original H).hardRead=(err H K).hardRead
  evaluated : (A.B.a.clock.op m n).push u.beta u.eval = RG01.Survive.coarse H O (keep H K)*RG01.Vacuum.exponentialShare (F) (PX) (err H K)
  localErr : Collection.Local (F) (PX) (err H K) cost (A.B.a.clock.forcedAllowance m)
  localKeep : Collection.Local (F) (PX) (keep H K)
    (Opera.earlyFee (p:=R.expense) A.B N m u.beta + (Z!^(K+1))⁻¹) (A.B.a.clock.forcedAllowance m)

variable {v Y d q C C' B r a b:ℝ}

private lemma retainedEq (K:ℕ) : RG01.Vacuum.shelf R H (RG01.Vacuum.importedTail R H (K+1)) false= remain H (χ:=Chi.canonical) (identityX H) (gradeCap (K+1)) (lengthCap (A:=A) (m:=m) (K+1)) (gShell (A:=A) (m:=m) (N:=N)):= by
  unfold RG01.Vacuum.shelf remain; congr! 2; rename_i z
  by_cases hv:RG01.Vacuum.importedTail R H (K+1) z
  · simp [RG01.Vacuum.chooseMark,hv,(YM.RG01.Survive.complement H z (K+1)).not.mpr (not_not.mpr hv)]
  simp [RG01.Vacuum.chooseMark,hv,(YM.RG01.Survive.complement H z (K+1)).mpr hv]

variable (hm:m<N)
variable {N':Captain H (X.p.profile (A.B.a.clock.J m)).order C' d v Y a b r B q k Chi.canonical}
  (he:Receipt (R.expense (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (X.p.profile (A.B.a.clock.J m)) K N')

include he
-- interface read through same stencil. This discharges existing `RG01.Survive`
-- analytic leaf producer inputs in their exact domain and norm.
lemma leafTicket : LeafReady χ! (gradeCap (K+1)) (lengthCap (A:=A) (m:=m) (K+1)) (B!) v (σ).order (slot N' (gradeCap (K+1)) K Z! (Z!^(K+1))) (Thermal1020.total N' (gradeCap (K+1)) K Z! (Z!^(K+1))) Z! := by
  exact leafReady N' he.turns he.chargeFits he.large le_rfl

include hm
theorem full (hu : RG.Shoot.Lives A.B.bake N (m+1) n u) (hb: u.beta ∈ RG.Shoot.band A.B.a (m+1))
    (hQ : Opera.Price A.B R.shape N m n u H)
    (hK:Real.exp (-(RG01.Vacuum.cashMark R m))*RG01.Vacuum.voucher (A:=A) m^3≤C*nativeG u.beta^(K+1)):
    Report H O K ((Real.sqrt 2^(K+1)+C)*nativeG u.beta^(K+1)+(Z!^(K+1))⁻¹) := by
  let S:=gradeCap (K+1); let ℓ:=lengthCap (m:=m) (A:=A) (K+1); let W:= (X.p.profile (j)); let Z:=F
  let θ:= A.B.kin.alpha N m; let g:=Z!
  have hn:(PX).order=W.order:= (Rain.jersey (A:=A) (m:=m)).1
  have hw:(PX).power=W.power:= (Rain.jersey (A:=A) (m:=m)).2.1
  have ha: preExponent (PX) ≤ (Γ).earn:=le_trans (show _ ≤ W.supportExponent+3 from (by unfold preExponent; rw [(Rain.jersey (A:=A) (m:=m)).2.2.1])) (R.pledging.agenda _ _ (step_paid A.B.a m)).1
  let B₀:=Thermal1020.basis H Chi.canonical K; have hL:= leafTicket H he; have hA:=he.second; let δ:= Height.asset (Γ)
  let β:= invoice (Q0) (D.L i) (R.shape.μ i j) s0 B g W.order k (cutK K) K; have hδ:= Height.asset_pos (Γ)
  have hS:Sailor G (PX).threshold q W.order:= ⟨fun c v hv=> N'.weigh.stroke c v (hv.trans N'.talent)⟩
  let Y:=err H K; let Z':=keep H K; let Z0:=logAt H K B₀ false; let W':= RG01.Vacuum.shelf R H (RG01.Vacuum.importedTail R H (K+1)) true; let X':= RG01.Vacuum.shelf R H (RG01.Vacuum.importedTail R H (K+1)) false
  have hh:= coupling H O hQ hm hu hb hL hn.le hw.le q N'.income hS N'.near N'.position ha hδ hA hK -- target API
  let τ:=readerCost (G:=G) (PX) W.order W.power g δ s0 β (1/2) (K+1)
  have hW:= RG01.Vacuum.rare R H O hQ hm hu hb (K+1) hK; unfold RG01.Vacuum.Decision at hW; dsimp only at hW
  have hx':X'= _ :=retainedEq H K
  have hLeft := survival (p:=(PX)) H hL (identityX H) θ rfl rfl hn.le W.power hw.le q N'.income hS N'.near N'.position ha hδ hA K le_rfl (hx' ▸ (show Collection.Local Z _ X' _ _ from hW.1)) (A.B.kin.path N m) (A.B.a.params m).clip u.beta (Song.weighty H Chi.canonical O) θ
  dsimp only at hLeft; rw [← hx'] at hLeft; change X'.logRead=Z'.logRead+Z0.logRead ∧ _ ∧ _ ∧ Collection.Local _ _ Z0 τ _ ∧ _ at hLeft
  have hFee: τ ≤ (g^(K+1))⁻¹:= by
    have hT:2≤g:= he.large
    unfold τ readerCost; rw [Rain.jersey (A:=A) (m:=m)|>.2.2.2]; rw [mul_left_comm]
    exact mul_le_of_le_one_right (by positivity) he.currency
  have ha0:= liftLocal hLeft.2.2.2.1 hFee le_rfl; have hy:Y.logRead=W'.logRead+Z0.logRead:=rfl
  refine ⟨?_,rfl,rfl,hh.1,addLocal hW.2.1 ha0 hy rfl (fun κ x=>?_ ),subLocal hW.1 ha0 (eq_sub_of_add_eq hLeft.1.symm) rfl ?_⟩
  · have h' : (original H).logRead=X'.logRead+W'.logRead:= RG01.Vacuum.shelfUnion R H _
    change _= Z'.logRead+Y.logRead; rw [h',hLeft.1,hy]; abel
  · have hga : ∃ g,W'.logRead=choir g ∘ pennant H:= by unfold W' RG01.Vacuum.shelf RG01.Vacuum.weigh; dsimp only; exact ⟨_,rfl⟩
    have hgb : ∃ g,Z0.logRead=choir g ∘ pennant H:= ⟨_,rfl⟩
    obtain ⟨g,hg⟩:= hga; obtain ⟨y,hy'⟩:= hgb
    exact choirMoves (V:=Y) _ (identityX H) _ θ (by rw [hy,hg,hy']; exact sung H g y) (χ:=Chi.canonical) rfl κ x
  intro κ x; exact choirMoves (V:=Z') _ (identityX H) _ θ rfl (χ:=Chi.canonical) rfl κ x
-- buy ticket on clock
variable (h: Mallow.RG12.Earned (Thermal1020.vacuum G) R.shape A.delay)
omit hm he
include h hm
lemma certified (M:ℕ)(hM:M≤A.B.a.clock.J (m+1)):
    ∃ (C d v Y a b r B q:ℝ)(k:ℕ)(N':Captain H (σ).order C d v Y a b r B q k Chi.canonical), Receipt (Γ) (σ) M N':= by
  have h: ThermalAt _ (R.expense (i) (j)) (D.L (i)) _ _ (R.shape.o (i) (j)) _ _ _:= h (i) s0 (A.B.valid.pays m) (j) (step_paid A.B.a m)
  obtain ⟨A,a,v,t,d,w,B,q,C,k,U,hU⟩:= h.cost M hM _ _ _ _ (Opera.protocol A.B hm R.pledging.conducts.full) _ _ H
  exact ⟨C,d,v,t,A,a,w,B,q,k,U,hU⟩
end YM.GapsLocal.Vacuum
