import YM.RGLocalTaylor.Consumer.Power
import YM.RG12.Burst.Cotton

/-!
# Producer to RG01.Survive.coupling

Keep the author's arbitrary-curvature/arbitrary-history rendering (`logAt`),
and its full register, denominator and scalar/path conventions. Narrow only for
this adapter; the underlying leaf license extends over all branches. Uniform in
arbitrary periods, histories and budgets **on the purchased construction**,
as a price on the E6 supported derivative norm BEFORE kinetic reset. Hard K
paid at physical reserved `forcedAllowance`. This file is for the unmarked
sector. No claim of true-coupling Taylor of the path kernels/forced vacuum nor
a bound independent of the term count (d powers requested consumes sufficiently
many Mayer moments, `7*(r+1) ≥ 8*d`, and all supplies including inherited
E remain those of this genuine history). No witness-matching across versions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor.Consumer
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration RG.Shoot Push.SectorMeasure Supply Input Testing Push.PriceCompiler Org
open ConnectedActivityE6.Blaze Blaze.March Captain Silica PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Height Refrain Song
open PhysicalNext.Repeat.Greenbelt Match Roof Roost Geo Time Opera PhysicalNext.Repeat.Legato
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open RG01 RG01.Survive Daisy.Charity.RG12
variable {G : Gauge} {X : Metals G} {D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}
    {m N n : ℕ} {u : RG.Rep G (A.B.a.S.side (m+1) n)} (H:Guide A.B R.shape N m n u)
    (O:Return.Wood A.B m n)

local notation "B!" => (A.B.a.budget m)
local notation "b" => (A.B.a.clock.hatBeta m)
local notation "J0" => A.B.a.clock.J (m+1)
local notation "P0" => (X.p.profile (A.B.a.clock.J m))
local notation "Γ" => R.expense (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)
local notation "y" => (A.B.a.clock.hatBeta (m+1))
local notation "L" => D.L (A.B.a.clock.J (m+1))
local notation "T0" => Chi.canonical
set_option quotPrecheck false
local notation "δ" => Height.asset Γ
local notation "capa" => Mayer.arcRadius G L b
local notation "F0" => H
variable (hH: Opera.Price A.B R.shape N m n u H) (hm:m<N) (hl : RG.Shoot.Lives A.B.bake N (m+1) n u) (hb: u.beta∈ RG.Shoot.band A.B.a (m+1))

-- price at presentation exactly as evaluated and includes non-analytic
-- selectors; accompany EBound with its smooth witnesses in the collimated
-- log & forced representation. `Passport` also provides explicit estimates
-- for the pre-orbit expansions. Output `ReaderCost` is at actual β.
variable {M p : ℕ}
lemma gate (ζ : Mallow.RG12.Earned (Mayer.decal G) R.shape A.delay)
    (hr : M ≤ J0) (hm:m<N): ∃ w, Mayer.Passport H (Γ).earn w (Height.away P0) (δ) (P0).order (P0).power M := by
  let ξ:= A.B.a; let j:= A.B.a.clock.J m
  obtain ⟨w,hV⟩:= ζ J0 b (A.B.valid.pays m) j (step_paid A.B.a m) M hr
  exact ⟨w,hV _ _ _ _ (Opera.protocol A.B hm R.pledging.conducts.full) u _ H⟩

variable (M)
local notation "tx" => Mayer.issue H Chi.canonical M
abbrev report := standard H
abbrev remainder : Collection.Source G (A.B.a.S.side m n) := fusedError (R:=R) (H:=H) («x»:= Mayer.issue H Chi.canonical M)
abbrev truncated : Collection.Source G (A.B.a.S.side m n) := logAt H M (Mayer.issue H Chi.canonical M) true
abbrev gross (k : ℕ) := Vacuum.importedTail R H k

structure Issued01 (H : Guide A.B R.shape N m n u) (O:Return.Wood A.B m n) (M : ℕ) (z : ℝ) : Prop where
  allClusters : ∃ w:ℝ, Mayer.Passport H (Γ).earn w (Height.away P0) (δ) (P0).order (P0).power M
  value : (A.B.a.clock.op m n).push u.beta u.eval = coarse H O (truncated H M) * Vacuum.exponentialShare (standard H) (A.B.a.budget m) (remainder H M)
  aligned : (plusone H (identityX H) Chi.canonical (A.B.kin.alpha N m)).logRead=(truncated H M).logRead+(remainder H M).logRead
  regular : ∀ i, (B!).Regular ((standard H).reg i).support ((remainder H M).logRead i) ∧ (B!).Regular ((standard H).reg i).support ((truncated H M).logRead i)
  hard : ((standard H).read (remainder H M)).ForcedFamily (B!)
  priced : ((standard H).read (remainder H M)).EBound (B!) z ∧ ((standard H).read (remainder H M)).KBound (B!) (A.B.a.clock.forcedAllowance m) ∧
    (truncated H M).hardRead=(remainder H M).hardRead ∧ (remainder H M).hardRead=(plusone H (identityX H) Chi.canonical (A.B.kin.alpha N m)).hardRead

include hH hm hl hb
lemma delivered (he:∃ w,Mayer.Passport H (Γ).earn w (Height.away P0) (δ) (P0).order (P0).power M)
    {c : ℝ} (hK:Real.exp (-(Vacuum.cashMark R m))*Vacuum.voucher (A:=A) m^3 ≤ c*((Real.sqrt u.beta)⁻¹)^(M+1)) :
    let price:=(Real.sqrt 2^(M+1)+c)*(Real.sqrt u.beta)⁻¹^(M+1)
    Issued01 H O M (price + (capa^(M+1))⁻¹) := by
  intro p'
  obtain ⟨w,hω⟩:=he
  let hω' := hω
  obtain ⟨Aa,a',C,d,v,t,r,B,q,e,K,θ,uJ,vJ,k,l,N',hθ,hΓ,hV,hp,hc⟩:= hω'
  let fee:= readerCost (G:=G) B! (P0).order (P0).power capa (δ) b w (1/2) (M+1)
  have hr:(B!).order=(P0).order:=Rain.jersey (A:=A) (m:=m)|>.1
  have hu:(B!).power=(P0).power:=Rain.jersey (A:=A) (m:=m)|>.2.1
  have hw:(B!).supportExponent=(P0).supportExponent:= Rain.jersey (A:=A) (m:=m)|>.2.2.1
  have hi : preExponent (B!) ≤ (Γ).earn:= by unfold preExponent; rw [hw]; exact R.pledging.agenda _ _ (step_paid A.B.a m)|>.1
  have hS : Sailor G (B!).threshold q (P0).order:= ⟨fun c g hb=> N'.weigh.stroke c g (hb.trans N'.talent)⟩
  have hP := RG01.Survive.coupling H O hH hm hl hb (hp.ready ..) hr.le hu.le q N'.income hS N'.near N'.position hi (Height.asset_pos ..) hp.agrees hK
  obtain ⟨hT,hB,hF⟩:= hP
  have hδ : fee ≤ (capa^(M+1))⁻¹ := by
    unfold fee readerCost; rw [mul_left_comm, Rain.jersey (A:=A) (m:=m)|>.2.2.2]; exact mul_le_of_le_one_right (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hp.scale) _)) hc
  have he' : ((standard H).read (remainder H M)).EBound (B!) (p'+(capa^(M+1))⁻¹):=
    VerifiedReset.Time.E_rises hB (add_le_add_right hδ _) -- check direction
  let T:= tx; let S:= standard H; let K0:= gradeCap (M+1); let H0:= lengthCap (A:=A) (m:=m) (M+1)
  let Ae := identityX H; let D':=Vacuum.importedTail R H (M+1); let E:=Vacuum.shelf R H D' true; let F:=Vacuum.shelf R H D' false
  have hf:= Vacuum.rare R H O hH hm hl hb (M+1) hK; unfold Vacuum.Decision at hf; dsimp only at hf
  have hEq:F= remain H (χ:=Chi.canonical) Ae K0 H0 (A.B.kin.alpha N m):= by
    unfold F D' Vacuum.shelf RG01.Survive.remain; congr! 2
    rename_i z
    unfold H0 K0; by_cases hv:Vacuum.importedTail R H (M+1) z
    · simp [Vacuum.chooseMark,hv,(complement H z (M+1)).not.mpr (not_not.mpr hv)]
    simp [Vacuum.chooseMark,hv,(complement H z (M+1)).mpr hv]
  let Y0:= logAt H M T false; let X':=truncated H M; let P':= B!
  let γ:= A.B.kin.alpha N m
  have W := RG01.Survive.survival H (hp.ready K0 H0) Ae γ P' rfl rfl hr.le (B!).power (le_refl _) q N'.income hS N'.near N'.position hi (Height.asset_pos ..) hp.agrees M le_rfl (hEq ▸ (show Collection.Local S B! F _ _ from hf.1)) (A.B.kin.path N m) (A.B.a.params m).clip u.beta (weighty H Chi.canonical O) γ -- hc powers not needed
  change (remain H (χ:=Chi.canonical) Ae K0 H0 γ).logRead=X'.logRead+Y0.logRead ∧ _ at W; rw [← hEq] at W
  have hw : (plusone H Ae Chi.canonical γ).logRead= X'.logRead + (remainder H M).logRead:=by
    rw [show (plusone H Ae Chi.canonical γ).logRead= F.logRead+E.logRead from Vacuum.shelfUnion R H .., W.1]; change _= X'.logRead+ (E.logRead+Y0.logRead); abel
  refine ⟨⟨w,hω⟩,hT,hw,?_,⟨hf.2.1.family.sym, hf.2.1.family.symtest, hf.2.1.family.meas,hf.2.1.family.meas_test,hf.2.1.family.reads,hf.2.1.family.reads_test,hf.2.1.family.permit⟩, he',hF,rfl,rfl⟩ -- hω consumed
  intro i
  let q:= (S.reg i).support
  have hΩ : (B!).Regular q (Y0.logRead i):= W.2.2.2.1.smooth i
  have hg:F.logRead i=X'.logRead i + Y0.logRead i:=congr_fun W.1 i
  change P'.Regular q (E.logRead i+Y0.logRead i) ∧ P'.Regular q (X'.logRead i)
  constructor
  · have he:= CouplingShape.reg_sub (hf.2.1.smooth i) (CouplingShape.reg_scale (-1) hΩ); simpa only [neg_one_smul,sub_neg_eq_add] using he
  rw [show X'.logRead i=F.logRead i- Y0.logRead i by rw [hg]; abel]; exact CouplingShape.reg_sub (hf.1.smooth i) hΩ

end YM.RGLocalTaylor.Consumer
