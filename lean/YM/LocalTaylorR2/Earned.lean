import YM.LocalTaylorR2.Ingress
/-!
# Output report on an actual Uses path. This comparison is in unnormalized
integrands, factored with the ACTUAL conditional denominator, common
normalization, pre-reset support/mask norm. Keep the logarithmic truncation
in the exponent rather than subtract volumes. Not an L1 claim that
exponentiating a small-in-this-norm non-normalized approximation preserves
moments in very large volumes. Regulator coupling in the error estimate
is the *actual* running coupling at the fine step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.CalendarStep
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Gas Ursell Trees Multiple OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration RG.Shoot Push.SectorMeasure Supply Input Testing Push.PriceCompiler Org
open ConnectedActivityE6.Blaze Blaze.March Captain Silica PhysicalNext PhysicalNext.Repeat Height Refrain Song
open PhysicalNext.Repeat.Greenbelt Match Roof Roost Geo Time Opera
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Progress.DirectedRecipe RG01.Vacuum Tail RG01.Survive
variable {G : Gauge}
open UVExtension Spire Orchard Mast Oasis PhysicalNext.Repeat.Legato
lemma coupling_paid {x y:ℝ}(l:ℕ)(ε:ℝ)(hε: ε≤1)(hx:1<x)(hy:y∈Set.Icc (x/2) (2*x)):
    x^(requested (l+1) ε) ≤ (Real.sqrt 2* (Real.sqrt y)⁻¹)^((l+1:ℝ)-ε) :=by
    let u:= (l+1:ℝ)-ε; have hu:0≤u:=by unfold u; linarith [Nat.cast_nonneg (α:=ℝ) l]
    have ht:0<x:=zero_lt_one.trans hx; have hz:0<y:=lt_of_lt_of_le (half_pos ht) hy.1
    have hv: (Real.sqrt x)⁻¹ ≤ Real.sqrt 2*(Real.sqrt y)⁻¹:= by
      rw [← div_eq_mul_inv,le_div_iff₀ (Real.sqrt_pos.mpr hz)]
      have h:=Real.sqrt_le_sqrt hy.2; rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤2)] at h
      rw [mul_comm,← div_eq_mul_inv, div_le_iff₀ (Real.sqrt_pos.mpr ht)]; exact h
    apply le_trans _ (Real.rpow_le_rpow (by positivity : (0:ℝ)≤(Real.sqrt x)⁻¹) hv hu)
    refine le_of_eq ?_; rw [Real.sqrt_eq_rpow,←Real.rpow_neg ht.le,← Real.rpow_mul ht.le]; congr 1; unfold u requested; push_cast; ring
variable {X: Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A) {m n N : ℕ}
variable {hG : G.Simple} (S : Uses R hG) {t:ℕ→ℕ}{B:Bid.Worth}{P:ℕ→ℝ}{Q:Bandage R P B}(L:Cellar S t Q)
set_option quotPrecheck false
local notation "C" => Cellar.yard (roseA S) L
local notation "Z" => (C).path
local notation "xF" => (Z).levels.clock.hatBeta (m+1)
local notation "oF" => A.B.a.clock.hatBeta (m+1)
local notation "gC" => Pert.Asymptotics.regulatorRun C N n (m+1)
local notation "ρ" => (C).path.rep N n m
local notation "ρf" => (C).path.rep N n (m+1)
local notation "b" => A.B.a.budget m
local notation "w" => A.B.a.clock.forcedAllowance m
local notation "j" => A.B.a.clock.J m
variable (hC:(Cellar.yard (roseA S) L).Makes)
-- Name the high terms explicitly; measures legible at Γ/est.Extraction.
variable (H: Guide A.B R.shape N m n (S.realBeat 0 N n (m+1)))
local notation "O!"=> (C).path.levels.clock.op m n
local notation "Z!" => (Song.posting (A.B.a.budget m) H)
local notation "α" => Alpha (A:=A) N m
local notation "X!"=>plusone H (RG01.Survive.identityX H) Chi.canonical (Alpha (A:=A) N m)
local notation "Ef"=>Opera.earlyFee (p:=R.expense) A.B N m (S.realBeat 0 N n (m+1)).beta
-- The `yard` path is definitionally this less dependent object too.
-- (Factored lemma for rewriting headlines, to avoid repeated unfolding.)
def spine : History G := ⟨A.B.a, fun N n m=> S.realBeat 0 N n m⟩
lemma path_eq : Z=spine R S:=rfl
include hG
structure Took (l:ℕ) (ε E:ℝ) (O:Return.Wood A.B m n) : Prop where
    calendar : Z=spine R S
    ready : ∃ (v q e t:ℝ) (y:H.ThinP→Orders l→ℝ) (z:H.ThinP→ℝ), ReadyHere R l H ε v q e t y z
    push : (A.B.a.clock.op m n).push (S.realBeat 0 N n (m+1)).beta (S.realBeat 0 N n (m+1)).eval = (S.realBeat 0 N n m).eval
    den : (S.realBeat 0 N n m).eval=coarse H O X!
    norm : (∫ V, coarse H O X! V ∂prior G _) = Wilson.partition G (A.B.a.S.side N n) ((S.realBeat 0 N n N).beta)
    pos V : 0<(S.realBeat 0 N n m).eval V
    parts : let A':= interpret R H l true; let E':=interpret R H l false; let t:= Song.weighty H Chi.canonical O
        (X!).logRead=A'.logRead+E'.logRead ∧ (X!).hardRead=A'.hardRead ∧ (X!).hardRead=E'.hardRead ∧
        coarse H O X! =coarse H O A'*exponentialShare Z! b E' ∧
        Collection.Local Z! b X! Ef w ∧ Collection.Local Z! b E' E w ∧ Collection.Local Z! b A' (Ef+E) w ∧
        Collection.vac X! t- Collection.vac A' t=Collection.vac E' 0 ∧ |Collection.vac E' 0| ≤ E ∧
        Averaging.delta ((Z!).read X!)-Averaging.delta ((Z!).read A')=Averaging.delta ((Z!).read E') ∧
        (b).threshold^2 * |Averaging.delta ((Z!).read E')| ≤ E
    graded (P0:ℕ→Prop) (i) : (∀ u,P0 u→i≤u) → i ≤ l+1 →
      Collection.Local Z! b (cohort H (χ:=Chi.canonical) (RG01.Survive.identityX H) (Alpha (A:=A) N m) (M:=l) (Candle.sprig H Chi.canonical) false P0) (oF^requested i ε) w

variable (h:Mallow.RG12.Earned (ticketD G) R.shape A.delay)
include h
omit h in
lemma priceBoundActual (l:ℕ)(hm:m<N)(ε:ℝ)(hv:ε≤1): oF^(requested (l+1) ε) ≤ ((Real.sqrt 2*gC)^((l+1:ℝ)-ε)):= by
  apply coupling_paid l ε hv (A.B.a.fits.delayed _)
  exact ((S.ticking N n (Uses.centerP _)).prices (m+1) (Nat.zero_le _) hm).2

private lemma paidBranch (l:ℕ)(ε E:ℝ) (O:Return.Wood A.B m n) (hm:m<N) (hE:oF^requested (l+1) ε ≤ E) (ha:l≤A.B.a.clock.J (m+1)) (hy:loss (A.B.a.clock.J (m+1)) ≤ ε) (hH:RG01.Vacuum.delivered S N m n H):
    let A':= interpret R H l true; let E':=interpret R H l false; let t:= Song.weighty H Chi.canonical O
        (X!).logRead=A'.logRead+E'.logRead ∧ (X!).hardRead=A'.hardRead ∧ (X!).hardRead=E'.hardRead ∧
        coarse H O X! =coarse H O A'*exponentialShare Z! b E' ∧
        Collection.Local Z! b X! Ef w ∧ Collection.Local Z! b E' E w ∧ Collection.Local Z! b A' (Ef+E) w ∧
        Collection.vac X! t- Collection.vac A' t=Collection.vac E' 0 ∧ |Collection.vac E' 0| ≤ E ∧
        Averaging.delta ((Z!).read X!)-Averaging.delta ((Z!).read A')=Averaging.delta ((Z!).read E') ∧
        (b).threshold^2 * |Averaging.delta ((Z!).read E')| ≤ E
    := by
  obtain ⟨hl,hb⟩:= (S.ticking N n (Uses.centerP _)).prices (m+1) (Nat.zero_le _) hm
  obtain ⟨hx,hx',hW,hr,hr',hA,h₀,hw⟩:=transmit R H O hH hm hl hb h l ha ε hy
  obtain ⟨hX,hV,hW',hD,hD'⟩:= mails R H O hH hm hl hb h l ha ε hy hG
  have hF : Collection.Local Z! (A.B.a.budget m) (interpret R H l false) E (A.B.a.clock.forcedAllowance m):= fullLocal hX hE le_rfl
  have hF' : Collection.Local Z! (A.B.a.budget m) (interpret R H l true) (Ef+E) (A.B.a.clock.forcedAllowance m):= fullLocal h₀ (add_le_add_right hE _) le_rfl
  exact ⟨hx,hx',hW,hr',hA,hF,hF',hD,hW'.trans hE,hD',hV.trans hE⟩

include hC
omit h in
lemma valid_spine : (spine R S).Selected := (path_eq R S L) ▸ hC.wilson
lemma weighs (l:ℕ) (ε:ℝ) (O:Return.Wood A.B m n) (hm:m<N) (hv: ε≤1) (ha:l≤A.B.a.clock.J (m+1)) (hy:loss (A.B.a.clock.J (m+1)) ≤ ε) (hH:RG01.Vacuum.delivered S N m n H):
    Took R S L H l ε ((Real.sqrt 2*gC)^((l+1:ℝ)-ε)) O := by
  let g := (Real.sqrt 2*(Real.sqrt (S.realBeat 0 N n (m+1)).beta)⁻¹)^((l+1:ℝ)-ε)
  have hw:= valid_spine R S L hC
  have hr : (S.realBeat 0 N n m).eval=(A.B.a.clock.op m n).push (S.realBeat 0 N n (m+1)).beta (S.realBeat 0 N n (m+1)).eval := (hw.steps N n m hm).1
  obtain ⟨C',d,v,t,u,a,r,B,q,y,z,p,x,θ,i,N',D'⟩:=deliver R H hm h l ha ε hy
  have hp : (S.realBeat 0 N n m).eval=coarse H O X!:=hr.trans (pressure R H O hH hm N')
  refine ⟨rfl,⟨v,q,p,x,_,_,D'⟩,hr.symm,hp,?_,Extra.Histories.Tour.bright (spine R S) hw N n m hm.le,?_,?_⟩
  · rw [← hp]; exact (spine R S).partition_eq hw N n m hm.le
  · exact paidBranch R S H h l ε g O hm (priceBoundActual (n:=n) R S L l hm ε hv) ha hy hH
  · obtain ⟨hl,hb⟩:= (S.ticking N n (Uses.centerP _)).prices (m+1) (Nat.zero_le _) hm
    obtain ⟨hx,hx',hW,hr,hr',hA,h₀,hw⟩:=transmit R H O hH hm hl hb h l ha ε hy
    exact fun t i hv hi=>hw t i hi hv

omit h hC in
lemma lasts (l r:ℕ)(ε:ℝ)(hp : 0<ε): ∀ᶠ m:ℕ in atTop, l≤A.B.a.clock.J (m+1) ∧ loss (A.B.a.clock.J (m+1)) ≤ ε ∧ r≤ (Z).levels.clock.J m ∧ r≤ ((Z).levels.budget m).order ∧ r≤ ((Z).levels.budget m).power := by
  let f(i:ℕ):= A.B.a.clock.J i; have hf:Tendsto f atTop atTop:=A.B.a.fits.deep
  obtain ⟨x,hx⟩:= exists_nat_gt ε⁻¹
  filter_upwards [hf.eventually_ge_atTop l,hf.eventually_ge_atTop r,hf.eventually_ge_atTop x] with m hm he ht
  have hU:f m≤ f (m+1):= A.B.a.fits.mono (by omega); have hY:=Q.clock.stage m
  refine ⟨hm.trans hU,?_,he,he.trans hY.1,he.trans hY.2⟩
  unfold loss; apply (inv_le_comm₀ (by positivity) hp).mpr; exact le_trans hx.le ((show (x:ℝ)≤(f (m+1):ℝ) from Nat.cast_le.mpr (ht.trans hU)).trans (le_add_of_nonneg_right zero_le_one))

/-- Including explicit unmarked reserve paid *even after one forced
divisor* and any finite extra integer hatBeta powers. -/
theorem redeemed (l r K p:ℕ)(ε:ℝ)(hε:0<ε)(hv:ε≤1):
    ∃ W':ℝ, 0≤W' ∧ ∀ᶠ m:ℕ in atTop,
    r ≤ ((C).path.levels.budget m).order ∧ r ≤ ((C).path.levels.budget m).power ∧ ∀ N n:ℕ,m<N →
       let g:=Pert.Asymptotics.regulatorRun (C) N n (m+1)
       let w':=(C).path.levels.clock.forcedAllowance m
       (0<g ∧ A.B.a.clock.hatBeta (m+1)^K*(w'/Real.sqrt w') ≤ W'*g^p) ∧
       Nonempty (Return.Wood A.B m n) ∧ (∃ H, RG01.Vacuum.delivered S N m n H) ∧ ∀ (H : Guide A.B R.shape N m n ((C).path.rep N n (m+1))), RG01.Vacuum.delivered S N m n H → ∀ O: Return.Wood A.B m n, Took R S L H l ε ((Real.sqrt 2*g)^((l+1:ℝ)-ε)) O:=by
  obtain ⟨a,ha,hA⟩:= RG01.Vacuum.Flat.currency A.B.a hG p K
  refine ⟨a,ha,?_⟩
  filter_upwards [lasts R S L l r ε hε] with m he
  refine ⟨he.2.2.2.1,he.2.2.2.2,?_⟩
  intro N n hm g w0
  obtain ⟨_,hb⟩:= (S.ticking N n (Uses.centerP _)).prices (m+1) (Nat.zero_le _) hm
  let u:=(S.realBeat 0 N n (m+1)).beta
  have hR : 0<u:= lt_of_lt_of_le (half_pos (zero_lt_one.trans (A.B.a.fits.delayed _))) hb.1
  have hw:0<w0:=Real.exp_pos _
  refine ⟨⟨inv_pos.mpr (Real.sqrt_pos.mpr hR),?_⟩, Tree.select _ (A.B.a.clock.op m n).patch.odd_side, hasGuide S hm,
    fun H hH O=> weighs R S L hC H h l ε O hm hv he.1 he.2.1 hH⟩
  rw [show w0/Real.sqrt w0=Real.sqrt w0 from (div_eq_iff (Real.sqrt_pos.mpr hw).ne').2 (Real.mul_self_sqrt hw.le).symm]; exact hA _ _ hR (Or.inl hb.2)
end YM.LocalTaylorR2.CalendarStep
