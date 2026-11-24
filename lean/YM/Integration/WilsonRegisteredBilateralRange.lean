import YM.Integration.WilsonRegisteredShortField
import YM.Integration.WilsonRegisteredAngularPair

/-! Uniform physical price of truncating both deposited rows in a single
product. Both finite conditional means continue to use the original full rows. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonRegisteredBilateralRange
open Filter Lattice RG Wilson Source MergeProof PhysicalNext.Repeat.Legato
open WilsonLimitConstruction Pert.Asymptotics WilsonInheritedRegisteredField
open WilsonRegisteredShortField WilsonRegisteredAngularPair
open private centered from YM.Integration.WilsonRegisteredAngularPair
open private currency from YM.Integration.WilsonDegreeFourFundedTail
open scoped Classical
variable {G:Gauge} (R:Run G) (simple:G.Simple) {ρ:ℝ} {T:Campaign R}
  {P:Campaign.Pillars R T} (funded:FundedOriginalProperties.{u} simple ρ P)
local notation "β"=>R.family.path.levels.clock.hatBeta

include simple funded in
theorem gross {k N per d:ℕ} (hk:k ≤ N) (ref:R.family.ref d ≤ k) (v:R.family.label d)
    (o:Site (R.family.side k per)) (b e:ℕ) {M:ℝ} (_hm:0 ≤ M)
    (cap:Next.UVStress.quota R.family d k N per v ≤ R.family.S.a k^d*(β k^e*M))
    (U:Config G (R.family.side k per)) : ‖high R.makes hk v o b U‖ ≤ (β k)^(e+1)*M := by
  let A:=R.family.path.rep N per k
  let C:=R.family
  let Z:=packet R.makes hk v o
  let α:=alto C.path k d
  let col:=(C.path.levels.params k).columns
  let size:=(C.labels.level d).coeffSize ((C.labels.level d).core Z.x)
  have non : 0 ≤ size:=Work.G08.size_nonneg _ _
  have xp : 0 ≤ β k:=zero_le_one.trans (R.family.path.levels.fits.delayed k).le
  have c1 : 1 ≤ col:=(C.path.levels.params k).columns_ge
  have cheap : Real.exp (-A.p.supportExponent*(b:ℝ)) ≤ 1:=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr A.p.exponent_pos.le) (by positivity))
  have accrued : ‖α‖*size ≤ β k^e*M := by
    calc
      _  ≤  ‖α‖*(C.S.a k^d*(β k^e*M)) := mul_le_mul_of_nonneg_left
        ((WilsonDegreeFourFundedTail.quota R hk v o).trans cap) (norm_nonneg _)
      _ = _ := by dsimp only [α];rw [alto_norm,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ (C.S.a_pos k).ne'),one_mul]
  have colSale : col ≤ β k:=funded.2.1.logBudget.money.present k
  change ‖α*_‖ ≤ _
  rw [norm_mul]
  calc
    _  ≤  ‖α‖*(Real.exp (-A.p.supportExponent*(b:ℝ))*(col*size)) :=
      mul_le_mul_of_nonneg_left (WilsonDegreeFourInheritedTail.field R.makes hk ref v o b U) (norm_nonneg _)
    _  ≤  ‖α‖*(col*size) := mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (mul_nonneg (zero_le_one.trans c1) non) cheap) (norm_nonneg _)
    _ = col*(‖α‖*size) := by ring
    _  ≤  β k*(β k^e*M) := mul_le_mul colSale accrued (mul_nonneg (norm_nonneg _) non) xp
    _ = _ := by rw [pow_succ];ring

include simple funded in
theorem original (e q:ℕ) {ε:ℝ} (he:0<ε) :
    ∀ᶠ m:ℕ in atTop,∀ N per (live:m<N) (dv dw:ℕ) (_rv:R.family.ref dv  ≤  m+1) (_rw:R.family.ref dw  ≤  m+1)
      (v:R.family.label dv) (w:R.family.label dw) (o:Fin 2→Site (R.family.side (m+1) per)) (Mv Mw:ℝ),
      0 ≤ Mv → 0 ≤ Mw →
      Next.UVStress.quota R.family dv (m+1) N per v ≤ R.family.S.a (m+1)^dv*(β (m+1)^e*Mv) →
      Next.UVStress.quota R.family dw (m+1) N per w ≤ R.family.S.a (m+1)^dw*(β (m+1)^e*Mw) →
      ∀ (η χ:ℂ→L[ℝ]ℝ) (c₁ c₂:Bool) (V:Config G (R.family.side m per)) (U:Config G (R.family.side (m+1) per)),
      let k:=m+1
      let b:=WilsonDegreeFourInheritedRange.height R (q+2*(e+1)+2*e) k
      let f:=fun X=>η (regular R.makes live v (o 0) X)
      let g:=fun X=>χ (regular R.makes live w (o 1) X)
      let a:=center R (N:=N) c₁ f V
      let z:=center R (N:=N) c₂ g V
      |(f U-a)*(g U-z)-(η (short R.makes live v (o 0) b U)-a)*(χ (short R.makes live w (o 1) b U)-z)|  ≤ 
        ε*regulatorRun R.family N per k^q*(‖η‖*‖χ‖)*(Mv*Mw) := by
  let p:=e+1
  let l:=ε/(13*(2:ℝ)^p)
  have lp:0<l:=div_pos he (by positivity)
  have sale:=WilsonDegreeFourFundedTail.fare R simple funded e (q+2*p) lp
  filter_upwards [(tendsto_add_atTop_nat 1).eventually sale] with m earn
  intro N per live dv dw rv rw v w o Mv Mw mv mw cv cw η χ ca cz V U k b f g a z
  let c:=regulatorRun R.family N per k
  let P:=β k^p
  let Q:=l*c^(q+2*p)
  let A:=f U-a
  let B:=g U-z
  let α:=η (high R.makes live v (o 0) b U)
  let γ:=χ (high R.makes live w (o 1) b U)
  have xp:0 ≤ β k:=zero_le_one.trans (R.family.path.levels.fits.delayed k).le
  have cp:0 ≤ c:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have pp:0 ≤ P:=pow_nonneg xp _
  have qp:0 ≤ Q:=mul_nonneg lp.le (pow_nonneg cp _)
  have fv X:|f X| ≤ ‖η‖*(3*P*Mv) := (η.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (WilsonRegisteredSoftCovariance.gross R simple funded live rv v (o 0) X e mv cv) (norm_nonneg _))
  have gv X:|g X| ≤ ‖χ‖*(3*P*Mw) := (χ.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (WilsonRegisteredSoftCovariance.gross R simple funded live rw w (o 1) X e mw cw) (norm_nonneg _))
  have af:|A| ≤ 2*(‖η‖*(3*P*Mv)) := centered R live ca f fv V U
  have bg:|B| ≤ 2*(‖χ‖*(3*P*Mw)) := centered R live cz g gv V U
  have arm {d:ℕ} (w:R.family.label d) (hr:R.family.ref d ≤ k) (x:Site (R.family.side k per))
      (Z:ℂ→L[ℝ]ℝ) {M:ℝ} (mp:0 ≤ M) (cash:Next.UVStress.quota R.family d k N per w ≤ R.family.S.a k^d*(β k^e*M)) :
      |Z (high R.makes live w x b U)| ≤ ‖Z‖*(Q*M) := by
    apply (Z.le_opNorm _).trans (mul_le_mul_of_nonneg_left _ (norm_nonneg _))
    rw [high,norm_mul]
    exact (mul_le_mul_of_nonneg_left (WilsonDegreeFourInheritedTail.field R.makes live hr w x b U)
      (norm_nonneg _)).trans (earn N per live d w x M mp cash)
  have afine:|α| ≤ ‖η‖*(Q*Mv):=arm v rv _ η mv cv
  have gfine:|γ| ≤ ‖χ‖*(Q*Mw):=arm w rw _ χ mw cw
  have gc:|γ| ≤ ‖χ‖*(P*Mw) := (χ.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (gross R simple funded live rw w (o 1) b e mw cw U) (norm_nonneg _))
  have cross : |A*γ+α*B-α*γ| ≤ 
      (2*(‖η‖*(3*P*Mv)))*(‖χ‖*(Q*Mw))+
      (‖η‖*(Q*Mv))*(2*(‖χ‖*(3*P*Mw)))+
      (‖η‖*(Q*Mv))*(‖χ‖*(P*Mw)) := by
    refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) ?_)
    · rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul af gfine (abs_nonneg _) (by positivity))
        (mul_le_mul afine bg (abs_nonneg _) (by positivity))
    rw [abs_mul]
    exact mul_le_mul afine gc (abs_nonneg _) (by positivity)
  have money:β k^p*c^(q+2*p) ≤ (2:ℝ)^p*c^q := currency R live p q
  have quote:13*l*((2:ℝ)^p)=ε:=by dsimp [l];field_simp
  have ident : (f U-a)*(g U-z)-(η (short R.makes live v (o 0) b U)-a)*(χ (short R.makes live w (o 1) b U)-z)=
      A*γ+α*B-α*γ := by
    change _-(η (_-_) -a)*(χ (_-_) -z)=_
    rw [map_sub,map_sub]
    dsimp only [A,B,α,γ,f,g]
    ring
  rw [ident]
  calc
    _  ≤  _ := cross
    _ = (13*l*(β k^p*c^(q+2*p)))*(‖η‖*‖χ‖)*(Mv*Mw) := by dsimp only [Q,P];ring
    _  ≤  (13*l*((2:ℝ)^p*c^q))*(‖η‖*‖χ‖)*(Mv*Mw) := by gcongr
    _ = _ := by rw [←mul_assoc (13*l),quote]

end YM.Integration.WilsonRegisteredBilateralRange
end
