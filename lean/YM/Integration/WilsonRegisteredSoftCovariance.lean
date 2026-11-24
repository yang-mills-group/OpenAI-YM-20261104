import YM.Integration.WilsonRegisteredRegularQuota

/-! Center the entire inherited regular factor in the genuine conditional
law before testing the large-support part of the second filed insertion. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonRegisteredSoftCovariance
open Function Filter MeasureTheory Lattice RG Wilson Source Push.Local MergeProof
open PhysicalNext.Repeat.Legato WilsonLimitConstruction Pert.Asymptotics WilsonInheritedRegisteredField
open private currency from YM.Integration.WilsonDegreeFourFundedTail
open scoped Classical
variable {G : Gauge} (R : Run G) (simple : G.Simple) {η : ℝ} {T : Campaign R}
  {W : Campaign.Pillars R T} (funded : FundedOriginalProperties.{u} simple η W)
local notation "β" => R.family.path.levels.clock.hatBeta

include simple funded in
theorem gross {N per k d : ℕ} (hk : k≤N) (ref : R.family.ref d≤k) (w : R.family.label d)
    (o : Site (R.family.side k per)) (U : Config G (R.family.side k per))
    (e : ℕ) {M : ℝ} (_hm : 0≤M) (cap : Next.UVStress.quota R.family d k N per w ≤
      R.family.S.a k^d*(β k^e*M)) :
    ‖regular R.makes hk w o U‖ ≤ 3*(β k)^(e+1)*M := by
  have xp : 0≤β k := zero_le_one.trans (R.family.path.levels.fits.delayed k).le
  have ap : 0<R.family.S.a k^d := pow_pos (R.family.S.a_pos k) _
  have cash : ((R.family.S.a k)^d)⁻¹*Next.UVStress.quota R.family d k N per w ≤ (β k)^e*M := by
    calc
      _ ≤ ((R.family.S.a k)^d)⁻¹*((R.family.S.a k)^d*((β k)^e*M)) :=
        mul_le_mul_of_nonneg_left cap (inv_nonneg.mpr ap.le)
      _ = _ := by rw [inv_mul_cancel_left₀ ap.ne']
  have col : (R.family.path.levels.params k).columns ≤ β k := funded.2.1.logBudget.money.present k
  calc
    _ ≤ _ := WilsonRegisteredRegularQuota.original R.makes hk ref w o U
    _ ≤ (3*(β k))*((β k)^e*M) :=
      mul_le_mul (mul_le_mul_of_nonneg_left col (by norm_num)) cash
        (mul_nonneg (inv_nonneg.mpr ap.le) (Work.G08.size_nonneg _ _)) (by positivity)
    _ = _ := by rw [pow_succ];ring

private theorem centered {N per j : ℕ} (hk : j+1≤N) (f g : Config G (R.family.side (j+1) per)→ℝ)
    {a b : ℝ} (hF : ∀U,|f U|≤a) (hG : ∀U,|g U|≤b) (V : Config G (R.family.side j per)) :
    let E := actualAverage R.family (N:=N) (p:=per) (m:=j) (E:=ℝ)
    |E (fun U=>(f U-E f V)*g U) V| ≤ (2*a)*b := by
  intro E
  have bound : ∀U,‖f U‖≤a := by simpa only [Real.norm_eq_abs] using hF
  have hf : |E f V|≤a := by
    rw [←Real.norm_eq_abs];exact actualAverage_norm_le R.family R.makes hk bound V
  rw [←Real.norm_eq_abs]
  apply actualAverage_norm_le R.family R.makes hk _ V
  intro U
  have sub : |f U-E f V|≤|f U|+|E f V| := by simpa only [Real.norm_eq_abs] using norm_sub_le (f U) (E f V)
  have delta : |f U-E f V|≤2*a := sub.trans ((add_le_add (hF U) hf).trans_eq (by ring))
  rw [Real.norm_eq_abs,abs_mul]
  exact mul_le_mul delta (hG U) (abs_nonneg _) ((abs_nonneg _).trans delta)

include simple funded in
theorem purchased (ev ew q : ℕ) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ j : ℕ in atTop, ∀ (N per : ℕ) (hk : j+1≤N) (dv dw : ℕ)
      (_rv : R.family.ref dv≤j+1) (_rw : R.family.ref dw≤j+1)
      (v : R.family.label dv) (w : R.family.label dw)
      (x y : Site (R.family.side (j+1) per)) (Mv Mw : ℝ), 0≤Mv → 0≤Mw →
      Next.UVStress.quota R.family dv (j+1) N per v ≤ R.family.S.a (j+1)^dv*(β (j+1)^ev*Mv) →
      Next.UVStress.quota R.family dw (j+1) N per w ≤ R.family.S.a (j+1)^dw*(β (j+1)^ew*Mw) →
      ∀ (η χ : ℂ →L[ℝ] ℝ) (V : Config G (R.family.side j per)),
      let k:=j+1
      let b:=WilsonDegreeFourInheritedRange.height R ((q+2*(ev+1))+2*ew) k
      let first:=fun U=>η (regular R.makes hk v x U)
      let second:=fun U=>χ (alto R.family.path k dw*WilsonDegreeFourInheritedTail.tail R.makes hk w y b U)
      let E:=actualAverage R.family (N:=N) (p:=per) (m:=j) (E:=ℝ)
      |E (fun U=>(first U-E first V)*second U) V| ≤
        ε*regulatorRun R.family N per k^q*(‖η‖*‖χ‖)*(Mv*Mw) := by
  let f:=ev+1
  let l:=ε/(6*(2:ℝ)^f)
  have lp : 0<l:=div_pos he (by positivity)
  have earlier:=WilsonDegreeFourFundedTail.fare R simple funded ew (q+2*f) lp
  filter_upwards [(tendsto_add_atTop_nat 1).eventually earlier] with j earn
  intro N per hk dv dw rv rw v w x y Mv Mw mv mw cv cw η χ V k b first second E
  let g:=regulatorRun R.family N per k
  let α:=alto R.family.path k dw
  have xp : 0≤β k :=zero_le_one.trans (R.family.path.levels.fits.delayed k).le
  have gp : 0≤g:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have a (U) : |first U|≤‖η‖*(3*(β k)^f*Mv) :=
    (η.le_opNorm _).trans (mul_le_mul_of_nonneg_left (gross R simple funded hk rv v x U ev mv cv) (norm_nonneg _))
  have hcash:=earn N per hk dw w y Mw mw cw
  have c (U) : |second U|≤‖χ‖*(l*g^(q+2*f)*Mw) := by
    apply (χ.le_opNorm _).trans (mul_le_mul_of_nonneg_left _ (norm_nonneg _))
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (WilsonDegreeFourInheritedTail.field R.makes hk rw w y b U)
      (norm_nonneg α)).trans hcash
  have sale: (β k)^f*g^(q+2*f) ≤ (2:ℝ)^f*g^q := currency R hk f q
  have quote : 6*l*((2:ℝ)^f)=ε := by dsimp [l];field_simp
  calc
    _ ≤ _ := centered R hk first second a c V
    _ = (6*l*((β k)^f*g^(q+2*f)))*(‖η‖*‖χ‖)*(Mv*Mw) := by ring
    _ ≤ (6*l*((2:ℝ)^f*g^q))*(‖η‖*‖χ‖)*(Mv*Mw) := by gcongr
    _ = _ := by rw [←mul_assoc (6*l),quote]

end YM.Integration.WilsonRegisteredSoftCovariance
end
