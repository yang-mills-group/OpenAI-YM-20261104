import YM.Integration.WilsonDegreeFourInheritedRange
import YM.Integration.WilsonMatrixTicketLanesReportedAdmission

/-! The actual finite upper label pays the spatial dimension of the long
regular part of the earlier coefficient in the physical covariance. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonDegreeFourFundedTail
open Function Filter MeasureTheory Lattice RG Wilson Source Push.Local
open PhysicalNext.Repeat.Legato WilsonLimitConstruction Pert.Asymptotics WilsonInheritedRegisteredField
open scoped Classical
variable {G : Gauge} (R : Run G) (simple : G.Simple) {η : ℝ} {T : Campaign R}
  {W : Campaign.Pillars R T} (funded : FundedOriginalProperties.{u} simple η W)
local notation "β" => R.family.path.levels.clock.hatBeta

theorem quota {d k N per : ℕ} (hk : k≤N) (w : R.family.label d) (o : Site (R.family.side k per)) :
    let L := R.family.labels.level d
    let Z := packet (C:=R.family) R.makes hk w o
    L.coeffSize (L.core Z.x) ≤ Next.UVStress.quota R.family d k N per w := by
  intro L Z
  have coord := WilsonTranslatedFactory.coordinate R.makes hk o ((R.family.factory d N per).terminal.symm w)
  change Z.x = _ at coord
  rw [←show L.coeffSize Z.x = Next.UVStress.quota R.family d k N per w from congrArg L.coeffSize coord]
  exact Work.G08.size_core L Z.x

private theorem currency {k N per : ℕ} (hk : k≤N) (e q : ℕ) :
    (β k)^e*(regulatorRun R.family N per k)^(q+2*e) ≤
      (2:ℝ)^e*(regulatorRun R.family N per k)^q := by
  let g := regulatorRun R.family N per k
  let b := R.family.path.β N per k
  have bp : 0<b := Overlay.beta_positive R.makes.wilson hk
  have gp : 0≤g := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have xp : 0≤β k := zero_le_one.trans (R.family.path.levels.fits.delayed k).le
  have band : β k/2 ≤ b := (R.makes.wilson.represents N per k hk).band.1
  have cash : g^2*b=1 := by
    change (Real.sqrt b)⁻¹^2*b=1
    rw [inv_pow,Real.sq_sqrt bp.le,inv_mul_cancel₀ bp.ne']
  have price : β k*g^2≤2 :=
    (mul_le_mul_of_nonneg_right (show β k≤2*b by linarith only [band]) (sq_nonneg g)).trans_eq
      (by linarith only [cash])
  calc
    _ = (β k*g^2)^e*g^q := by rw [pow_add,pow_mul,mul_pow];ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg xp (sq_nonneg _)) price e)
      (pow_nonneg gp _)

include simple funded in
theorem fare (e q : ℕ) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ k : ℕ in atTop, ∀ N per (hk:k≤N) d (w:R.family.label d) (o:Site (R.family.side k per))
      (M:ℝ), 0≤M → Next.UVStress.quota R.family d k N per w ≤ R.family.S.a k^d*(β k^e*M) →
    let Z := packet (C:=R.family) R.makes hk w o
    let A := R.family.path.rep N per k
    let b := WilsonDegreeFourInheritedRange.height R (q+2*e) k
    ‖MergeProof.alto R.family.path k d‖*(Real.exp (-A.p.supportExponent*(b:ℝ))*
      ((R.family.path.levels.params k).columns*(R.family.labels.level d).coeffSize
        ((R.family.labels.level d).core Z.x))) ≤ ε*regulatorRun R.family N per k^q*M := by
  let l := ε/(2:ℝ)^e
  have lp : 0<l := div_pos he (by positivity)
  filter_upwards [WilsonDegreeFourInheritedRange.fee R simple funded (q+2*e) lp] with k paid
  intro N per hk d w o M nonneg cap Z A b
  let L := R.family.labels.level d
  let α := MergeProof.alto R.family.path k d
  let g := regulatorRun R.family N per k
  have size : 0≤L.coeffSize (L.core Z.x) := Finset.sum_nonneg fun _ _=>norm_nonneg _
  have actual : ‖α‖*L.coeffSize (L.core Z.x) ≤ β k^e*M := by
    calc
      _ ≤ ‖α‖*(R.family.S.a k^d*(β k^e*M)) :=
        mul_le_mul_of_nonneg_left ((quota R hk w o).trans cap) (norm_nonneg _)
      _ = _ := by
        dsimp only [α]
        rw [MergeProof.alto_norm,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ (R.family.S.a_pos k).ne'),one_mul]
  calc
    _ = (Real.exp (-A.p.supportExponent*(b:ℝ))*(R.family.path.levels.params k).columns)*
        (‖α‖*L.coeffSize (L.core Z.x)) := by ring
    _ ≤ (l*g^(q+2*e))*(β k^e*M) := mul_le_mul (paid N per hk) actual
      (mul_nonneg (norm_nonneg _) size) (mul_nonneg lp.le (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _))
    _ = l*(β k^e*g^(q+2*e))*M := by ring
    _ ≤ l*((2:ℝ)^e*g^q)*M := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (currency R hk e q) lp.le) nonneg
    _ = _ := by dsimp only [l,g];field_simp

include simple funded in
theorem measured (e q : ℕ) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ j : ℕ in atTop, ∀ N per (hk:j+1≤N), R.family.ref 4≤j+1 →
    ∀ (v w : R.family.label 4) (x : Site (R.family.side N per)) (o : Site (R.family.side (j+1) per))
      (η χ : ℂ→L[ℝ]ℝ) (V : Config G (R.family.side j per)) (M:ℝ), 0≤M →
    Next.UVStress.quota R.family 4 (j+1) N per w ≤ R.family.S.a (j+1)^4*(β (j+1)^e*M) →
    let E := actualAverage R.family (N:=N) (p:=per) (m:=j) (E:=ℝ)
    let F := fun U=>η (actualTransport R.family (N:=N) (R.family.O N per v x) hk U)
    let H := fun U=>F U-E F V
    let α := MergeProof.alto R.family.path (j+1) 4
    let b := WilsonDegreeFourInheritedRange.height R (q+2*e) (j+1)
    |E (fun U=>H U*χ (α*WilsonDegreeFourInheritedTail.tail R.makes hk w o b U)) V| ≤
      ‖χ‖*(ε*(regulatorRun R.family N per (j+1))^q*M)*E (fun U=>|H U|) V := by
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (fare R simple funded e q he)] with j rate
  intro N per hk ref v w x o η χ V M nonneg cap E F H α b
  have pay := WilsonDegreeFourInheritedTail.measured R hk ref v w x o η χ V b
  dsimp only at pay
  have cash := rate N per hk 4 w o M nonneg cap
  dsimp only at cash
  have positive : 0≤ E (fun U=>|H U|) V :=
    integral_nonneg (fun U=>mul_nonneg (actualConditionalDensity_nonneg R.family R.makes hk V U) (abs_nonneg _))
  apply pay.trans
  apply mul_le_mul_of_nonneg_right _ positive
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left cash (norm_nonneg χ)

end YM.Integration.WilsonDegreeFourFundedTail
end
