import YM.Frontier6.Bouquet.Garland.Open
import YM.Integration.WilsonMaxwellThermometerWardCoefficient
import YM.Integration.WilsonMaxwellThermometerWardOrbitStation

/-! Read the true equation on its earned section with a real or imaginary
polarization. Its scalar and its first occupied finite inversion coefficient
vanish at the same location and regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerWardCredit
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels Source Push
open PertExtension PertExtension.Orb PertExtension.Orb.SlotEvaluation PertExtension.Series
open Chart Series.Radial Series.Tested WilsonMaxwellThermometerWardPupil
open WilsonMaxwellThermometerWardConditional WilsonMaxwellThermometerWardReflection
open WilsonMaxwellThermometerWardOrbitStation
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge} {n:Side}

theorem scalar (even:Even n.val) (a:ℝ) (t:ℝ):preExpectation (fun _:Config G n=>a) t=a:=by
  have one:=preNum_one_pos (G:=G) (n:=n) (t:=t) even
  change preNum _ t / preNum _ t = a
  apply (div_eq_iff one.ne').2
  unfold preNum
  simp only [Pi.one_apply,one_mul,integral_const_mul]

theorem normalize {f:Config G n→ℂ} (hf:Continuous f) {K:Config G n→ℝ}
    (hk:Continuous K) (L:ℂ→L[ℝ]ℝ) (t:ℝ)
    (paid:(∫q:OEdge n→G.El,(preDensity t (liftLinks q):ℂ)*
       (f (liftLinks q)*(K (liftLinks q):ℂ)) ∂WilsonMaxwellThermometerWardConditional.law G)=0):
    preExpectation (fun X=>L (f X)*K X) t=0:=by
  let tariff:=fun q:OEdge n→G.El=>(preDensity t (liftLinks q):ℂ)*(f (liftLinks q)*(K (liftLinks q):ℂ))
  have hu:Continuous (liftLinks : (OEdge n→G.El) → Config G n):=lift_cont _
  have hw:Continuous (preDensity (G:=G) (n:=n) t) := Real.continuous_exp.comp (((energy_cont.div_const 2).neg).div_const (t^2))
  have ht:Continuous tariff:=((Complex.continuous_ofReal.comp hw).mul (hf.mul (Complex.continuous_ofReal.comp hk))).comp hu
  have hm:=L.integral_comp_comm (μ:=WilsonMaxwellThermometerWardConditional.law G)
    (ht.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have literal (q:OEdge n→G.El):
      L (tariff q)=(L (f (liftLinks q))*K (liftLinks q))*preDensity t (liftLinks q):=by
    let X:=liftLinks q
    have eq:tariff q=(preDensity t X * K X) • f X:=by
      change (↑(preDensity t X):ℂ)*(f X*↑(K X))=_
      rw [Complex.real_smul,Complex.ofReal_mul]; ring
    rw [eq,map_smul,smul_eq_mul]; dsimp only [X]; ring
  change _ / _ = 0
  have raw: preNum (fun X=>L (f X)*K X) t=0:=by
    unfold preNum
    simp_rw [←literal]
    change (∫q:OEdge n→G.El,L (tariff q) ∂WilsonMaxwellThermometerWardConditional.law G)=0
    rw [hm]
    change L (∫q:OEdge n→G.El,(preDensity t (liftLinks q):ℂ)*
       (f (liftLinks q)*(K (liftLinks q):ℂ)) ∂WilsonMaxwellThermometerWardConditional.law G)=0
    rw [paid,map_zero]
  rw [raw,zero_div]

variable {d:ℕ} {F:Frame G d} (C:SectionData F) (c:F.Coeff) (L:ℂ→L[ℝ]ℝ)
    (o:Site n) {H:Hol G} (sound:C.Sound H) (pop:Bid.pop C)
local notation "full" => (fun U:Config G n=>L (C.places c o U))
local notation "raw" => selected C c L o (active (F:=F))
local notation "head" => selected C c L o (next (F:=F))

include sound pop in
theorem ground (even:Even n.val) (simple:G.Simple)
    (paid:∀t:ℝ,t≠0→preExpectation full t=0) :
    L (c 0)=0 ∧ diagonalWith (tray G) (restrictedO head) 2=0 :=by
  have un:full=(fun _:Config G n=>L (c 0))+raw:= funext (literal C c L o sound)
  have money:=WilsonMaxwellThermometerWardCoefficient.extraction C c L o sound pop even simple
  have priced:=WilsonMaxwellThermometerWardCoefficient.addition (fun _:Config G n=>L (c 0)) raw
    continuous_const (WilsonMaxwellThermometerWardCoefficient.admitted C c L o sound pop _).continuous
  have withdrawn:preExpectation raw =ᶠ[Tested.germ] fun _=> -(L (c 0)) := by
    filter_upwards [eventually_pos] with t ht
    have zero:=paid t ht.ne'
    rw [un,priced,Pi.add_apply,scalar even] at zero
    linarith
  have left:L (c 0)=0:=by
    have uniq:=tendsto_nhds_unique money.2.1 (tendsto_const_nhds.congr' withdrawn.symm)
    linarith
  refine ⟨left,?_⟩
  have gone : (fun t:ℝ=>t⁻¹^2*preExpectation raw t)=ᶠ[Tested.germ] fun _=>0 := by
    filter_upwards [withdrawn] with t zero
    simp [zero,left]
  exact tendsto_nhds_unique money.2.2 (tendsto_const_nhds.congr' gone.symm)

end YM.Integration.WilsonMaxwellThermometerWardCredit
