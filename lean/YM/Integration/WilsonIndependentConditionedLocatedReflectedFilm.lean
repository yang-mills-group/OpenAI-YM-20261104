import YM.Integration.WilsonIndependentConditionedLocatedBulbMoney
import YM.Integration.WilsonIndependentConditionedLocatedFold
import YM.Integration.WilsonIndependentConditionedLocatedOptics

/-! The signed finite physical/independent reflected film at the genuine
spatial ruler, with its original admission purchased before the regulator. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedLocatedReflectedFilm
open Function Filter Set MeasureTheory Metric Lattice Extraction Wilson
open RG12 Cells Push.GridApprox Trace.Physical.GermGraph RG16 RG16.Literal
open Maxwell XSpace XSpace.Cirrus Table.Pairing WilsonMaxwellThermometerReflectedIncidence
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Embroider WilsonCoeffUV.Layout
open WilsonIndependentConditionedFolioStations (ports)
open WilsonIndependentConditionedGramBulbProfile (chart profile)
open WilsonIndependentConditionedGramSpatialCourse (Page)
open WilsonIndependentConditionedGramSpatialHost (date)
open WilsonIndependentConditionedLocatedBulbMoney (ruled mode)
open WilsonIndependentConditionedLocatedFold (film folded)
open WilsonCenteredCompactBooking (mass)
open scoped Classical Topology ContDiff BigOperators
variable {a:Axis}{x:E4}(B:Bulb (site x) a){G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)

def weight {A s r:ℝ}(h:1≤r/s)(D E:ℕ)(z:CellR)(o:Fin 2→ Cover):ℂ:=
  (((A/s)^4*(farther h (profile B D true)).ψ.val (Mer.position (A/s) 0 z (o 0)))*
    ((A/s)^4*(farther h (profile B E false)).ψ.val (Mer.position (A/s) 0 z (o 1))):ℝ)

theorem cell {A s r:ℝ}(hs:0<s)(hr:0<r)(h:1≤r/s)(D E:ℕ)(z:CellR)(o:Fin 2→ Cover):
    weight B (A:=A) h D E z o = (((A/r)^8:ℝ):ℂ)*mode B D E (A/r) o:=by
  unfold weight mode
  rw [ruled _ hs hr h,ruled _ hs hr h]
  norm_cast
  ring

theorem original (simple:G.Simple){t:ℕ}(ht:0<t):
    ∃ψ:Test 2,∃C:ℝ,0≤C ∧ (∀y,0≤(ψ y).re) ∧
    ∀ᶠr:ℝ in 𝓝[>] 0,∀{m f K U p:ℕ}{ε:ℝ},m=date R simple r →
      ∀page:Page R r m f K t U p ε,∀(per D E:ℕ),∀z:CellR,
        let w:=weight B (A:=R.family.S.a K) page.root_one D E z
        (∀o:Fin 2→ Cover,w o≠0 → mass R ψ r (K,per) (wrap _ ∘ o)≠0) ∧
        ∀L H:Finset Cover,
           (∑n∈L,∑q∈H,‖w (ports n q)‖)≤C ∧
           (∑y,‖folded (film L H) (fun o=>wrap (R.family.side K per) ∘ o) w y‖)≤C:=by
  obtain ⟨ψ,σ,sp,pos,opened⟩:=WilsonIndependentConditionedLocatedBulb.original B G
  obtain ⟨C,cp,cost⟩:=WilsonIndependentConditionedLocatedBulbMoney.original B
  refine ⟨ψ,C,cp,pos,?_⟩
  filter_upwards [WilsonIndependentConditionedLocatedOptics.original R simple ht (lt_min sp zero_lt_one)] with r tiny
  intro m f K U p ε named page per D E z w
  let δ:=R.family.S.a K/r
  have dp:0<δ:=div_pos (R.family.S.a_pos _) page.positive
  have mesh:8*δ < min σ 1:=by simpa only [show (4:ℝ)*2=8 by norm_num] using tiny named page
  have point(o:Fin 2→ Cover):w o=((δ^8:ℝ):ℂ)*mode B D E δ o:=
    cell B (R.family.S.a_pos _) page.positive page.root_one D E z o
  constructor
  · intro o atSite
    rw [point] at atSite
    apply opened R page.positive (K,per) D E (mesh.le.trans (min_le_left ..)) o
    intro zero
    apply atSite
    apply mul_eq_zero_of_right
    unfold mode
    exact_mod_cast zero
  · intro L H
    have cover:=cost dp (mesh.le.trans (min_le_right ..)) D E (film L H)
    have signed:(∑n∈L,∑q∈H,‖w (ports n q)‖)≤C:=by
      rw [←(WilsonIndependentConditionedLocatedFold.two L H (fun o=>‖w o‖))]
      simpa only [point] using cover
    exact ⟨signed,(WilsonIndependentConditionedLocatedFold.paid ..).trans signed⟩
end YM.Integration.WilsonIndependentConditionedLocatedReflectedFilm
end
