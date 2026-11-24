import YM.Integration.WilsonAddressedFiniteGuardFields
import YM.Integration.WilsonOriginalMicroscopicEntranceOpticalUnits
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAddressedFiniteGuardCapital
open Function Finset Lattice Wilson RG Source Labels Extra.Histories Extra.Multi Push.AbsoluteSums.Animals
open PhysicalNext.Repeat.Legato
open WilsonOriginalMicroscopicGuardedWallet (loss)
open WilsonOriginalMicroscopicEntranceOpticalUnits (dye rank)
open WilsonAddressedFiniteGuardFields (cap)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)
local notation "CF" => R.family
local notation "H" i:max => (CF).path.levels.clock.hatBeta i
private theorem material (d K:ℕ):loss R d K ≤ dye R d*(H K)^(rank R d):=by
  have β:1 ≤ H K:=((CF).path.levels.fits.delayed K).le
  have price:0 ≤ BasisCost.price ((CF).localSection d):=zero_le_one.trans (BasisCost.price_pos _)
  apply mul_le_mul_of_nonneg_left _ (by change 0 ≤ 1+BasisCost.price ((CF).localSection d);linarith)
  have th:((CF).path.levels.budget K).threshold⁻¹ ≤ H K:=by
    rw [←min_eq_left ((CF).path.levels.budget K).threshold_le]
    exact WilsonOriginalCoordinateExposure.threshold R K
  exact pow_le_pow_left₀ ((zero_le_one:0 ≤ (1:ℝ)).trans (le_max_left ..)) (max_le β th) _


variable {I:Type}(d:I → ℕ)
def price (B:ℝ)(s:Finset I):ℝ:=2*∏j∈s,dye R (d j)*B
def power (e:ℕ)(s:Finset I):ℕ:=∑j∈s,(rank R (d j)+e)
def count (s:Finset I):ℕ:=∑j∈s,(R.family.localSection (d j)).stencil.card

theorem count_bound {p K:ℕ}(o:I → Site (R.family.side K p))(s:Finset I):
    (WilsonAddressedFiniteGuardFields.footprint R d p K o s).card ≤ count R d s:=
  Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _=>Finset.card_image_le)

theorem price_nonneg {B:ℝ}(bp:0 ≤ B)(s:Finset I):0 ≤ price R d B s:=by
  apply mul_nonneg (by norm_num)
  apply Finset.prod_nonneg
  intro j _
  exact mul_nonneg (by change 0 ≤ 1+BasisCost.price _;have h:=BasisCost.price_pos ((CF).localSection (d j));linarith) bp

theorem original {N p K:ℕ}(live:K ≤ N)(v:∀j:I,(CF).label (d j)){B:ℝ}(_bp:0 ≤ B)(e:ℕ)
    (income:∀j,((CF).labels.level (d j)).coeffSize (v j) ≤ B*(H K)^e)(s:Finset I):
    2*(∏j∈s,cap R d N p K v j) ≤ price R d B s*(H K)^(power R d e s):=by
  let h:=H K
  have hp:0 ≤ h:=zero_le_one.trans ((CF).path.levels.fits.delayed K).le
  have cap_pos(j:I):0 ≤ cap R d N p K v j:=
    (norm_nonneg _).trans (((WilsonAddressedFiniteGuardFields.unary R d N p K (fun _=>0) v j).2.2 1).1)
  have each(j:I):cap R d N p K v j ≤ (dye R (d j)*B)*h^(rank R (d j)+e):=by
    apply (WilsonAddressedFiniteGuardFields.budget R d N p K v live j).trans
    have scaled:=mul_le_mul (material R (d j) K) (income j)
      (show 0 ≤ ((CF).labels.level (d j)).coeffSize (v j) from Finset.sum_nonneg (fun _ _=>norm_nonneg _))
      (mul_nonneg (show 0 ≤ dye R (d j) from by unfold dye;have h:=BasisCost.price_pos ((CF).localSection (d j));linarith)
        (pow_nonneg hp _))
    apply scaled.trans_eq
    dsimp [h]
    rw [pow_add]
    ring
  calc
    _ ≤ 2*(∏j∈s,(dye R (d j)*B)*h^(rank R (d j)+e)):=mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod (fun j _=>cap_pos j) (fun j _=>each j)) (by norm_num)
    _=_:=by rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum];unfold price power h;ring

end YM.Integration.WilsonAddressedFiniteGuardCapital
end
