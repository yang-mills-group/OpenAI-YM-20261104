import YM.Integration.WilsonSeparatedPrefixMovingCohorts

/-! The two own-date profiles describe the same fine bonds. SplitHill is
earned here on the genuine parent sites of their nonzero quadrature terms. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingLenses
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open scoped BigOperators Topology Classical

theorem address_scale (T x y:ℝ)(o:CellR)(a:Cover)(p:Point4)(pos:0<T):
    T • address (x/T) (y/T) o a p=address x y o a p:=by
  unfold Mer.address Mer.position
  rw [smul_add,smul_sub,smul_smul,smul_smul,smul_smul]
  simp only [mul_div_cancel₀ _ pos.ne']

private theorem roof (L:Side){S:Finset Cover}(held:S.Nonempty)(η K:ℝ)(pos:0≤η)(small:η≤1)
    (homes:∀a∈S,η*(Bank.terrain.gap 0 (parentC L a):ℝ)≤K)(i:Cover):
    η*(Bank.terrain.gap 0 i:ℝ)≤K+saddleP L S i:=by
  obtain ⟨a,ha,spread⟩:=summitT L held i
  rw [spread]
  have tri:(Bank.terrain.gap 0 i:ℝ)≤(Bank.terrain.gap 0 (parentC L a):ℝ)+
      (Bank.terrain.gap (parentC L a) i:ℝ):=by exact_mod_cast Bank.terrain.tri 0 (parentC L a) i
  have stretched:=mul_le_mul_of_nonneg_left tri pos
  rw [mul_add] at stretched
  exact stretched.trans (add_le_add (homes a ha) (mul_le_of_le_one_left (by positivity) small))

/-- Different home rulers, including the common displaced cell. Each occupied
site is its original fine-grid site. -/
theorem original {nearD farD:ℕ}(P:Patch)(φ:Rarity nearD)(ψ:Rarity farD)
    (x y T gap zNear zFar:ℝ)(o:CellR)(positive:0<x)(zoom:1≤T)
    (fit:x*P.L.val≤1)(distanced:0<gap)
    (separated:∀a∈tsupport φ.ψ.val,∀b∈tsupport ψ.ψ.val,gap≤dist a (T • b))
    (nearBox:radiusH φ (x*P.L.val) y≤zNear)
    (farBox:radiusH ψ ((x/T)*P.L.val) (y/T)≤zFar)
    (nearLive:(VisitsT φ x y o).Nonempty)(farLive:(VisitsT ψ (x/T) (y/T) o).Nonempty):
    let η:=x*P.L.val
    let H:=4*max zNear (T*zFar)
    SplitHill (saddleP P.L (VisitsT ψ (x/T) (y/T) o)) (saddleP P.L (VisitsT φ x y o))
      η H (gap/η):=by
  intro η H
  have tp:0<T:=zero_lt_one.trans_le zoom
  have ep:0<η:=mul_pos positive (by exact_mod_cast P.L.pos)
  have opt:0<x/T:=div_pos positive tp
  have outer:η/T=x/T*P.L.val:=by dsimp only [η];ring
  have oh:1≤H:=by
    have zr:1≤zNear:=(fieldCap φ (x*P.L.val) y).trans nearBox
    dsimp only [H];linarith [le_max_left zNear (T*zFar)]
  have localNear(a:Cover)(ha:a∈VisitsT φ x y o): η*(Bank.terrain.gap 0 (parentC P.L a):ℝ)≤H:=by
    have v:=reachFit φ η y o ep _ (visita P φ x y o positive a ha)
    exact v.trans (mul_le_mul_of_nonneg_left (nearBox.trans (le_max_left ..)) (by norm_num))
  have localFar (a:Cover)(ha:a∈VisitsT ψ (x/T) (y/T) o):
      η*(Bank.terrain.gap 0 (parentC P.L a):ℝ)≤H:=by
    have pos:0<(x/T)*P.L.val:=mul_pos opt (by exact_mod_cast P.L.pos)
    have v:=reachFit ψ ((x/T)*P.L.val) (y/T) o pos _
      (visita P ψ (x/T) (y/T) o opt a ha)
    rw [←outer] at v
    calc
      η*(Bank.terrain.gap 0 (parentC P.L a):ℝ)=
        T*((η/T)*(Bank.terrain.gap 0 (parentC P.L a):ℝ)):=by field_simp [tp.ne']
      _≤T*(4*zFar):=mul_le_mul_of_nonneg_left
        (v.trans (mul_le_mul_of_nonneg_left (outer ▸ farBox) (by norm_num))) tp.le
      _≤H:=by dsimp only [H];nlinarith only [le_max_right zNear (T*zFar)]
  refine ⟨angleC _ farLive,angleC _ nearLive,oh,div_pos distanced ep,ep.le,fit,
    roof P.L farLive η H ep.le fit localFar,roof P.L nearLive η H ep.le fit localNear,?_⟩
  intro d e
  obtain ⟨a,ha,h⟩:=summitT P.L farLive d
  obtain ⟨b,hb,f⟩:=summitT P.L nearLive e
  have reach:gap/η≤1+(Bank.terrain.gap (parentC P.L a) (parentC P.L b):ℝ):=by
    obtain ⟨A,active⟩:=featureV ψ (η/T) (y/T) o (parentC P.L a)
      ((visiting (div_pos ep tp)).mp (outer ▸ visita P ψ (x/T) (y/T) o opt a ha))
    obtain ⟨B,lit⟩:= featureV φ η y o (parentC P.L b)
      ((visiting ep).mp (visita P φ x y o positive b hb))
    have far:=separated _ lit _ active
    rw [address_scale T η y o _ _ tp,dist_comm] at far
    apply (div_le_iff₀ ep).mpr
    rw [mul_comm]
    exact far.trans (orbital η y o (parentC P.L a) (parentC P.L b) A B ep)
  rw [h,f,Bank.terrain.swap (parentC P.L b) e]
  apply reach.trans
  simp only [add_assoc]
  apply add_le_add_right
  exact_mod_cast ((Bank.terrain.tri (parentC P.L a) d (parentC P.L b)).trans
    (Nat.add_le_add_left (Bank.terrain.tri d e (parentC P.L b)) _))

end YM.Integration.WilsonSeparatedPrefixMovingLenses
