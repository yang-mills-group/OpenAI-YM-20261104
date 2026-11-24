import YM.Integration.WilsonThermometerOffsetGraphColumn

/-! A reversible singleton transfer on one chosen physical child, with the
old signed graph and the original divided forced allowance on both dates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOffsetGraph
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Copper
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {C:Family G} {N m p d:ℕ}
    {D:GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "L" => C.S.block m
local notation "I" => Palette C d
local notation "J" => Mark C d
local notation "M" => C.path.rep N p (m+1)
local notation "R" => C.path.rep N p m
local notation "O" => Bud C p m

def placed (u : billStart C p m N) (b : O) :
    Tape G (C.side (m+1) p) →ₗ[ℂ] Tape G (C.side (m+1) p) where
  toFun F := (orient u F b).comp (Native.pull (displacement C p m b) ((L).val:ℝ)⁻¹)
  map_add' _ _ := by rw [orient, LinearMap.comp_add, LinearMap.add_comp];rfl
  map_smul' _ _ := by rw [orient, LinearMap.comp_smul, LinearMap.smul_comp];rfl

structure Transfer (h : C.Makes) (hm : m<N) (b : O)
    (V : I →ₗ[ℂ] Tape G (C.side (m+1) p)) (W : I →ₗ[ℂ] Tape G (C.side m p))
    (r : I ≃ₗ[ℂ] I) : Prop where
  payment (x : I) : size (amplify d C L x) ≤ ld C.path.levels m*size (r x) ∧
    size (r x) ≤ ld C.path.levels m*size (amplify d C L x)
  travel (x : I) : Travel C N m p d (child C p m b) D
    (placed (keys0 h hm) b (V x)) (W (r x)) (ld C.path.levels m*size (amplify d C L x))

theorem step (h : C.Makes) (hm : m<N) {B B' : ℝ} {V : I →ₗ[ℂ] Tape G (C.side (m+1) p)}
    (hc : SignedPrice C m p d N D B B') (H : Group C N (m+1) p d V B) (b : O) :
    ∃ (W : I →ₗ[ℂ] Tape G (C.side m p)) (r : I ≃ₗ[ℂ] I),
      Group C N m p d W B' ∧ Transfer (D:=D) h hm b V W r := by
  obtain ⟨s,K,c,β,T,Q,plot,turns,_,_,fare,two,hQ,clip,small,within⟩ := hc.author
  let α := Doors.rate L
  let γ := trim L+oldCost d K*α
  let t := beamCost d c K
  let δ := 2*tollP d K c β+tollV d L K c α β*shiftFee (M).p*B
  choose P w z cap form ride low using
    WilsonThermometerOffsetGraphColumn.received (u:=keys0 h hm) plot h hm H turns b
  let A : I →ₗ[ℂ] I := (slide_linear z).mk' _
  have contour : Contour C m d t c γ A := sails_now plot cap low
  have hK := zero_le_one.trans plot.cursor.fits
  have hc0 := zero_le_one.trans plot.posp
  have hm0:0 ≤ margin d c K := mul_nonneg (add_nonneg (sCpos hK) (aCpos hK)) hc0
  have ht : 0 ≤ t := by change 0 ≤ margin d c K+1+c; linarith
  have o0 : 0 ≤ oldCost d K := by unfold oldCost; positivity
  have ha : 0≤α := plot.a_pos
  have hγ : 0 ≤ γ := add_nonneg (lit L).le (mul_nonneg o0 ha)
  have rate (x:I) := contour.earns ht plot.posp hγ clip hQ small x
  have inj : Injective A := by
    apply LinearMap.ker_eq_bot.mp
    refine LinearMap.ker_eq_bot'.mpr fun x hx => ?_
    have small := (rate x).1
    rw [hx,size_zero,mul_zero] at small
    exact norm_le_zero_iff.mp ((size_norm x).trans ((size_refund L x).trans small))
  let r := LinearEquiv.ofBijective A ⟨inj,LinearMap.injective_iff_surjective.mp inj⟩
  let W := ((slide_linear P).mk' _).comp r.symm.toLinearMap
  have clean (x : I) : W (r x) = Slide x P := by change Slide (r.symm (r x)) P = _;rw [r.symm_apply_apply]
  have taut (e : ℝ) (x : I) : (∑ i:J,‖val x i‖*(e*chargeN L i))=e*size (amplify d C L x) := by
    rw [← charge_sum L x,Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => mul_left_comm ..)
  have inv : 2*Q ≤ ld C.path.levels m := by
    change 2*Q+t+(1+oldCost d K) ≤ ld _ _ at two
    linarith
  have ha1 : α ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (L).property) (by norm_num)
  have g1 : γ ≤ 1+oldCost d K := add_le_add (light L) (mul_le_of_le_one_right o0 ha1)
  have direct : t+γ ≤ ld C.path.levels m := by
    change 2*Q+t+(1+oldCost d K) ≤ ld _ _ at two
    linarith
  refine ⟨W,r,⟨?_,hc.pos.2⟩,fun x =>
    ⟨(rate x).1.trans (mul_le_mul_of_nonneg_right inv (size_ge _)),
     (rate x).2.trans (mul_le_mul_of_nonneg_right direct (size_ge _))⟩,?_⟩
  · intro y
    obtain ⟨x,rfl⟩ := r.surjective y
    have profile := plot.cursor.sense d le_rfl
    have bought := Printed.all (Real.sqrt_pos.mpr (forcedPos ..)) (h.wilson.represents N p m hm.le).good
      Finset.univ profile.order profile.power (fun i _ => (form i).twist profile.order profile.power (val x i))
    rw [taut] at bought
    rw [clean]
    refine ⟨_,bought.grow ?_⟩
    have pos : 0 ≤ ahead K c d := add_nonneg (mul_nonneg zero_le_two hm0) zero_le_one
    have left := mul_le_mul_of_nonneg_left (rate x).1 pos
    rw [←mul_assoc] at left
    exact left.trans (mul_le_mul_of_nonneg_right within (size_ge _))
  · intro x
    let move := placed (keys0 h hm) b
    have measured := Travel.list Finset.univ h hm plot.door (fun i _ => (ride i).smul (val x i))
    change Travel _ _ _ _ _ _ _
      (∑ i:J,val x i • move (V (ticket i))) (Slide x P)
        (∑ i:J,‖val x i‖*(δ*chargeN L i)) at measured
    have collated : (∑ i:J,val x i • move (V (ticket i))) = move (V x) := by
      simp_rw [←map_smul,←map_sum,cardp x]
    rw [collated,taut] at measured
    rw [clean]
    exact measured.extend (mul_le_mul_of_nonneg_right fare (size_ge _))

end YM.Integration.WilsonThermometerOffsetGraph
end
