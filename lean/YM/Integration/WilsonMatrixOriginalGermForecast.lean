import YM.Integration.WilsonMatrixOriginalGermMarket
import YM.Integration.WilsonMatrixOriginalGermPeriod

/-! The same input used in the measured nonbare response has an affordable complete germ at
the capture date. Its exact finite coordinate table tends to the previously reported independent
coordinates, with the same clock on every finite regulator. -/

noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermForecast
open Filter Lattice RG RG12 RG17 Spec Wilson Labels Extraction FullVolume Table Climb
open Source MS.Local.Physical MS.Menus FVA2 PhysicalNext.Repeat.Legato Next.Rank.Price
open Trace.Physical.GermGraph WilsonMatrixTicketLanesNativePrices WilsonMatrixOriginalIndependentColumns
open WilsonMatrixOriginalIndependentLimit WilsonMatrixOriginalGermMarket WilsonInheritedRegisteredField Finset
open scoped Classical Topology BigOperators

variable {G:Gauge} (R:Run G) (B:Deck G) {f:Extraction.Order} {S:Table R.family.book} (F:Final R.family f S)
    (L:Layout F) (U:Ultrafilter (ℕ×ℕ)) (hU:(U:Filter (ℕ×ℕ)) ≤ L.lens)

include hU

private theorem doors (m:ℕ) (age:R.family.ref 4 ≤ m):
    ∀ᶠ z:ℕ×ℕ in (U:Filter _),Opened R.family 4 m z.2 ∧ m ≤ z.1:=by
  have sub:=hU.trans L.certified
  have wind:=(WilsonMatrixOriginalGermPeriod.winds R.family 4 m f).mul_const (stock R.family m)
  have cheap:=wind.eventually_lt_const (by norm_num:0*stock R.family m < 1/4)
  filter_upwards [cheap.filter_mono sub,((OPE.Cards.largeMesh f).eventually_ge_atTop m).filter_mono sub]
    with z open_at reaches
  exact ⟨⟨age,open_at⟩,reaches⟩

/-- The two arms may spend these exact coefficients on the same complete held fields. -/
theorem measured (τ:ℕ→ℝ) (climate:Climate R U τ) (r:ℝ) (w:R.family.label 4)
    (age:R.family.ref 4 ≤ L.level r):
    Tendsto (fun z:ℕ×ℕ=>spectrum R B (L.level r) z.1 z.2 (atRef L 4 r z w))
      (U:Filter _) (𝓝 (fixed R B F L τ r w)):=by
  let m:=L.level r
  let y (z:ℕ×ℕ):=normalized R m z.1 z.2 (atRef L 4 r z w)
  have germ:Tendsto y (U:Filter _) (𝓝 (L.shift 4 r w)):=WilsonMatrixOriginalGermPeriod.at_date R F L U hU r w age
  have scaled:Tendsto (fun z:ℕ×ℕ=>(R.family.labels.level 4).scaled (shrink R.family m z.1 z.2) (y z))
      (U:Filter _) (𝓝 ((R.family.labels.level 4).scaled (τ m) (L.shift 4 r w))):=by
    apply tendsto_pi_nhds.mpr
    intro i
    simp only [Frame.scaled_apply]
    exact (((Complex.continuous_ofReal.tendsto _).comp ((climate m).2.2.pow _)).mul (tendsto_pi_nhds.mp germ i))
  exact ((weights (warehouse R) B 4).continuous_of_finiteDimensional.tendsto _).comp scaled

/-- A preperiod numerical budget pays the true earlier program on every favorable capture geometry.
The same coupon works at every site and on every one of the genuine older gauge inputs there. -/
theorem filed (simple:G.Simple) (r:ℝ) (w:R.family.label 4) (age:R.family.ref 4 ≤ L.level r)
    (wallet:ℝ) (paid:∀N p,L.level r ≤ N→Next.UVStress.quota R.family 4 (L.level r) N p
      (atRef L 4 r (N,p) w) ≤ R.family.S.a (L.level r)^4*wallet):
    let m:=L.level r
    ∀ᶠz:ℕ×ℕ in (U:Filter _),∃(opened:Opened R.family 4 m z.2)(live:m ≤ z.1),
      let fit:=(fitting 4 z.1 z.2 m R.makes opened live).trans (WilsonMatrixOriginalGermAnchor.clocked R m
        (shrink R.family m z.1 z.2) (shrink_pos R.family R.makes live z.2).ne')
      let v:=atRef L 4 r z w
      let a:=spectrum R B m z.1 z.2 v
      (∑i,‖a i‖) ≤ 32*wallet*fare (warehouse R) B 4 ∧
        ∀o(V:Config G (R.family.side m z.2)),field R.makes live v o V=
          ∑i,a i*field R.makes live (WilsonMatrixOriginalGermAnchor.issued R B (N:=z.1) (p:=z.2) fit i) o V:=by
  intro m
  filter_upwards [doors R F L U hU m age] with z hz
  obtain ⟨opened,live⟩:=hz
  refine ⟨opened,live,?_⟩
  intro fit v a
  have funding:(R.family.S.a m^4)⁻¹*Next.UVStress.quota R.family 4 m z.1 z.2 v ≤ wallet:=by
    have ap:0<R.family.S.a m^4:=pow_pos (R.family.S.a_pos _) _
    have h:=mul_le_mul_of_nonneg_left (paid z.1 z.2 live) (inv_nonneg.mpr ap.le)
    rwa [←mul_assoc,inv_mul_cancel₀ ap.ne',one_mul] at h
  have real:0 ≤ fare (warehouse R) B 4:=sum_nonneg fun _ _=>sum_nonneg fun _ _=>norm_nonneg _
  refine ⟨(charge R B F L m z.1 z.2 opened live v).trans ?_, read R B simple m z.1 z.2 opened live v⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left funding (by norm_num)) real

end YM.Integration.WilsonMatrixOriginalGermForecast
