import YM.FVA2.InvoiceB
/-!
# Correct engineering-power and position normalization before any test. B-character

No positivity demands on position.M fields for exact identities.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option quotPrecheck false
namespace YM.FVA2.BoxOffice
open Function Filter Set MeasureTheory
open Pert Pert.Position Maxwell Maxwell.Free PositionX PositionX.Bare.Shop PositionX.Bare.Subcell
open Wilson Lattice Gauge Labels PertExtension PertExtension.Chart
open PertExtension.LatticePT RG FormalOPE.RG10 FormalOPE.RG10.BlockGauge FormalOPE.RG10.MultiGauge FormalOPE.RG10.InversionTop
open MS MS.Koszul MS.Theater MS.Book MS.Book.Program MS.Book.Convolve MS.Land MS.Menus
open Clock Score Based PairCoords Modes Paper Trans ColorCode Attend
open PowerSeries
open scoped Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} (V: Warehouse G) {U J : Type} {n r d:ℕ} {N:Side}
local notation "F"=>V.F
local notation "ψ"=> PairCoords.φ (U:=U) (J:=J)
local notation "Y"=> sameAxis V.F d
section act
variable (W: LatticePT.Word G) (b:Module.Basis U ℝ (Wilson.Field G N))(u:Site N)(e:ℝ)
local notation "ιψ"=> Boson.sharp (bell (J:=J) b) φ (bell_even b)
def ordinary (d:ℕ) (D: Frame G d)(S: YM.Source.SectionData D)(H:YM.Source.Hol G)(hs:S.Sound H)(hp: Bid.pop S): Label G d→ₗ[ℂ] Paper.Price ψ :=
   ((e:ℂ)^d)⁻¹ • (( ∑ i:D.Index, (LinearMap.proj i: (D.Index→ℂ)→ₗ[ℂ] ℂ).smulRight (ιψ (Source.seated u (D.grades i).2 (Plate.bare S i)))) ∘ₗ (topMatrix S H hs hp).inverse (covarianceSymbol G) ∘ₗ D.coords.toLinearMap )
lemma one_ardor : ordinary (J:=J) b u e W.d W.F W.S W.H W.sound W.chosen (W.F.basis W.axis)= enter b u e W:= by
    let M:=((e:ℂ)^W.d)⁻¹;
    rw [ordinary, LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.sum_apply, enter]; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; let L:= W.F; let D:= (topMatrix W.S W.H W.sound W.chosen); change M • (( D.inverse ( covarianceSymbol G ) ( L.coords (L.basis W.axis))) i ) • ιψ (BoxOffice.cast W i u) = _; unfold billV M; rw [L.coords_basis,Complex.ofReal_mul,Vertex.true_coefficients W.S W.H W.sound W.chosen W.axis i,mul_smul ]; push_cast; rfl
lemma atOwn (k:ℕ) (i: V.Atom k)(h: PositionX.Bare.wt F i=d)(p:Label G d)(he:p.val=((V.scene k).basis i).val): gate V (J:=J) b u e k ((V.scene k).basis i) = ordinary (J:=J) b u e d (V.scene d) (V.S d) V.H (V.h d) (V.acts d) p:= by
   subst d; rw [gate_name,← one_ardor (raw V k i), show p= _ from Subtype.ext (he.trans ( PositionX.Bare.base_weight_val (warehouse V) i ).symm ) ]; rfl
lemma at_gate (p:Label G d)(he:p∈Labels.Grade (d,r)): gate V (J:=J) b u e d p= ordinary (J:=J) b u e d (V.scene d) (V.S d) V.H (V.h d) (V.acts d) p:= by rw [ ← (V.scene d).basis.sum_repr p,map_sum,map_sum ]; refine Finset.sum_congr rfl fun i _=> ?_; rw [map_smul,map_smul]; by_cases h:(V.scene d).grades i=(d,r); rw [ atOwn V b u e d i (congr_arg Prod.fst h) _ rfl ]; rw [show (V.scene d).basis.repr p i= 0 from (V.scene d).power_coefficient i (Ne.symm h) he,zero_smul,zero_smul ] -- simp hGoal scopes
local notation "v0" => velvet V (J:=J) b u e
lemma costing (j:Glyph (wings G) d) : velvet V (J:=J) b u e d (sameAxis V.F d j)= ((e:ℂ)^j.size)⁻¹ • ∑ i: V.Atom j.size, ( V.prices (wings G) j.size j.grade j.2.2 i :ℂ ) • ιψ (Track.singleStamp V u i) := by
   rw [ velvet,LinearMap.comp_apply, physical_letter, gate_scale, at_gate V b u e _ (show ColorCode.letter j∈Labels.Grade (j.size,j.grade) from Warehouse.label_grade (wings G) (d:=j.size) j.2.2), ordinary, LinearMap.smul_apply, LinearMap.comp_apply,LinearMap.sum_apply ]; simp_rw [ V.price_cast ]; rfl -- binder issue Macro V and Πv
-- use ℤunit & Earth.Fit. expression pre-int. lantern =∑ funds from basis after cancellation expense.L direct equation.Crypt.
local notation "B"=> wings G
variable {h:ℕ}(p:Team)(x:ℝ)(A: Acts (wings G) d)
local notation "ζ"=> Clock.warp ψ ( shift p x ) ( share p x )
lemma body (hl:e≠0) (A:Acts (wings G) d) (j:Glyph (wings G) d):
  (∑ i:V.Atom j.size, Track.beyond V b u p x A (⟨j,i⟩: Track.Beamers V (wings G) d))=
     ( (e:ℂ)^j.size ) • (currency ψ (into (Channel.credits j x A)) * ζ (v0 d (sameAxis F d j))) := by
   rw [costing V b u e j,warp_t, mul_smul_comm, smul_inv_smul₀ (show (e:ℂ)^j.size≠0 from pow_ne_zero _ (by exact_mod_cast hl)) ]; unfold Track.beyond; simp_rw [ Track.tariff,map_mul,mul_assoc ]; rw [map_sum,Finset.mul_sum ]; apply Finset.sum_congr rfl; intro i _; let k :Track.Beamers V (wings G) d:=⟨j,i⟩; have ht (u:ℝ) : into (PowerSeries.C u)=PowerSeries.C (u:ℂ):= map_C ..; simp_rw [ht, currency_c (p:=ψ), warp_t ]
-- relation lantern all. need combine PS coefficient weighting after.Expected warp.
def factorEF (V': ℂ)(k j:ℕ):ℂ:= (V'^k)⁻¹*V'^j
lemma launched (hl:e≠0) (A:Acts (wings G) d):
   (((e:ℂ)^d)⁻¹) • Track.lantern V b (J:=J) u p x A= ∑ i: Glyph (wings G) d, currency ψ (PowerSeries.C (factorEF e d i.size) * (into (Channel.credits i x A))) * ζ (v0 d (Y i)):= by
   unfold Track.lantern; rw [ Fintype.sum_sigma, Finset.smul_sum ]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [body V b u e p x hl A,map_mul,mul_assoc,currency_c (p:=ψ), ← mul_smul ]; rfl
end act
section tune
variable (p:Team)(x:ℝ) (d:Fin n→ℕ)(A:Lattice.Cover)(c:Fin n→Lattice.Cover)
variable [Fintype U][Fintype J][DecidableEq J] (he:Even N.val) (b:Module.Basis U ℝ (Wilson.Field G N))(g:Module.Basis J ℝ (Param G N))
local notation "ιψ"=> Boson.sharp (bell (J:=J) b) φ (bell_even b)
local notation "Ξ"=> (Attend.guide (Currency b he (J:=J)) (unmarked b g))
local notation "W"=> unmarked b g
local notation "ζ"=> Clock.warp ψ ( shift p x ) ( share p x )
local notation "η"=> Currency b he (J:=J)
local notation "S"=> Attend.guide η ( ζ W )
-- factor near P.boot membership
variable (X:(i:Fin n)→Acts (wings G) (d i))
local notation "πZ"=> (Channel.coord N A c)
-- `box bit` arity univ; general arbitrary addresses; ticket.fuel no authority.Body.Use exact.Sum.Er.
lemma sealFrom (I: Finset (Fin n)) : into (Track.ticketRead V N d p x X A c I) = S (∏ i∈I, Track.lantern V b (J:=J) (πZ i) p x ( X i )):= by
   rw [ Track.ticketRead, Track.packages V b, map_sum, map_sum ]; refine Finset.sum_congr rfl fun i hi=>?_ ; rw [ funding ]; swap; · rw [warp_acts,Program.pay0,hungry g b]
   rw [ map_mul ]; apply congr_arg; apply Eq.symm; apply reserve; rw [← Clock.out_real ]; apply guides; rw [warp_acts,Program.pay0,hungry g b ]; exact Track.bench V b g he d p x A c I i -- argument order
end tune
end YM.FVA2.BoxOffice
