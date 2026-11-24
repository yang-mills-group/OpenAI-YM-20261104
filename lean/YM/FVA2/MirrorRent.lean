import YM.FVA2.SectorMirror
/-!
# Link/Haar predecessor charges at paired full & inversion periods

Here exactly powers: Θ^m(v)=A_S(v) on all fields.
 Φ restricted gaussian: top+penalty half, Desc allow any t_v. Holds for all v (of respective tag t)
 on exponential germ using no extra collar size paid to comparisons.Even roots & fixed tag.Solver.S.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.Both.Rent
open Function Filter Topology MeasureTheory Lattice Gauge RG _root_.YM.Wilson
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10 FormalOPE.RG10.Inherit FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice FormalOPE.RG10.BlockGauge
open PertExtension.Orb Precision GaussianScore RGComparison.Core16 RGComparison.Core16.Descent Tree Exterior Push.BetaTransport Tandem Luggage
open MeasureTheory.Measure (IsAddHaarMeasure)
open Contacts.Lyre Contacts.Lyre.Align Fabric CityHistory Mirror Blocking
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c f n:Side}
variable (S:StepData c f)(h:S.patch.Branches S.kernel G)(he:Even f.val)(hc:Even c.val)
local notation "T"=> Forestry S
local notation "P"=> canopy S
local notation "H"=> Both.orb G f he
local notation "K"=> Both.orb G c hc
local notation "Y"=> Both.lights G S he
local notation "Z"=> Mirror.House.join Y K
-- exact germ (if use art, then global.DataTher)
local notation "st"=> Contacts.Milling.Garf.art S
local notation "F"=> Pins G f
local notation "Wₓ"=> Future G S T
local notation "M"=> Cross (G:=G) S P
local notation "FS"=> Pins G c
variable (b:S.Choices)
lemma top_flip (f:Side)(A:Pins G f): bareF G f (ref G f A)= bareF G f A:= by unfold bareF; rw [ lamps,_root_.YM.Wilson.energy_pull ]
lemma top_bridge (v:Flats G f): bareF G f ( Trans.coverL G f v )= 2 * OpenSlots.firstBill v:= by unfold bareF; rw [ ← Trans.assemble_exp ]; change energy ( liftLinks ( expLinks G _ v ) )= 2*( _ /2 ); ring
include h
lemma forecast (x:Config G f)(v:Config G c): tagEnergy S st (Lattice.pull Align.inverse 0 x) (Lattice.pull Align.inverse 0 v)= tagEnergy S st x v := by
    let g:= S.prediction x st; let V(i:Edge (Site c))(x:G.El):ℝ:= linkEnergy S ( x * ( g i )⁻¹ );
    have hp(i:Edge (Site c)): linkEnergy S (Lattice.pull Align.inverse 0 v i * ( S.prediction ( Lattice.pull Align.inverse 0 x ) st i )⁻¹)=V ( reflect i ) (v ( reflect i )):= by
       rw [Align.split_pure S h x, flip_channel, flip_channel]; let u:= reflect i; let p:= v u; let a:=g u; unfold V linkEnergy; congr 1; change G.price (p⁻¹*(a⁻¹)⁻¹)= G.price ( p*a⁻¹); rw [ show p⁻¹*(a⁻¹)⁻¹=p⁻¹*(p*a⁻¹)⁻¹*(p⁻¹)⁻¹ from by group, G.price_conj,G.price_inv ]
    unfold tagEnergy noiseEnergy; simp_rw [ hp ]; let U:= Equiv.ofBijective Orb.reflect ( show Bijective (Orb.reflect (n:=c)) from ( show Involutive _ from ( fun v=> reflect_reflect v ) ).bijective ); exact Equiv.sum_comp U (fun i=> V i (v i))
include hc he
lemma paid_all (x: M × Flats G c): tagEnergy S st ( liftLinks (expLinks G _ ( OpenSlots.extend P x.1 )) ) ( liftLinks ( expLinks G _ x.2 ) )= 2* substep ( canopy S ) st x:= by
    let U:= expLinks G _ ( OpenSlots.extend P x.1 ); let t:= expLinks G _ x.2; let C:= liftLinks t; let q:=S.prediction (liftLinks U) st; let a:= S.kernel.penalty;
    have he : (∑ i: Edge (Site c), dawn S (liftLinks U) C i) = 2*orbitC S U t := Align.estimate S h U t hc he
    have hv(i:OEdge c): t i*( atStep S st U i )⁻¹=C i.val*( q i.val )⁻¹:= by unfold C atStep q; rw [lift_at]
    unfold tagEnergy noiseEnergy linkEnergy; rw [← Finset.mul_sum ]; change a*(∑ i:Edge _,dawn S (liftLinks U) C i)=2*(a * ∑ i: OEdge _,G.price ( t i*(atStep S st U i )⁻¹)); rw [ he, mul_left_comm ]; simp_rw [hv]; rfl
omit hc he in
lemma choice_rent (x: S.Choices) : substep P x (G:=G)=ᶠ[𝓝 0] substep P b := by
    have hp:Tendsto (fun p: M×Flats G c=>expLinks G _ (OpenSlots.extend P p.1)) (𝓝 0) (𝓝 1):= by
         have hh : expLinks G _ (OpenSlots.extend P (0:M))=1:= by rw [map_zero]; exact identity_zero
         rw [← (identity_zero (G:=G) (I:=OEdge f))]; exact (( neighborhood_exp (G:=G) (I:=OEdge f)|>.continuousAt ).tendsto.comp ( by simpa [Function.comp_def] using (( (OpenSlots.extend (G:=G) P).continuous_of_finiteDimensional).comp continuous_fst |>.tendsto (0:M × Flats G c) ) )) -- fdef
    filter_upwards [ hp.eventually (BlockGauge.same_choice S h b) ] with u hu; unfold substep BlockGauge.penalty BlockGauge.distance atStep; rw [ hu x ]

local notation "TAX"=> (tax S (Forestry S) b (G:=G))
local notation "TAM"=> (tax S (Forestry S) st (G:=G))
local notation "J"=> (substep P b (G:=G))
lemma symmA : (tax S T b) ∘ (Z).t=ᶠ[𝓝 0] tax S T b:= by
    obtain hF:= tax_same S T b h st
    have hy: TAM ∘ (Z).t=TAM:= by
        funext u; rcases u with ⟨x,v⟩; unfold tax; simp only [Function.comp_apply ];
        change tagEnergy S st ( (T).drape (expLinks G _ ((Y).t x))) ( expLinks G _ ((K).t v))=_; rw [ ← inserts, show pext G S T ( (Y).t x)= _ from Eq.symm (Both.full_reflect S x) ,lamps, show (K).t v=ref G c v from rfl, lamps, ← show (T).drape (expLinks G _ x)= _ from Eq.symm (inserts S T x), forecast S h ]; -- rhs definal
    apply Filter.EventuallyEq.trans _ hF; refine ((hF.symm.comp_tendsto ?_) ).trans hy.eventuallyEq; simpa using (( Z ).t.continuous_of_finiteDimensional.tendsto 0)
lemma car (x:M × Flats G c): CityHistory.tax S T st (( Z ).ε x)=2* substep P st x:= by
    rcases x with ⟨y,u⟩; change tagEnergy S st ( (T).drape (expLinks G _ (litF G S y))) (expLinks G _ (Trans.coverL G c u))=_
    rw [← inserts S T (litF G S y), Both.signal, ← Trans.assemble_exp (x:= OpenSlots.extend P y), ← Trans.assemble_exp (x:=u) ]; exact paid_all S h he hc (y,u)
lemma tollage : tax S T b ∘ (Z).ε=ᶠ[𝓝 0] (2:ℝ) • substep P b := by
    obtain hf := tax_same S T b h st; apply (hf.symm.comp_tendsto ?_ ).trans; · exact ( choice_rent S h b st ).mono fun i hi=> ( car S h he hc i ).trans ( congr_arg ((2:ℝ)*·) hi )
    simpa using (( Z ).ε.continuous_of_finiteDimensional.tendsto 0)
end YM.FVA2.Both.Rent
