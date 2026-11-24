import YM.LocalLTE.Vinyl.Pack
import YM.LocalLTE.Vinyl.Age
import YM.LocalLTE.Marked.Send
import YM.MergeProof.Limb
/-! Root skeleton bill with independent coefficients, permits at true Path not homogeneous marker. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open FrameBox Pastel Merge Merge.Palette

open Merge.Palette Gas Ursell Bakers
open Greenbelt
set_option quotPrecheck false
attribute [local instance] Gauge.frobInner
variable {ι:Type}(M:ι → Lotus.Leaf R) (φ:ι→ Config G f→ℝ) (H:Cash W t μ L Q o a T R)(χ:Chi)
-- Every label.Energy in θ ledger same geometry.T.Z.T.Tag projection Ward.
local notation "Oz"=> Merge.Tickets (Merge.Palette.sign M S)
local notation "Y₀"=> radiusB t
variable (z:H.fragrances)(D:Captain.Oscars M z) {θ ι' J:ℕ}
local notation "Ux"=> (fun k=> z.snd k)
local notation "U₀"=> Captain.reachability (H:=H) z
local notation "M₀"=> (fun i=> East.docket H z i)
local notation "q₀"=> (fun k=> Captain.quietR M (z.2 k) (D k))
variable {α C B' v₁ d v₀ e A β κ :ℝ}(q n k :ℕ)(r₀:ℕ→ℕ)(A':ι→Prop)(hx:Candor M z D q n r₀ A')



-- Whorl.S e_a first variant C. v ~ -(1/2), power requires upper H(i,n) chosen from jumpFee grads.V.Uniform. use p length atMost.
local notation "EC"=> Directions G c
local notation "SC"=> Disk G c
open Sienna FrameBox Grove
open PhysicalNext.Repeat.East
-- Maneuvers depend on V generic. Carrier.P.Slot all.S.Fin count.Bound independent periods.
variable (φ':Veil c f→ℝ) (h':∀ i,0≤φ' i) (rA:ι→ℝ) (hr:∀ i,0≤rA i)
local notation "Y'"=> betaF G t L
local notation "Ω"=> Merge.Tickets (Merge.Palette.sign M S)


-- switched book before masks.
open Merge.Photo Merge.Motion Marker Switch
variable [Fintype ι]
abbrev sponsor (i:Stars H M) : Ways ι:= fun t p=> pearl i.1 M (Palette.ways rA t p) i.2
abbrev actorsV (i:Stars H M)(U:Config G c) :ℝ:= Ursell.coefficient H.seam i.1.2*(∏ k, Palette.act M H χ U (i.1.snd k).val (i.2 k))/↑(i.1.fst+1).factorial
abbrev cursors (A:Stars H M→Support c)(f : Stars H M→ Config G c→ℝ)(i:Stars H M)(U:Config G c) : Ways ι:=fun s T=> sponsor M H rA i s T*masked (Pressure.temp t) (A i) (f i) U
variable (p:BudgetPoint)(hB:p.B=radiusB t)(hU:p.threshold=Pressure.temp t)
local notation "Vt"=> exactE M H χ
local notation "A'₀"=> (fun (i:Stars H M)=> reachability i.1)
local notation "χ'"=> Merge.Palette.sign M S
local notation "W'"=> Vt
lemma music (i:H.fragrances)(U:Config G c)(s T): (Palette.song M H χ rA i U) s T = ∑ j:Oscars M i,sponsor M H rA ⟨i,j⟩ s T * actorsV M H χ ⟨i,j⟩ U:=by
    let δ:=coefficient H.seam i.2/(i.fst+1).factorial; let Y k u := Palette.act M H χ U (i.snd k).val u; let r(z:Tickets χ'):= ∏ j∈z.val,Palette.ways rA s T j; let g k z:=r z*Y k z
    change coefficient H.seam i.2*(∏ k,∑ j,g k j)/↑(i.fst+1).factorial= _
    rw [Fintype.prod_sum,Finset.mul_sum,Finset.sum_div]; apply Finset.sum_congr rfl; intro j _
    change coefficient H.seam i.2*(∏k:Option (Fin i.fst), g k (j k))/↑(i.fst+1).factorial=(∏k,r (j k))*(coefficient H.seam i.2*(∏k,Y k (j k))/↑(i.fst+1).factorial)
    unfold g; rw [prod_mul_distrib]; ring

-- At 0 every term with Enter shuts. Elements are stars indexed by shape.ThinP
omit [Fintype ι] in
lemma dialed (i:Stars H M)(he: Enter M H i)(T:Finset ι): sponsor M H rA i 0 T = 0 :=by
    obtain ⟨k,j,h⟩:= he; exact Finset.prod_eq_zero (mem_univ k) (Finset.prod_eq_zero (f:=Palette.ways rA 0 T) h (by unfold ways; split_ifs<;>simp))
omit [Fintype ι] in
lemma defaults (i:Stars H M)(he:¬Enter M H i)(s T): sponsor M H rA i s T=1:=by
    exact Finset.prod_eq_one fun j _ => by rw [show (i.2 j).val=∅ from Finset.not_nonempty_iff_eq_empty.mp (fun h=>he ⟨j,h⟩),Finset.prod_empty]

variable (C₁:Captain H j C d v e B' v₁ y B η k χ)(hH:Daisy.HostQ H C₁.conduit B' B k) (hx0:p.order ≤ j)
include C₁ hH hx0 hU
lemma folk (i:H.fragrances)(U:Config G c)(s T): tones M H χ rA i U s T =∑ j: Oscars M i,cursors M H rA A'₀ W' ⟨i,j⟩ U s T :=by
    unfold Merge.Photo.tones
    rw [music,music,← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro z _
    let i' : Stars H M:= ⟨i,z⟩; let f:= W'; by_cases he:Enter M H i'
    · let x:= i'; have hp: f i' = wingTerm (χ:=χ) i'.1 M i'.2:= by unfold f exactE; rw [if_pos he]
      rw [dialed M H rA ⟨i,z⟩ he,zero_mul,sub_zero]
      refine congr_arg (sponsor M H rA i' s T*·) ?_
      change actorsV M H χ i' U=masked (Pressure.temp t) (reachability i'.1) (f i') U
      rw [hp,← hU]; exact congr_fun (wing C₁ i'.1 M i'.2 hH p hU hx0 p.power le_rfl|>.1) U
    rw [defaults M H rA _ he,defaults M H rA _ he,sub_self]; change _=sponsor M H rA i' s T*_
    unfold exactE; rw [if_neg he]; by_cases h:Healthy (Pressure.temp t) (reachability i'.1) U
    · rw [masked_eq _ _ _ _ h]; change (0:ℝ)=_*0; rw [mul_zero]
    rw [masked_ne _ _ _ _ h,mul_zero]
end YM.LocalLTE.Fan
