import YM.FVA2.Full.Stated
/-!
# Orbit-removal supplier retaining internal kernel estimates

Extend the results in `YM/MS/SpaceOut/Saga` and `YM/MS/Fleet/Passage`; note
`Images.small` for the **marked** $ΔMark$ estimates, `mid` (with unbounded-belt
estimates in `Balk`), and `runs` for the `Period` estimates on the orbit/periodic
calculation. Kernels on the `Rake`/`Vista` conventions; for how to use `Images`
(including **derivatives**) see `YM/FVA2/Removal/Wires`.

The `Fixed` hypothesis is at the bulk level. Don't need marked Taylor
matching at this step (see `FlowSet` etc. hypotheses here for the actual
requirements on the seeds & parameters). So it can be used both before
and after inserting the unphysical generator pieces. No claim about any
differentiation of lattice observables in their external positions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.SpaceOut
open Set Filter Function Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit Cog
open Vista Orbit.LogReal Logarithm LogTime Program Wilsonian Wind Knobs
open scoped Topology ContDiff Interval
variable {G:Gauge} {I W:Type}[LinearOrder W] {M:Vista.Visa I}{L:I→Side}{η:I→ℝ}{A:Faces I}{Q:Seeds G I W} {v:Team}{b:Bool}
variable {U:Recount G}
-- Keep the cover (`outside`) and orbit/period cases distinct. Matching to Main
-- uses `b=true` on the latter.
local notation "Ω"=> outside L
local notation "α"=> Orbit.Scope G (skyline G v) η
local notation "Ι"=> Orbit.uniform G I
local notation "Z"=> enterV L b
local notation "Q0"=> TokenB G v η
variable (G L η v b Q A M) in
structure Images (U Y:Rake.Dance G I W) : Prop where
 tower : Circuit (outside L) (Orbit.uniform G I) (TokenB G v η) A Q (Orbit.Scope G (skyline G v) η) 0 U
 mid : Balk M (outside L) Ι α 0 A U
 runs : ∃ S D, Circuit (enterV L b) (lampV G L) (TokenB G v η) A Q S D Y ∧
     Period ( Mid M L ) Z (lampV G L) S D Y A 1 ∧
     Period (After M L) Z (lampV G L) S D Y A (Tail M L)
 small : ∀ (t:Finset W),t.Nonempty→∀ k,ΔMark M L false (Y t k-U t k)
variable (B: Fixed ( col ( skyline G v )) U true 4 1)(K:FlowSet M Q)(H:warmV η M)
include B K H
lemma realized (b:Bool)(hc:Vista.Clearance L A)(he:Vista.width L A): ∃ (Y:Rake.Dance G I W)(X:SoC G W I L)(U:Rake.Dance G I W), Images G M L η A Q v b U Y ∧
 (∃ V:Fleet.SlotB G L,∀ i, Portrait G η v A L b Q i (V i) ( X i ) ∧ ∀ t n p, X i t n p []=Y t n i p []) ∧ Folio U M L ∧ Folio Y M L ∧ ∀ (s:Finset W),s.Nonempty→∀ n, cash_out M L ( Vane.blade (Y s n)- Vane.blade (U s n)) := by
    let K0:= Orbit.uniform G I; let Z':= enterV L b; obtain ⟨S0,H0,U,hU,h0⟩:= HarborStory B K H A L; obtain ⟨S,D,Y,hS⟩:= CorΦ Z' A ( health G L ) (tokenCaps v η G) (fun z=> K z|>.1); have hx(i:I):= C_to i ( health G L ) hS ( guarding G v η L i ); have hX : H0=0:= deadD rfl hU.defect; have hB : S0=Orbit.Scope G (skyline G v ) η:= soloB hU.action (dawnG η L ( skyPC G v ));
    let V (i:I):= Valve L b S D i; let X(i:I):= Vision L b Y i A; have H' := Sedona hc he M ( b:=b ); have hv := ( show Vista.Gate M S0 Q from ⟨ by rw [hB]; exact sky_budget H ( skyPC G v ) B, fun s=> (K s).2⟩ ); have he (s:Finset _)(h:s.Nonempty)(n:ℕ):= Vista.signal hU hS hv ( Doors .. ) H' s h n; refine ⟨ Y,X,U,?_,⟨ V,fun i=>?_⟩, h0,fun s h k=> he s h k|>.1,fun s h k=> he s h k |>.2.2 ⟩;
    · refine ⟨ hB ▸ hX ▸ hU, hB ▸ hX ▸ ζ_cover hU hv (Doors ..),⟨ S,D,hS, Vista.μ_maker hU hS hv ( Doors .. ) H', Vista.last_m hU hS hv ( Doors .. ) H' ⟩ ,fun s h k=> Vista.Peak hU hS hv (Doors ..) H' h k⟩
    obtain hp: Portrait G η v A L b Q i (V i) ( X i ) := by unfold Portrait LedgerB; rw [ ← traveller G L b i ]; exact hx i
    exact ⟨ hp,fun t n p=>readδ t L A Y b i p n ⟩
end YM.MS.SpaceOut

namespace YM.MS.Fleet
open Set Filter Function Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit Cog
open Vista Orbit.LogReal Logarithm LogTime Program Wilsonian Wind Knobs SpaceOut
open scoped Topology ContDiff Interval
variable {G:Gauge} {I W:Type}[LinearOrder W] {M:Vista.Visa I}{L:I→Side}{η:I→ℝ}{P:I→ Lattice.Cover}{Q:Seeds G I W} {v:Team}{b:Bool}
variable {A: High.Recount G}
variable (B: Fixed (col ( skyline G v )) A true 4 1)
include B
/-- Enriched quotient-to-cover comparison with linked native unmarked+mark families.
Draw from same `Y` heat and costs. -/
lemma imageBank (K: FlowSet M Q)(H:SpaceOut.warmV η M)(b:Bool)(hc:Clearance L P)(he:Vista.width L P): ∃ (Y X:Rake.Dance G I W)(f:Terrify W I), Images G M L η P Q v b X Y ∧ Easier G L Q P v η X ∧ CCOrb G η v P L Q b f ∧ f ∅=0 ∧ SpaceOut.Folio X M L ∧ SpaceOut.Folio Y M L ∧ ∀ s:Finset W,s.Nonempty → ∀ n, f s n= toZ Y s n ∧ cash_out M L ( f s n - toZ X s n ) := by
    obtain ⟨Y,S,U,hI,⟨X,H⟩,hC,hB,hK⟩:= SpaceOut.realized B K H b hc he; let f(t:Finset W)(n:ℕ)(i:I):ℂ:=limUnder atTop (fun p:ℝ=> S i t n p []); have h0 : f ∅=0:= by funext n i; unfold f; rw [(H i|>.1.2.1)]; exact Filter.Tendsto.limUnder_eq tendsto_const_nhds
    have hm (s:Finset W)(_hz:s.Nonempty)(n:ℕ): f s n=Vane.blade (Y s n):= by funext i; unfold f; simp_rw [ ( H i ).2 ]
    refine ⟨ Y,U,f,hI,hI.tower.crew,⟨ X,S,fun i=> H i|>.1, fun s n i=>?_⟩, h0,hC,hB,fun s hs n=>⟨ hm s hs n,?_⟩ ⟩
    · by_cases hs:s.Nonempty
      · rw [show (fun p:ℝ=>S i s n p [])=_ from funext (H i|>.2 s n),hm s hs n]; exact (hB s hs n).1 i
      rw [ Finset.not_nonempty_iff_eq_empty.mp hs,h0,(H i|>.1.2.1)]; exact tendsto_const_nhds
    rw [ hm s hs n ]; exact hK s hs n
end YM.MS.Fleet
