import YM.MS.Fleet.Docks

/-!
Actual two-cutoff theorem (first version). Quantitative comparison statement for PURE POLE MS
renormalized `MS_Data` connected cumulants in 4D, with the Landau-lattice gauge calculations on
exact inversion quotient tori (or just tori); arbitrary finite marks of physical grade.
Uses still-adjusted exact terms; below we shall identify genuine gauge invariant reading,
then the finite conversions. Works for marker parameters including designated log length `R.η` and
Mesh offsets. Scalar endpoint has the convergence previously claimed only internally on laws.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Fleet
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native
open Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit Cog
open scoped Topology ContDiff Interval
variable {G:Gauge}{I W:Type}[LinearOrder W]{L:I→Side}{S:Finset W}
    {X U:Rake.Dance G I W}{Q:Seeds G I W}{F:I→Law G}{n:ℕ}{A:Faces I}
    (c:Berth ( W:=W ) ( I:=I )) {b:Bool}
open Vista Vane Rake.Geo Land High Program Logarithm Wind Menus Orbit.LogReal
variable {B:Local.Physical.Deck G}{O: Booked B}{V:LitBook B}{T:Prescription B}
   {R: Geo I}{Wv: Visa I}{l:W→ Rake.Label B}{M: MS_Data G O}
local notation "Ψ"=> outside L
local notation "ιW"=> Orbit.uniform G I
local notation "πA"=> Scope G (Wind.skyline G T.team) R.η
lemma τv (i:I)(t:ℝ) (s:Finset W): voyage c X s n i t [] = X s n i ( exp t ) []:= by
   unfold voyage vessel unload; rw [sleeve_here, home_0]; exact one_mul _
-- Γ comparison at actual endpoint ν. R is arbitrary subtraction log-length (NOT μ), see MeasureD.
abbrev SlotB (G:Gauge) (L:I→Side):= (i:I)→ LogReal.Series ( FixedMode G (dimT L i))
def Ρ_Orb (t:Finset W)(n:ℕ) (X: SpaceOut.SoC G W I L) (f:I→ℂ): Prop:= ∀ i, Tendsto (fun p:ℝ=> (X i) t n p []) atTop (𝓝 (f i))
def CCOrb (G:Gauge)(η:I→ℝ)(T:Team)(A:Faces I)(L:I→Side)(Q:Seeds G I W)(b:Bool)(Z:Finset W→ℕ→I→ℂ): Prop:= ∃ f: SlotB G L, ∃ X: SpaceOut.SoC G W I L, (∀ i:I, SpaceOut.Portrait G η T A L b Q i (f i) (X i)) ∧ ∀ s n, Ρ_Orb s n X (Z s n)
lemma orb_unique {f g:Finset W→ℕ→ I→ℂ}{η:I→ℝ}{p:Team} (h:CCOrb G η p A L Q b f)(he:CCOrb G η p A L Q b g): f=g:= by
    obtain ⟨F,H,h,hX⟩:= h; obtain ⟨J,X,he,hL⟩:=he; have heq : H=X:= by funext i; obtain ⟨hm,hK⟩:= he i; obtain ⟨ht,hu⟩:= h i; exact sumLabels hu ( ( just ht hm ).symm ▸ hK )
    exact funext fun n=> funext fun s=> funext fun i=> tendsto_nhds_unique ( hX n s i ) ( (heq.symm ▸ hL : _) n s i )
omit [LinearOrder W] in
lemma allow_zero (i:I): Allow (0:Glade G I) i∧ Vane.blade (0:Glade G I) i=0:= by
    have he := Tendsto.limUnder_eq ( g:=fun _ :ℝ => (0:ℂ) ) (x:= (0:ℂ)) (f:=atTop) tendsto_const_nhds; -- arguments check
    change Tendsto _ _ _ ∧ _ ; refine ⟨ tendsto_nhds_limUnder ⟨0,tendsto_const_nhds (x:=(0:ℂ))⟩, he⟩ -- trouble
lemma empty_allow (s:Finset W)(L:I→Side)(A:Faces I){η:I→ℝ}{p:Team}(h: SpaceOut.Easier G L Q A p η X)(hx:s=∅)(n:ℕ): ∀ i,Allow (X s n) i:= by rw [hx,h.1]; exact fun i=>(allow_zero ( G:=G ) i).1
lemma fee (h:Crew Ψ ιW πA 0 A Q X)(hp:SpaceOut.FlowSet Wv Q): ∀ p:Finset W,∀ n:ℕ,Knits ( X p n ):= by
   obtain ⟨Y,hY,h'⟩:= growM ( Y:=0 ) Ψ ιW A (healthy ..) (fun n=> feesBuy ( skyPC G T.team|>.owes n ) R.η ) (fun x n=> knit0 G I) (fun s=> hp s|>.1); exact soloP hY h ▸ h'
-- exponent ℓ compare.W.Index centers independent.Need offsets/read lengths positivity.VV.
variable (h:G.Simple) (hc:TaylorOK M V T)(hx:Mesh R ( info c ))
    (hV: WidthW Wv R.η c)(hj:Clearance L A)(hL: Vista.width L A)
include h hc hx hV hj hL
lemma pursuit (b:Bool): ∃ (f: Finset W→ℕ→ I→ℂ)(g p:Rake.Dance G I W), CCOrb G R.η T.team A L ( SeedsW c V T l R ) b f ∧ LOrd V R T l (info c) g ∧ DOrd O R M l (info c) p ∧
    f ∅=0 ∧ ∀ s:Finset W,s.Nonempty→∀ n:ℕ,
    let k:= Vane.charge (Label.h∘ l) s
    let C:= Vane.blade (g s n)
    let B:= Vane.blade (p s n)
    cash_out Wv L ( f s n - C ) ∧ title R eps_gain k (C-B) ∧ Verdict R k 0 ( g s n ) ∧ Verdict R k 0 ( p s n ):= by
    let Q:=SeedsW c V T l R; let HP: SpaceOut.FlowSet Wv Q:=cashSeeds c T l V hV
    obtain ⟨Y,F,S,U,hU,H,hC,hB,hK⟩:= SpaceOut.Resolution hc.bulk HP hV.proper b hj hL
    obtain ⟨g,p,hg,hp,hD⟩:= Covers V M T l R h hx hc -- order inspect
    have ht : g=voyage c U := perfect hg ( Boarding c (seedW_ok c) hU (fee hU HP) ); -- shadow hp
    have he(i:I)(s:Finset W)(H':s.Nonempty)(n:ℕ): Vane.blade ( g s n ) i= Vane.blade ( U s n ) i:= by
        have h := ( ( hC s H' n ).1 i ).comp tendsto_exp_atTop; apply tendsto_nhds_unique ( hD s H' n|>.1.1 i ); rw [ht]; exact h.congr fun t=>(τv c i t s).symm
    let f(t:Finset W)(n:ℕ)(i:I):ℂ:=limUnder atTop (fun p:ℝ=> S i t n p []); have h0 : f ∅=0:= by funext n i; unfold f; rw [(H i|>.1.2.1)]; exact Filter.Tendsto.limUnder_eq tendsto_const_nhds
    have hm (s:Finset W)(hz:s.Nonempty)(n:ℕ): f s n=Vane.blade (Y s n):= by funext i; unfold f; simp_rw [ ( H i ).2 ]
    refine ⟨ f,g,p,⟨ F,S,fun i=>H i|>.1, ?_⟩,hg,hp,h0,fun s hz n=>?_⟩
    · intro s n i; by_cases hs:s.Nonempty
      · rw [ show (fun p:ℝ=>(S i s n p [])) = _ from funext (H i|>.2 s n) ]; rw [hm s hs n]; exact (hB s hs n).1 i
      rw [Finset.not_nonempty_iff_eq_empty.mp hs,h0,(H i|>.1.2.1)]; exact tendsto_const_nhds
    intro k C0 B0; obtain ⟨ht,hz',hu⟩:= hD s hz n; refine ⟨?_,marketV ht hz' hu, ht,hz'⟩; rw [ hm s hz, show C0=_ from funext fun i=> he i s hz n ]; exact hK s hz n
end YM.MS.Fleet
