import YM.MS.Fleet.Residue
/-!
Fixed offsets comparison and pointwise conversion to single-Mark. Keep any scaling along sequence
but in argument for identity at fixed index only need constant Visa. Applies to primitives as well.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Fleet
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native
open Lattice City Latch Job Belt Flux Wire Book Convolve Orbit Cog
open scoped Topology ContDiff Interval
variable {G:Gauge}{I J W:Type}[LinearOrder W]{L:I→Side}
 {X U:Rake.Dance G I W}{Q:Seeds G I W}{P:Faces I}{R:High.Recount G}
local notation "Ψ"=> ( outside L )
local notation "ιW"=> ( Orbit.uniform G I )
open Native.Wilsonian Paint Rake.Geo Vane Land Program Logarithm Wind Menus Orbit.LogReal
open Puff Puff.Actors Puff.Mom Vista High High.Knobs
variable {η:I→ℝ}{k:Team}{ V: Vista.Visa I }
local notation "πA"=> Scope G (Wind.skyline G k) η
variable (B: Fixed ( col ( skyline G k )) R true 4 1)
include B
abbrev Terrify (W I:Type):= Finset W→ℕ→I→ℂ
def toZ (F:Rake.Dance G I W): Terrify W I:= fun s n=> Vane.blade ( F s n )
lemma Ωgo (K:SpaceOut.FlowSet V Q)(H:SpaceOut.warmV η V)(b:Bool)(hc:Clearance L P)(he:Vista.width L P): ∃ (X:Rake.Dance G I W)(f:Terrify W I), SpaceOut.Easier G L Q P k η X ∧ CCOrb G η k P L Q b f ∧ (∀ i t s,Vane.Allow ( X i t ) s) ∧ f ∅=0 ∧ ∀ s:Finset W,s.Nonempty → ∀ n, cash_out V L ( f s n -toZ X s n ):= by
    obtain ⟨Y,F,S,U,hU,H,hC,hB,hK⟩:= SpaceOut.Resolution B K H b hc he; let f(t:Finset W)(n:ℕ)(i:I):ℂ:=limUnder atTop (fun p:ℝ=> S i t n p []); have h0 : f ∅=0:= by funext n i; unfold f; rw [(H i|>.1.2.1)]; exact Filter.Tendsto.limUnder_eq tendsto_const_nhds
    have hm (s:Finset W)(_hz:s.Nonempty)(n:ℕ): f s n=Vane.blade (Y s n):= by funext i; unfold f; simp_rw [ ( H i ).2 ]
    refine ⟨ U,f,hU,⟨ F,S,fun i=> H i|>.1, fun s n i=>?_⟩, fun i t s=>?_, h0, fun s hs n=>?_⟩
    · by_cases hs:s.Nonempty
      · rw [show (fun p:ℝ=>S i s n p [])=_ from funext (H i|>.2 s n),hm s hs n]; exact (hB s hs n).1 i
      rw [ Finset.not_nonempty_iff_eq_empty.mp hs,h0,( H i ).1.2.1 ]; exact tendsto_const_nhds
    · by_cases hi:i.Nonempty; exact hC i hi t|>.1 s; rw [ Finset.not_nonempty_iff_eq_empty.mp hi, hU.1 ]; exact ( allow_zero ( G:=G ) s ).1
    rw [ hm s hs n ]; exact hK s hs n
variable {c:Berth ( W:=W ) ( I:=I )}{A:W→ Actor G}
-- treat generic Circle arbitrary grade version.All G.Simple appears solely via B.Tripping. Use expansion
lemma sold (h: Badge A) (t:ℝ)(u:W→Cover): ∃ (X:Rake.Dance G Unit W) (w:ℕ→ Finset W→ℕ→ℂ), SpaceOut.Easier G (fun _=>1) ( goalsK ( I:=Unit ) (fun i _=>u i) (fun _=>t) A ) 0 k (fun _=>t) X∧(∀ s n i,Vane.Allow (X s n) i)∧ CCOrb G (fun _=>t) k crane walkway (goalsK (fun i _=>u i) (fun _=>t) A) false (fun s n i=>w i s n )∧ Accord atTop w (fun s n=>toZ X s n () ):= by
   let C i (_:ℕ):= u i; let a(_:ℕ):= t; let Q0:= goalsK C a A; let V:Visa ℕ:= ⟨ fun i=> 1+ |t|,fun _=>by simp⟩; have hp: SpaceOut.warmV a V:= fun i=>le_rfl; obtain ⟨U,f,hU,hF,H,h0,hX⟩:= Ωgo (L:=walkway) ( Q:=Q0 ) B (moneyM C ⟨hp,fun w=> ⟨‖Tone.embed (u w)‖ +1,(by positivity),0,fun i=> (le_of_lt (lt_add_one _))|>.trans_eq (by rw [pow_zero,mul_one,Pi.one_apply,mul_one])⟩⟩ (fun i=>⟨ false,0,h i ⟩)) hp false Cleared scaleWalk; let X:= favorite (fun (_:Unit)=> 0) U; have he:SpaceOut.Easier G (fun (_:Unit)=>1) (goalsK (fun i _=>u i) (fun _=>t) A) 0 k (fun _=>t) X:= stalk hU 0 _ _; have hD: U=favorite (fun _=>()) X:= soloP hU (stalk he crane _ (fun _=>())); refine ⟨ X,(fun i s n=> f s n i),he,(fun s n _=> H s n 0 ),hF,?_⟩; intro s n; change Tendsto (f s n) atTop (𝓝 (toZ X s n ())); by_cases hz:s.Nonempty
   · let F:= toZ X s n (); obtain hu:= Timed (hX s hz n ) ( fun i=>rfl ); have he'(i:ℕ):toZ U s n i=F:= by nth_rw 1 [ hD ]; rfl -- definitions
     change Tendsto (fun p=> f s n p - toZ U s n p) atTop (𝓝 0) at hu; simp_rw [ he'] at hu; exact (tendsto_sub_nhds_zero_iff.mp hu) -- name
   rw [Finset.not_nonempty_iff_eq_empty.mp hz,h0]; unfold toZ; simp only [he.1,Pi.zero_apply]; rw [ show Vane.blade _ ()=0 from (allow_zero (G:=G) ()|>.2) ]; exact tendsto_const_nhds -- syntax simp shadow
-- notational.LAB.Read single lack. explicit Offen.Box.Kind.
end YM.MS.Fleet
