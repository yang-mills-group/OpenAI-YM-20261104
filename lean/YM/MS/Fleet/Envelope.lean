import YangMills.WilsonProof.NativeSupport.YM.MS.Puff.State
import YM.MS.Fleet.Price
/-!
Moment evaluation. Vacuum norm retained. The insertion marks here may even be the output
of a differential on any primitive, with genuine ghost/parity. This still proves existence
separately. Use CCOrb to assert independent of data representation/choices. At arity zero also.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Fleet
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native
open Lattice City Latch Job Belt Flux Wire Book Convolve Orbit Cog Orbit.LogReal
open Cylinder Lab High Program Logarithm Wind Menus Native.Wilsonian Native.Draft Paint
open Puff Puff.SplitP Puff.Engine Puff.Actors Puff.Mom
open scoped Topology ContDiff Interval
variable {I W:Type}[LinearOrder W]{G:Gauge} {L:I→Side}{x:Faces I}{b:Bool}{T:Team}
    {c:Berth ( I:=I ) ( W:=W )}{f:Finset W→ℕ→I→ℂ}{ η:I→ℝ}{U:W→Actor G}
set_option quotPrecheck false
local notation "μ"=> goalsK c η U
local notation "flX"=> normal G
-- background even property for B_init from `guarding`
lemma Bguard (b:Bool)(v:Team)(L:I→Side)(η:I→ℝ)(i:I)(k:ℕ) : Pure σbranch false (B_init G L b ( TokenB G v η ) i k) := by
   obtain h:= ( Orbit.guarding G v η L i ) k|>.2; unfold B_init; rw [ Vexp ]; cases b; exact h.smul _; exact Rim _ _ _ ( Pure.smul _ h )
lemma CoreOrb (hv: Badge U)(b: Bool)(i:I)(j:Faces I)(c:Berth ( I:=I ) ( W:=W ))(η:I→ℝ)(L:I→Side)(p:Team): Puff.Mom.Star ( W0 L b (goalsK c η U) i j ) σbranch ( B_init G L b ( TokenB G p η ) i ):={
   energy:= Bguard b p L η i -- notation.E binder
   seed s k:= by
       change Pure _ false ( Aspect b L i j (goalsK c η U s k i)); by_cases hp:s.card=1; swap; · rw [goals_t c η hp]; simp only [Pi.zero_apply,map_zero]; exact Pure.zero
       obtain ⟨y,rfl⟩:= Finset.card_eq_one.mp hp; rw [goals_m,vFrame ]; exact expect_n L j _ b i ( ((hv y).actual k (η i)).move (fun x=> c y i+x) ) }
lemma grow_θ (b:Bool)(n:Side)(t:ℝ): Clear σbranch ( normal G n b t ) := readsK ((foe G t).close) b -- X_even requires Lace.L.stop
variable (i:I) {S: SpecB (FixedMode G (dimT L i))} {X:SlotB G L}
abbrev bury (i:I)( s:Finset W)(f:Finset W→ℕ→ I→ℂ):= bouquet (fun a n=> f a n i ) s
lemma proper (hp: CCOrb G η T x L μ b f)(hc:Badge U) (hX: SpaceOut.LedgerB G η T L b i (X i)) (s:Finset W):∃ F:LogReal.Series ( FixedMode G (dimT L i)), Lodged σbranch ( flX _ b ) ( X i ) ( Ocell G L b i x ∘ Memo (fun w=> c w i) U s ( η i ) ) F ∧ ∀ k,Tendsto (fun t:ℝ=> F k t [] ) atTop (𝓝 (bury i s f k)):= by
   obtain ⟨ K,Q,H,hM⟩:= hp; obtain ⟨H',ht⟩:= H i; let P:= goalsK c η U; obtain he: ( X i )=( K i ):= just hX H'; rw [ he ]; let V:=Q i; let n:=dimT L i; let m:= normal G n b; refine ⟨ Mez σbranch V s,?_,fun k=> momDepart (v:=fun s k=>f s k i) (fun s k=> hM s k i ) s k ⟩ -- errors q
   have he : W0 L b P i x ∅ = 0:= by funext z; change Aspect b L i x ( goalsK c η U ∅ z i)=_; rw [goals_t c η (by simp : (∅:Finset W).card≠1), Pi.zero_apply,Pi.zero_apply,map_zero]; rfl -- Finsupp
   obtain hm:= moments ( L:=m ) ( grow_θ b n ) H' ht (CoreOrb hc b i x c η L T) he s; rw [ show ( Font σbranch ( W0 L b P i x ) s )=_ from funext ( ships c U η x L i b ) ] at hm; exact hm
-- variant with arbitrary context F fixed, not SlotB.M.
end YM.MS.Fleet
