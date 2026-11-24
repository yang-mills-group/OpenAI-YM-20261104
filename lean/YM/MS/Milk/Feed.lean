import YM.MS.Milk.Key
import YM.MS.Tide.Stated
import YM.MS.Milk.Mural
import YM.MS.Milk.Outfit
import YM.Next.RANK.GaussTags
/-!
# Multi-standard.Even connected equation only.Expose operations.Near past estimate when all distinct, theorem.Probewise identity. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Milk
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Analysis Submodule InnerProductSpace City Next.Rank Next.Rank.Normal Theater Drops Maxwell Local.Physical
open Labels
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
open Puff Actors SplitP Puff.Mom Swirl Vane Fleet Tide PeakT -- names
variable {W X I : Type} {G: Gauge}[LinearOrder W]{B: Local.Physical.Deck G}{M:Land.Booked B}{A:Land.MS_Data G M}
    {P:Geo I}{T:W→Rake.Label B}{x:Position W I}{Y:Rake.Dance G I W}{F:Finset W}
    { f:I→ℕ→ℂ }{n:ℕ}
local notation "M1"=> marked W
lemma marble_v (v:Finset W→Convolve.T ℂ) (F:Finset W): bouquet v F 0=Cheer Toy M1 (fun x=>v x 0) F:= by
   let T:= LinearMap.proj 0 ( R:=ℂ ) ( φ:=fun _:ℕ=>ℂ ); have ht: Puff.Tether T Trunk Toy:= by
      refine ⟨ ?_,?_⟩; · change _root_.YM.MS.Puff.SplitP.refineV useN _ _=1; unfold refineV; rw [if_pos (show 0=useN.origin from rfl) ]; rfl
      intro x y; change useN.Lift Toy.core x y 0=x 0*y 0; rw [useN.loan]; rw [ show useN.pieces 0={(0,0)} from useN.home ,Finset.sum_singleton ]; rfl -- ζ norm
   exact ht.figure M1 v F
lemma rank_s {v:ℝ→Finset W→ ℂ}{p:Finset W→ℂ}(l:Filter ℝ)(hp:∀ i,Tendsto (fun t=> v t i) l (𝓝 ( p i )))(S:Finset W) : Tendsto (fun t=> Cheer Toy M1 (v t) S) l (𝓝 (Cheer Toy M1 p S)):= by
   let Μ:= Toy.stack M1; have he (i:ℕ) (x:Finset W): Tendsto (fun t=> Μ.power ( v t ) i x) l (𝓝 ( Μ.power p i x )):= by induction i generalizing x with| zero=> exact tendsto_const_nhds | succ i ih=> exact tendsto_finsetSum (subs x) (fun i _=> (hp i.1).mul ( ih i.2 ))
   unfold Cheer cheers; simp_rw [ Finset.sum_apply ]; exact tendsto_finsetSum _ fun i _=> ( he i S ).const_smul ( Actors.phase i ) -- infer
lemma form_I {i:I}(h: Mesh P x)(hp:DOrd M P A T x Y)(he:∀ F:Finset W,F.Nonempty→ Allow ( Y F 0 ) i)(F:Finset W): Tint ( Forum G ( PlainX x i ) ) ( entry G _ ( PlainI x h i ) ) ( pot F ( Lightning ∘ T ) ) []= Tide.PeakT.ordZ ( Fleet.toZ Y ) F 0 i:= by
   let V:= LogU ( PlainX x i ) ( PlainI x h i ) ( Lightning ∘ T ); let f(s:Finset W):= Vane.blade ( Y s 0 ) i; let p(t:ℝ)(s:Finset W):= V s t [];
   have hx (s:Finset W): Tendsto (fun t=>p t s) atTop (𝓝 (f s)):= by
       obtain hz|hz:=s.eq_empty_or_nonempty; · subst s; simp_rw [p,V, originL, f, hp.1 ]; exact ( allow_zero (G:=G) i ).1 -- Orientation p zero
       convert! (he s hz) using 1; funext t; unfold p V; rw [ ← sun T x h hp i, slew,seated ]; rw [show net ([]:Legs (Lane4 G))=0 from rfl,right0,one_mul ]
   let U:= MeterU ( PlainX x i ) ( PlainI x h i ) ( Lightning ∘ T ); have hU0(s:ℝ): U F s [] = Cheer Toy M1 (p s) F:= by
       unfold U; rw [ ← ExpU ]; let Θ:= lampL (Lane4 G) s; have ht: Puff.Tether Θ ( ASeq G ) Toy:= ⟨ rfl,fun _ _=> times_nil .. ⟩; exact ht.figure M1 V F -- ASeq proof met
   refine tendsto_nhds_unique ( horizonT _ ( PlainI x h i ) _ F [] ) ?_; change Tendsto _ _ (𝓝 ( bouquet _ F 0 )); rw [marble_v ]; exact (rank_s _ hx F).congr ( fun p=> (hU0 p).symm )
-- include Width from HP. hidden.Te.
omit [LinearOrder W]
variable {T:Fin n → Rake.Label B} {x:Position (Fin n) I} {Y: Rake.Dance G I (Fin n)}
lemma Hymn (h:Mesh P x)(hp:DOrd M P A T x Y)(i:I) (he:∀ F:Finset (Fin n),F.Nonempty → Allow ( Y F 0 ) i): Tide.PeakT.ordZ (Fleet.toZ Y) Finset.univ 0 i=Wick.moment G ( WithLp.toLp _ ( PlainX x i ) ) (fun t=> Maxwell.reduceEq ( Lightning ( T t ) ) ):= by rw [ ← form_I h hp he ]; exact harvest (z:= WithLp.toLp _ (PlainX x i)) ( PlainI x h i ) ( Lightning ∘ T ) -- orientation.Points
end YM.MS.Milk
