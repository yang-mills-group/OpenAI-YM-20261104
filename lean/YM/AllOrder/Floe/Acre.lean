import YM.AllOrder.Floe.Rungs
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe.Step
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Pace Aero StateE
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge}{ι:Type}[Nonempty ι]{a b C D Z Λ ε σ Ω:ℝ}{k r m n N l:ℕ}{j:Side}
open Rent PriceCompiler
namespace PlanV
variable (g:G.Simple) (A:ℕ→Stage)(d f:ℕ→ℝ)(U:MapPrices)
variable (φ:ℕ→Age→ℝ)(L:ℕ→ℝ)(N:ℕ) (he:∀ i t,0<φ i t) (ht:∀ i,0<L i)
-- Ω possibly negative pre-L. use abs.
def alignment (x y:ℕ) (i:Age)(S:ℕ→Fees) : Prop := ∃ z, PriorDue G (A y).clip (A x).width (A y).width (A y).paths (S x) (S y) (L x) (U.α y) N i (|U.Ω y|) z
structure Concession (G:Gauge) (N:ℕ)(φ:ℕ→ Age→ℝ)(S:ℕ→Fees) : Prop where
   pos i t : 0< S i t
   crossing i x y : StepStages x y→ i∈ Age.scope N→ alignment (G:=G) A U L N x y i S
   use i x y : StepStages x y→ i∈ Age.scope N→ S y i ≤ U.α x ∧ S y i≤ U.α y
   top x i:S x i ≤ φ x i
local notation "b"=> fun x i=> min (φ x i) (min (U.α x) (U.α (x+1)))
include g he ht
lemma lease : ∃ S, Concession A U L G N φ S:= by
 have hb x i:0<b x i:= lt_min (he x i) (lt_min (U.alpha_pos _) (U.alpha_pos _));
 let F (k:ℕ)(S:ℕ→Fees):= (∀ i t,0<S i t∧ S i t ≤ b i t) ∧ ∀ i:Age,index i<k→∀ x y,StepStages x y→alignment (G:=G) A U L N x y i S
 have hx(k:ℕ):∃ S,F k S:= by
    induction k with
    | zero=> exact ⟨b,fun i t=>⟨hb ..,le_rfl⟩,fun i hi=>False.elim (Nat.not_lt_zero _ hi)⟩
    | succ k ih=>
       obtain ⟨p,hp,hP⟩:= ih
       choose t htc hC using fun i x y=> PlanV.anchor g N i (p x) (p y) (fun i=> (hp x i).1) (fun i=> (hp y i).1) (A x) (A y) (L x) |U.Ω y| (U.α y) (ht x) (abs_nonneg _) (U.alpha_pos y)
       let S (x:ℕ)(i:Age):= if index i=k then min (p x i) (min (t i x x) (t i (x+1) x)) else p x i; have he0 i x (h:index i<k):S x i=p x i:=if_neg (Nat.ne_of_lt h); have he i t:0<S i t∧ S i t≤b i t:= by unfold S; split; rename_i h; exact ⟨lt_min (hp i t|>.1) (lt_min (htc ..) (htc ..)),(min_le_left ..).trans (hp i t|>.2)⟩; exact hp i t
       refine ⟨S,he,fun i hi x y hv=>?_⟩; obtain h|h:= lt_or_eq_of_le (Nat.le_of_lt_succ hi)
       · obtain ⟨v,hv⟩:= hP i h x y hv; exact ⟨v,PlanV.pre_eq N i (p x) (p y) (S x) (S y) (A y) hv (fun j hj=>(he0 j x ((ante hj).trans h)).symm) (he0 i y h).symm (fun j hj=>(he0 j y ((ante (i:=j) (j:=i) (Or.inl hj)).trans h)).symm)⟩
       apply hC i x y (S y) (S x) (he y i|>.1) _ (fun j hj=>he0 j x ((ante hj).trans_eq h)) fun j hj=> he0 j y ((ante (i:=j) (j:=i) (Or.inl hj)).trans_eq h); unfold S; rw [if_pos h]; apply le_trans (min_le_right ..); obtain rfl|rfl:= stepStages_source hv; exact min_le_left ..; exact min_le_right ..
 obtain ⟨S,h₁,h₂⟩:=hx (N*N+N+1); refine ⟨S, ⟨fun i t=>(h₁ i t).1,fun i x y h hi=> h₂ i (Nat.lt_succ_of_le (index_mono i hi)) x y h, fun i x y h hi=>?_,fun i j=>(h₁ i j).2.trans (min_le_left ..)⟩⟩
 have hx:S y i ≤ min (U.α y) (U.α (y+1)):= (h₁ y i).2.trans (min_le_right ..); refine ⟨?_,hx.trans (min_le_left ..)⟩; obtain h|h:= stepStages_source h <;> subst x; exact hx.trans (min_le_left ..); exact hx.trans (min_le_right ..)
end PlanV
end YM.AllOrder.Floe.Step
