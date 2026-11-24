import YM.AllOrder.Kinetic.Tavern
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Kinetic.Port
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable (P:Patch)(K:KernelChoices){G:Gauge}{n m:Side}{a C Λ:ℝ}{k N:ℕ}
local notation "T[" n "]"=> trees P K n
local notation "S[" n "]"=> dock P K n
local notation "X[" n "]"=> Positions (Primary n G)
local notation "J"=> RealSlice.Vertical G P K
local notation "E"=> Coarse G
local notation "R[" n "]" => Poll.Body (Key T[n] G)

-- ι neutral. require at least one input context. realized at scheduled Tube and full σ via graph. station choose irrelevance.
variable {ι:Type} [Nonempty ι]
variable (p:Clip) (O: ChartRatio G)(x:ι→PathData G)(L: ι→ℝ){L':ℕ}
variable (Q:Push.Uniform.Before G a C P.J K (N+3)) (hB:P.Branches K G)(hx:∀ i,(x i).Bounds p a C (L i))
    (hO:LocalRatio O)
local notation "Z"=> Q.tables p P
local notation "Lℓ"=> Lobby P K G
def heightV (P:Patch)(K:KernelChoices)(p:Clip)(Q:Push.Uniform.Before G a C P.J K (N+3)):= small_a (min (Q.tables p P).width (Q.tables p P).rate)
def gross (P:Patch)(K:KernelChoices)(p:Clip)(Q:Push.Uniform.Before G a C P.J K (N+3)):= stairC P K p Q*boltC 1 (Q.tables p P).rate
structure Passage where
 leading :ι→Stalk (Lobby P K G) (Lobby P K G)
 inverted:ι→Stalk (RealSlice.Vertical G P K) (RealSlice.Vertical G P K)
 head : ∀ i,Belt (leading i) (heightV P K p Q) (revenue P K p Q 1)
 summit : ∀ i, Belt (inverted i) (heightV P K p Q) (gross P K p Q)
 puts : ∀ i n,Ad G P K n→ direct (leading i) n=headMatrix (seedT P K p (x i) n)
 exterior : ∀ i n,Ad G P K n→ direct (inverted i) n= (Ker.Start.pulse P K p (x i) n)⁻¹

include Q hB hx
lemma offers : Nonempty (Passage P K p x Q):= by
  obtain ⟨F,h,H⟩:=classicalChoice P K p x L Q hB hx 1 (by omega); choose I hI hi using fun i=> cap_green P K p (x i) Q (hx i) hB; let T:= heightV P K p Q; let d:= (Z).rate; let g:=(Z).width; have hA : T≤ small_a g:=div_le_div_of_nonneg_right (min_le_left ..) (by norm_num); have hD : T≤ small_a d:=div_le_div_of_nonneg_right (min_le_right ..) (by norm_num)
  refine ⟨⟨fun i=>stick (F i),fun i=>stick (I i),fun i=>(stick_belt (h i)).debt hA le_rfl,fun i=>(stick_belt (hI i)).debt hD le_rfl,fun i n hn=>?_,fun i n hn=>?_⟩⟩
  · rw [stick_entry, ←H i n hn]; rfl
  rw [stick_entry,← hi i n hn,green,Ker.Spine.unpack] -- green unfolds definition name
lemma receipts : 0<heightV P K p Q ∧ 0≤ revenue P K p Q 1 ∧ 0≤ gross P K p Q:=
 let h:= reignQ P K p x L Q hB hx; ⟨div_pos (lt_min h.2.1 h.2.2.2) (by norm_num), (basicK P K p x L Q hB hx).2 1,mul_nonneg (mul_nonneg (inv_pos_of_pos (half_pos (half_pos h.1))).le (Real.exp_pos _).le) (boltC_pos _ h.2.2.2).le⟩
variable (T : Passage P K p x Q)
def session (A:Passage P K p x Q) (i:ι) := applyM (A.leading i) (A.inverted i)
def tenure (Q:Push.Uniform.Before G a C P.J K (N+3)) := billH (Coarse G) (RealSlice.Vertical G P K) (revenue P K p Q 1) (gross P K p Q) -- P shadows Outer p variable
lemma apex : Grade L (fun _ : ι=> tenure P K p Q) ∧ ∀ i,Belt (session P K p x Q T i) (heightV P K p Q) (tenure P K p Q) := by
 let t:= heightV P K p Q; have h:=receipts P K p x L Q hB hx; refine ⟨gia _ ?_,fun i=> (rentM (n:=three) (T.leading i) (T.inverted i) 0 0 h.1.le (T.head i) (T.summit i) h.2.2).1⟩; unfold tenure billH; have hz:= h.2.1; have he:= h.2.2; positivity
end YM.AllOrder.Kinetic.Port
