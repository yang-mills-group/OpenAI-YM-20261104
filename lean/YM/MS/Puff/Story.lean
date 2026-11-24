import YangMills.WilsonProof.NativeSupport.YM.MS.Puff.Live
/-!
Recover the ordinary (vacuum-normalized) moment of any subset of insertions on the finite
inversion quotient (or full cover torus). Then the density relation with non-normalized
expectation. Note how these go from jointly exponentiated oriented cumulants with arity zero
included to the single (product) stencils. No symmetry postulate on correl arrays.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Puff.Mom
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Flux Wire Book Convolve Orbit Cog Orbit.LogReal
open SplitP Actors Engine Dynamics HeatFlow
open scoped Topology ContDiff Interval
variable {A W I:Type}{p:Sector A}[Fintype A][LinearOrder W]{F B Z:Series A}{L:Lines A}{s:Finset W}
   {Q:SpecB A}{X: Infos W A}{P:Mate A W}
variable (he:∀ i,Clear p (L i))(hp:Background p L Q B)(hf:CascadeS p L P B X)(ht:Star P p Q)
set_option quotPrecheck false
local notation "σ"=> ((2:ℂ)⁻¹)
local notation "N"=> Mote he
local notation "T"=> ( N ).liftV useN
local notation "τ"=> marked W
-- θ field only in proofs
local notation "θ"=> Engage he (branchB he hp ht.energy)
omit [Fintype A] in
abbrev Mez (p:Sector A)(X:Infos W A) := Cheer (StackP p) ( marked W ) X
abbrev PermV (p:Sector A): Actors ( SpecB A ):= ( actor p ).stack useN
abbrev Font (p:Sector A)(V:Mate A W):= Cheer (PermV p) ( marked W ) V -- blank normative
-- presumes s.nonempty or chosen Q ∅=0. use through finite grade.
include he hp hf ht
lemma liveM (x:Finset W)(i:ℕ): Status (Mez p X x i) (Static L (Mez p X x i)+ Level p L B (Mez p X x) i 0):= by
    let Y:=Mez p X; let A:=HeatFlow.deriv p; obtain h : ( A.extrapolate useN ).valid ( Y x ) ( (θ).move (Y x) ):= expense ( A.extrapolate useN ) θ ( marked W ) ( fenn he hp hf ht ) hf.1 ( flags he hp hf ht ) x; change Status _ ( Static L ( Y _ i )+ Level p L B ( Y x ) i 0 ); rw [ ← leafN he hp ]; exact h i
omit he hp ht in
lemma originM (h:P ∅=0) (s:Finset W)(k:ℕ): Mez p X s k 0=Font p P s k:= by
    let K: Linear (OM A) (BL A):= LinearMap.proj (R:=ℂ) 0; let U:= pointL ℕ K; have ht : Tether U (StackP p) (PermV p):= ( rain ℝ 0 ).Extrapolation useN; obtain hc:= congr_fun ( ht.figure ( marked W ) X s ) k; rw [show U ∘ X=P from ?_] at hc; exact hc
    funext s k; change X s k 0=P s k; by_cases hs:s.Nonempty; exact hf.2 s hs k|>.1; rw [ Finset.not_nonempty_iff_eq_empty.mp hs,h,hf.1 ]; rfl
-- single-fill. including scalar endpoint & arity zero. data `once`.
def Lodged (p:Sector A)(L:Lines A)(B:Series A)(Q:SpecB A)(F:Series A): Prop:= ∀ n, Fill L (Q n) (F n) (Level p L B F n 0)
lemma moments (hv:P ∅=0) (s:Finset W) : Lodged p L B (Font p P s) (Mez p X s):= fun n=> ⟨ originM hf hv s n, liveM he hp hf ht s n⟩
omit he hp hf ht
lemma momonly (h:Lodged p L B Q F)(hv:Lodged p L B Q Z): F=Z:= by
   funext n; induction n using Nat.strong_induction_on with| h n ih=> obtain ht:= hv n; rw [show Level p L B Z n 0=Level p L B F n 0 from Finset.sum_congr rfl fun j hj=>by rw [ih j (Wind.path_in hj|>.2)] ] at ht; exact expertise (h n) ht
omit [Fintype A] in
-- un-normalized density.Thermo powers.Stated term for ∂P.
abbrev tintB (p:Sector A)(F:Series A) := Cheer (Pie p) useN F
include hp he
lemma point_ξ (h:∀ i,Pure p false (Q i)): ∀ i,Status (( tintB p B ) i) ( Static L (( tintB p B ) i)) := exp_B he hp h
-- derivative wrt function direction on Cheer: L.join functions, pass.Many; want multiplication relation Υ.
end YM.MS.Puff.Mom
