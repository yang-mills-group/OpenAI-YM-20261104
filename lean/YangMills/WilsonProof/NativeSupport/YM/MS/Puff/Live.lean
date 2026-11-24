import YM.MS.Puff.Live
import YM.MS.Puff.Site
/-!
# Moment from the `Background` & `CascadeS` log calculus
Includes arbitrary sets, joint log, collapsing via Support later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Puff.Mom
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Flux Wire Book Convolve Orbit Cog Orbit.LogReal
open SplitP Actors Engine Dynamics HeatFlow
open scoped Topology ContDiff Interval
variable {A I W E:Type}{p:Sector A}[Fintype A][LinearOrder W]{B:Series A}{L:Lines A}{s:Finset W}
   {Q:SpecB A}{X: Infos W A}{P:Mate A W}
abbrev Pie (p:Sector A) := roof ℝ ( actor p )
def Mote (h:∀ i,Clear p (L i)):= Station ℝ (fun i=> Baker (L i) (h i))
abbrev StackP (p:Sector A): Actors ( Series A ):= (Pie p).stack useN
structure Star (V:Mate A W)(p:Sector A)(Q:SpecB A): Prop where
   energy : ∀ i,Pure p false (Q i)
   seed : ∀ s i,Pure p false ( V s i )
variable (he:∀ i,Clear p (L i))(hp:Background p L Q B)(hf:CascadeS p L P B X)(ht:Star P p Q)
lemma firm (A:Linear (BL A) (BL A))(h:PinAct A p L)(_hp:Background p L Q B) (hx:B=revise B A)(hf:CascadeS p L P B X)(he:∀ s n,A (P s n)=P s n): ∀ s, X s=revise (X s) A:= by -- A conflict.
    suffices H:CascadeS p L P B (fun s=> revise (X s) A) from congr_fun (sumLabels hf H); refine ⟨?_,fun s hs k=>?_⟩; · dsimp only; rw [hf.1]; unfold revise; ext; simp -- 0 simp
    obtain ⟨hx',H⟩:=hf.2 s hs k; refine ⟨Eq.trans ( congr_arg A hx' ) ( he .. ),?_⟩;
    obtain H' := glpto h.gl H; -- RHS walk
    apply Eq.mp ?_ H'; congr! 1; funext t; change A (frame _ _ + _) = _; rw [map_add, Pi.add_apply,map_add, ← h.kev, turnQ _ _ t k 0 h,hx.symm ]; unfold labels; simp_rw [ Finset.sum_apply,map_sum ]; congr 2; simp_rw [Finset.sum_apply]; exact Finset.sum_congr rfl fun x _=> Finset.sum_congr rfl fun y _=>(h.joins t _ _).symm
include he hp
lemma branchB (hv:∀ i,Pure p false (Q i)): B∈(StackP p).guard:= fun i _ t _=> pastStand hp he hv i t
include hf ht
lemma fenn : X∈ allIndex (StackP p).guard ( Finset W ):= by
   let Z: Op A ℂ:= Koszul.sign p true; have hx:B=revise B Z:= by funext n i; rw [ revise, Function.comp_apply, show Z _=_ from Pure.signs ( pastStand hp he ht.energy n i ) true ]; simp
   have hz:=firm Z (signACT he) hp hx hf (fun s n=> by rw [ show Z _=_ from Pure.signs (ht.seed s n) true ]; simp); intro s _ n _ i _ l hd; have H : Pure p false ( X s n i ) := by
       intro l hh; obtain ht := congr_fun (congr_fun (congr_fun (hz s) n) i) l; unfold revise at ht; simp only [Function.comp_apply,Z,Koszul.at_sign,show degree p l=true from (by simpa using hh),cross_true, neg_one_mul] at ht; linear_combination ht/2
   exact H l hd
local notation "N"=> Mote he
set_option quotPrecheck false

local notation "T"=> ( N ).liftV useN
local notation "Φ"=> ((2:ℂ)⁻¹)
local notation "τ"=> marked W
omit hf ht
lemma leafN (v:Series A)(n:ℕ): ( T ).join B v n= Level p L B v n 0:= by change useN.Lift (N).join B v n = _; rw [ loan ]; unfold Level pathU; rw [ show useN.pieces n=antidiagonal n from rfl, Tone.Frame.canon_sub (fun i j=>(N).join ( B i ) ( v j )) n,hp.1,map_zero,LinearMap.zero_apply,zero_add ]; rfl
-- rhs logarithm
lemma tube ( n:ℕ): Level p L B B n 1= ( T ).join B B n:= by
    rcases n with _|n; · unfold Level pathU; rw [ leafN he hp ]; -- then pathU
                          simp [ubB,Domain.paths,pathU,Level];
    change _= useN.Lift (N).join B B (n+1); rw [loan,show useN.pieces _=antidiagonal _ from rfl,Tone.Frame.canon_corner (fun i j=> (N).join ( B i ) (B j)) _ (by omega),hp.1,map_zero,map_zero,LinearMap.zero_apply,zero_add,zero_add]; rfl
lemma lab : (extrapolate useN (HeatFlow.deriv p)).valid B ((T).move B+ Φ • (T).join B B):= by
    intro n; by_cases hm:n=0; · rw [hm,Pi.add_apply, show (T).move B 0=0 from Eq.trans (congr_arg (N).move hp.1) (map_zero _), Pi.smul_apply, leafN he hp,show Level p L B B 0 0=0 from (by simp [pathU,Level,ubB,Domain.paths]),hp.1]; simpa using (HeatFlow.deriv p).empty
    rw [Pi.add_apply,Pi.smul_apply,← tube he hp]; exact hp.2 n ( Nat.pos_iff_ne_zero.mpr hm )|>.2
-- `gradient_K` extend through coupling.H and exponential linearize
lemma exp_B (h:∀ i,Pure p false ( Q i )) : ∀ i,Status (((Pie p).Cheer useN B) i) (Static L (( (Pie p).Cheer useN B ) i)):= expense (HeatFlow.deriv p) N useN (branchB he hp h) hp.1 ( lab he hp )
include hf ht
abbrev Engage (hQ:B∈( StackP p).guard) : Engine (StackP p):= ( T ).augment B hQ -- he explicit? verify #p
local notation "θ"=> Engage he (branchB he hp ht.energy)
lemma thalf (p':Finset W) (k:ℕ) : Φ • ((τ).Lift ( T ).join X X p' k)= labels p L X p' k:= by
    let Y:= T; have H:= congr_fun (Stencil.halfB ( Y.join ) X (fun i j=> Y.rear ( fenn he hp hf ht i (Set.mem_univ _)) ( fenn he hp hf ht j ( Set.mem_univ _ ))) hf.1 p') k; rw [Finset.sum_apply] at H; exact H -- orientation
lemma flags : ((HeatFlow.deriv p |>.extrapolate useN).extrapolate τ).valid X ((θ|>.liftV τ).move X+ Φ • (θ|>.liftV τ).join X X):= by
   intro S n; change Status _ ( Static L ( X S n )+( T ).join B ( X S ) n+ Φ • ( (τ).Lift (T).join X X S n )); rw [ thalf he hp hf ht, leafN he hp,add_assoc ]; by_cases hS:S.Nonempty; exact ( hf.2 S hS n |>.2 ); rw [Finset.not_nonempty_iff_eq_empty.mp hS, hf.1, show Level p L B 0 n 0=0 from Finset.sum_eq_zero fun j _=> map_zero ( (N).join ( B (n-j) ) ),labels,show Rake.picks (∅:Finset W)=∅ from (by unfold Rake.picks; ext; simp) ]; simp only [Finset.sum_empty,add_zero, Pi.zero_apply]; rw [show Static L 0=0 from funext fun t=>map_zero ( frame ( L t ) )]; exact status_0 _
-- afterward Packing
end YM.MS.Puff.Mom
