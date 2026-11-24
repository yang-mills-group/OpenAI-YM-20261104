import YM.FVA2.XReg.Faith
import YM.FVA2.Arrival.Checkpoint
/-!
# Intermediate supplier: formal comparison in the X position scheme

This comparison is BEFORE the mass-independent N. We give simultaneous `Lifetime`
(removal) results, near-identity-leading position scheme, and the exact cancellation
of the finite-regulator bare frame from the preceding stages. `Faith.written` and
`Faith.points` include convergence results on the corresponding fixed-geometry
compact sets. See `Speed` for power estimates. The scale law/final mass-independent
change of basis are supplied in `Scale`; go to `YM/FVA2/Main.lean` for the full result.

`ν` in this file is in the logarithmic convention of `YM/MS`. For example use
`ν = Teller.logNu 1` (see `Teller/Mass.lean`) to assert results at unit MS mass.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace YM.FVA2.Reg
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.Menus MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival Dframe
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open Normalize.Fray Reg.Point Reg.Unique Pivot CoverTest Higher State Reg.Choice Token Faith
open scoped Topology ContDiff BigOperators Classical
variable {n d k:ℕ}{G:Gauge}
local notation "Π"=> Press.portDeck G
local notation "𝒮"=> XSpace.Structure1.Point G d n
local notation "μ"=> (PowerSeries.mk (R:=ℂ))
local notation "W"=> Fin n
local notation "O"=> Position.OpenAxis.Plot (Press.portDeck G)
-- specified dimensional optics before color-curl ensembles.
variable (ν:ℝ)(Y:Initialize G){V:Normalize.Store G}(K:Rose.Pick V)(T: MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
variable (h:G.Simple)(S: Prescription (Press.portDeck G))
lemma leaf_chain {e:ℕ}(H:d≤e)(p:Sec G d): coeff k (Token.leaf_t ν K T e) (up H p)=up H ( coeff k (Token.leaf_t ν K T d) p ):= by unfold leaf_t stepV; simp_rw [ coeff_mk,rules,LinearMap.sum_apply,map_sum, LinearMap.smul_apply, _root_.map_smul, State.chainL ν V T H ]
structure SchemeV (S: Prescription (Press.portDeck G)):Prop where
    born : Ace.Sag Y T S -- orientation etc and full Travel price at every rank
    cost : Landing.Lifetime Y T S
    prepared (ν:ℝ)(d:ℕ): ∀ᶠ m in Front, Pivot.Ready ν Y V S d m
    pays (ν:ℝ) : Lit ν K T ( Token.conversion ν K T )
    reflects (ν:ℝ)(d:ℕ) : Formal ( Token.leaf_t ν K T d ) ∧ constantCoeff ( Token.leaf_t ν K T d )=1
    coherence (ν:ℝ)(d:ℕ) : ( V.measure d ).Solved (root ν V T d) ( State.kernel ν T d ) ∧ (∀ z:Normalize.Pick G d, z 0=0 → ( V.measure d ).Solved z ( State.kernel ν T d ) → z=root ν V T d )
    location (ν:ℝ)(d:ℕ) : Higher.HasAll Front (fun i=> Rose.proposed Y K i d) ( Faith.reports ν K T d )
    plotV (ν:ℝ)(n d k:ℕ)(p:Tags G d n): Senses (conf n) (fun i=> Rose.measureₓ Y K d i k p) (fun x=> Faith.rate ν K T d x k p)
include h
lemma lifts (p:Ace.Sag Y T S): SchemeV Y K T S:= ⟨ p, Landing.life Y T S h p.Taylor, fun ν _d=> Pivot.timely ν Y V S T h p.Taylor p.still p.base frontier, fun ν=> Faith.hearty ν Y K S T h p.Taylor p.still p.base, fun ν _d=> Faith.canonical ν Y K S T h p.Taylor p.still p.base, fun ν _d=> ⟨ State.success ν V T|>.2.1, near_free ν V T ⟩, fun ν _d=> Faith.tents ν Y K S T h p.Taylor p.still p.base, fun ν _n _d k p'=> Faith.confidence ν Y K S T p' h p.Taylor p.still p.base k⟩
def supplies := Continuum.Continuation.mk Y ( Position.OpenAxis.Plot Π ) T
local notation "Δ"=> Continuum.Continuation.proofStart h (supplies Y T)
/-- Both literal Tide and Dial endpoints usable. This extends their *raw* stencil verdict by
 choosing same M.team in actual $B^a$ columns. Use the same regulator stencils;
Lifetime for all these chosen S, plus full finite position renormalization comparison. $Faith.rate$, $reports$ include
  the continuum-side near-identity filtration frame when interpreted in X coupling, and their equality to Wilson starting
  series limits with their position calibration.
 The PT coefficients are independently defined in `Birth`, attached to `Rose.measure/proposed` data by exact identities
 in Arrival. No modification by desired comparison data.
-/
theorem comparisonCP4 (dial:Bool): ∃ S:Prescription (Press.portDeck G), S.team=(Δ dial).team ∧ SchemeV Y K T S:= by
    obtain ⟨S,hs,hu⟩:= (Arrival.checkpoint3 G ( supplies Y T ) h dial ).2; have hV : TaylorOKF T (Press.wickInput Y) S:= hu.plan; obtain ⟨ hx,hw ⟩:= Favors.upgrades Y T S hV; let Q:= Favors.Norm₀ S; exact ⟨ Ace.amen Q,hs,lifts Y K T h (Ace.amen Q) ⟨ Ace.correct Y T Q hx, Ace.strictU Q hw,Ace.horiz _⟩ ⟩
-- instance without dependency hypothesis. ∀ gauge.Fast
omit h in
lemma earns (G:Gauge)(h:G.Simple) (Y:Initialize G) (dial:Bool) : ∃ (V:Normalize.Store G)(K:Rose.Pick V) (T: MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (S:Prescription (Press.portDeck G)), S.team=(Continuum.Continuation.proofStart h (supplies Y T) dial).team ∧ SchemeV Y K T S:= by obtain ⟨v⟩:= equipped h; obtain ⟨k⟩:= Rose.nominate Y h v; obtain ⟨T⟩:= MS.Land.bookedMS ( Position.OpenAxis.Plot ( Press.portDeck G ) ); exact ⟨ v,k,T,comparisonCP4 Y k T h dial ⟩
end YM.FVA2.Reg
