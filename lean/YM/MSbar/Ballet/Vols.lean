import YM.MSbar.Ballet.Fame
import YM.MergeProof.Groom
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Harvest.Eco
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Weave
import YM.MergeProof.Revenue
import YM.MergeProof.Tray
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Pediment
import YM.Planned.PRIMARY_INTEGRAL_295.Novas

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {K : MapPrices} {X : Targets s K} {D : Rolls s} {Θ : Protection D} {p : Expenses X} {u : Return.Wages} {l : ℕ→ℝ} {P : Teller G}

open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe
variable (R:Register D p u l)
def Hoard (Z:Delays Θ): Prop:= ∀ j x,Z.betaEntry j ≤ x→∀ i, StepStages j i→ let T:= X j i; let L:= D.L j; (T.goal L x)⁻¹* Real.exp (-(T.mark L (R.μ j i) x)) ≤ YM.MSbar.Heath.Stock.courage G L x
lemma stocking (V: Delays Θ) :∃ W:Delays Θ,DelayLe V W∧∀ Y:Delays Θ,DelayLe W Y →Hoard R Y:=by
    let f j i x:= let T:= X j i; let L:= D.L j; (T.goal L x)⁻¹* Real.exp (-(T.mark L (R.μ j i) x)) ≤ YM.MSbar.Heath.Stock.courage G L x
    obtain ⟨x,-,hx,H⟩:= collect_upper V.betaEntry _ fun j=> eventually_transitions j _ _ (fun i hi=> show ∀ᶠ x in atTop, f j i x from Legato.Bandage.winter (X j i) (D.L j) _ (R.consumes _ _ hi).2.1)
    let W:Delays Θ:={V with betaEntry:=x}; exact ⟨W,⟨hx,le_rfl,le_rfl,le_rfl⟩,fun Y hy j x he i ht=> H j x ((hy.beta j).trans he) i ht⟩
structure Dome(Z:Delays Θ):Prop where
    height : ∀ (V:Delays Θ)(he:DelayLe Z V)(B:Bar V)(w:Wait B)(A:Levels G),Paid w A→ (∀ i:ℕ,A.clock.hatBeta (i+1) ≤2*A.clock.hatBeta i)∧∀ i j,YM.MSbar.Mosaic.hatW (A.clock.hatBeta i)^4≤(A.S.side i j).val
lemma loft(V:Delays Θ) : ∃ W:Delays Θ,DelayLe V W∧ Dome W:=by
    have hp(i:ℕ): ∀ᶠ x:ℝ in atTop, betaF G x (D.L i) ≤ 2*x:= (YM.MSbar.Heath.Stock.shiftedLog G _).mono fun x hh=>hh.2.2.2.2.1
    choose f hf using fun i=> eventually_atTop.mp (hp i); let W:Delays Θ:={V with betaEntry:=fun i=>max (V.betaEntry i) (f i), shells:=fun i=>max 1 (V.shells i), growth:=fun i=> max (V.growth i) 4}; refine ⟨W,⟨fun i=>le_max_left ..,le_rfl, fun i=>le_max_right ..,fun i=>le_max_left ..⟩, ⟨fun K h b w A he=>?_⟩⟩ -- inner mk.Prop single field maybe Lean needs braces
    constructor
    · intro i; let j:=A.clock.J (i+1); rw [Extra.Iteration.block_beta i,Extra.Iteration.block_eq he]; exact hf j _ ((le_max_right ..).trans ((h.beta j).trans (he.pays i)))
    intro i j; have hp:= he.volume i j; let k:= A.clock.J (i+1); let X:=A.clock.coverSize i; suffices hx: X^4 ≤ (A.S.side i j).val by
       apply le_trans (pow_le_pow_left₀ (sq_nonneg _) (Nat.le_ceil _) 4); push_cast at *; exact_mod_cast hx
    apply le_trans _ hp; have hm: 1 ≤ K.shells k:= (le_max_left ..).trans (h.shells ..); have hu:4 ≤ K.growth k:=(le_max_right ..).trans (h.growth ..);
    exact le_trans (Nat.pow_le_pow_left (show X ≤ 1+X+A.clock.coverSize (i+1) by omega) _) ((Nat.pow_le_pow_right (by omega : 0 <1+ X+A.clock.coverSize (i+1)) hu).trans (Nat.le_mul_of_pos_left _ hm))
end YM.PhysicalNext.Repeat.Mallow
