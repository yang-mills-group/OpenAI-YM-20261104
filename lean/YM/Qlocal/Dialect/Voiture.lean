import YM.Qlocal.Dialect.Keeper
import YM.Comparison.RG02.Bulk.Fk
/-!
# Decompose a true `Fk` for the Tempensor.Reader clock art.Ph.
 Finite-regulator normalized prescription.Owner is a single FOREST and TAG. No comparing winding here. All fields gauge germ identity on `Colors` mood_V_Point.Art`; in particular irrespective supported history/Frame.He flags. Link to REAL interpretation needs prior support allocations. Here we show exact Price on deconstructing the Fk Log by any coupled morph. Epoch actual projections will interpret in known colors at Unit.Analytics.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Dialect
open Function Finset Set
open Marker MeasureTheory Extra.Trajectories
open Comparison Comparison.RG02 Comparison.RG02.Order
open Comparison.RG02.Assembly
open Function Filter Set Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Next.Fluctuations Next.SectorChange Multi PertExtension.Series
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {V I J K : Type} [DecidableEq I] [DecidableEq J] [DecidableEq K] [Fintype I][Fintype J][Fintype K]
variable {G:Gauge} {c f:Side}
variable {R:Census I}{S:Census J}{X:Census K}
namespace Keeper
open Join Bulk
variable (T: Poly R→ₐ[ℂ]Poly S)(hp:∀ x,(T x).part S.quiet=x.part R.quiet)
variable {N:Type*}[NormedAddCommGroup N][NormedSpace ℝ N][FiniteDimensional ℝ N]
variable {M r:ℕ}{W:Multi.Hot R→ N→ℂ}{X':Multi.Hot S→ N→ℂ}{L : N→ℝ}{l:Multi.Hot R→ℕ}{l':Multi.Hot S→ℕ}
variable (h:∀ x i, i≤r→ T (lit R (fun j:Multi.Hot R=> markLetter l W j x i)) = lit S (fun j:Multi.Hot S=> markLetter l' X' j x i))
local notation "F"=> morph T (indices r)
include h hp
lemma harmonized (x : N) : F (series R r (expansions l W L x))= series S r (expansions l' X' L x):= by
 rw [exponent_identity,exponent_identity]; have he : morph T (indices r) (series R r (Assembly.affine l W L x))=series S r (Assembly.affine l' X' L x):= by
    apply sheet_ext; intro i; rw [morph_sheet, orders_sheet, orders_sheet,map_smul, Assembly.affine,Assembly.affine, map_add, map_add, map_add,realCoeff,realCoeff, Assembly.curve,Assembly.curve, PowerSeries.coeff_mk,PowerSeries.coeff_mk]; rw [h x i.val.card (order_limit _ _), show ∀ z:ℂ,T (Poly.bead R z)=Poly.bead S z from fun z=> T.commutes z]
 rw [Multi.pass_map (morph T _) _ (driver_quiet ..) (by rw [he]; exact driver_quiet ..), he];
lemma compH (z:N)(U:(K→ℝ)→ₗ[ℝ]N)(Q:Matrix K K ℝ)(hQ:Q.IsSymm)(hv:Q.PosDef): F (prescription z U l W L Q hQ r)= prescription z U l' X' L Q hQ r:= by
 let μ:= Gaussian.cloud Q; have he (X : Type)[DecidableEq X][Fintype X] (R:Census X) (l:Multi.Hot R→ℕ)(W:Multi.Hot R→N→ℂ):
     Integrable (fun y: K→ℝ=> series R r (expansions l W L (Assembly.translate z U y))) μ ∧ prescription z U l W L Q hQ r=∫ y: K→ℝ, series R r (expansions l W L (Assembly.translate z U y)) ∂μ:= by
        let p(y: K→ℝ):= series R r (expansions l W L (Assembly.translate z U y)); let q':= prescription z U l W L Q hQ r; let hf(s):=contracted z U l W L Q hQ hv r s; have ht: Integrable p μ:= (integrable_pi_iff).2 (fun i:(Board R r).Mode=>(hf i).1); refine ⟨ht,Poly.ext fun s=> ?_⟩; rw [(hf s).2]; exact ( (Poly.get s).restrictScalars ℝ|>.integral_comp_comm ht)
 let E':= (morph T (indices r)).toLinearMap.toContinuousLinearMap.restrictScalars ℝ; have hh (y:K→ℝ) : E' (series R r (expansions l W L (Assembly.translate z U y)))= series S r (expansions l' X' L (Assembly.translate z U y)):= harmonized T hp h _
 obtain ⟨hx,hμ⟩:= he I R l W; obtain ⟨hL,hK⟩:= he J S l' X'; rw [hμ,hK]; exact (E'.integral_comp_comm hx).symm.trans (integral_congr_ae (Eventually.of_forall hh))
-- binder K instances duplicate implicit above edit
variable {H:StepData c f}{p:Clip}{O : ChartRatio G} {P: PathData G}
    (K0: Bulk.Kernel H p P O) (F':Forest H.ratio)(t:H.Choices)(d: Exterior.fieldDir G c 1)
    (W0:Colors R G f)(U0:Colors S G f)(hw:W0.vac = U0.vac)
omit h
include hp hw
lemma Fk_natural (hc:∀ (x : Bulk.Joint H F' (G:=G)) i, i≤ r→ T (lit R (fun j:Multi.Hot R=>markLetter W0.power (markFn H F' W0) j x i))=lit S (fun j:Multi.Hot S=>markLetter U0.power (markFn H F' U0) j x i)) : morph T (indices r) (Fk K0 F' t W0 d r)=Fk K0 F' t U0 d r:= by
 unfold Fk; have hE : geometric K0 F' t W0= geometric K0 F' t U0:= by unfold geometric Bulk.fee supplement; rw [hw]
 rw [hE]; exact compH T hp hc (L:=geometric K0 F' t U0) _ _ _ (K0.symm F' t) (K0.positive F' t)
end Keeper
end YM.Qlocal.Dialect
