import YM.FVAAlt2.Pipeline.Crown
import YM.FVAAlt2.Winder.Grove
/-! # Per-cell T version convergence. No finite-volume O bound uniform at every arbitrary allowed side; pays through all fixed-output setting at chosen history. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Pipeline.Fees
open Function Set Filter MeasureTheory Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Geometry Prim Diagram Diagram.Formal PertExtension Series Series.Radial Series.Tested Chart Binding Ledger Gauge Booth Arm Crown
open Lattice RG Precision Comparison.RG02.Bulk Oracle Circuit
open PowerSeries
open scoped ENNReal NNReal Topology BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
open Budget.FVAAlt2.Wind Budget.FVAAlt2.Wind.Pine Budget.FVAAlt2.Wind.Seed
variable {G:Gauge}{X:Type}{c f:Side} {σ:Binding.Scale} {m:ℕ} {Q:KernelChoices}{M:X→ℕ}{N:Page M→Side} {Γ: History G}
open Period.Field
variable {C:Circuit M N}(Y:Oracle.Program Q)(Φ:∀ P:Patch,P.Branches Q G) (K: Comparison.RG02.Bulk.Chain Γ)(P: SeriesT C Q Γ)
variable (L:Page M→Binding.Scale)(p:ℕ) -- period
local notation:max "U_" p:max k:max=> P.stepData C Γ p k
local notation:max "F_" p:max k:max=> Halo.bios ( P.stepData C Γ p k )
local notation:max "τ_" k:max=> Γ.S.side k
local notation:max "R_" p:max k:max=> ( Γ.S.side ( P.vol k ) p )
local notation "Pr"=> C.bore G Φ L
lemma forms (f c:Side): Self ( Bump f c ) (traverse c f):= by rintro (x|x) ; exacts [ congr_arg (fun i=> Sum.inl (i,x.2)) (Lattice.wrap_lift x.1), congr_arg (fun i=> Sum.inr (i,x.2)) (Lattice.wrap_lift x.1) ] -- Prod.eta
lemma frames (f:Side):Self (hibern f PlaqAxes) Boot.pinto:=fun i=> Prod.ext (Lattice.wrap_lift i.1) rfl
lemma floor_prim (T_ :StepData c f)(V: Branchix → Orders (KFoot G))(H: Sphere T_ (Halo.bios T_) σ V)(e q:ℕ): ∀ (i:Fin q)(x:KFoot G), ( Booth.studied V f c ) e q ∘ (Subtype.val: Hold i ( joint G f c x ) → Tuple ( Pins f c G ) q) = Stalk.collect (Arch.projection (joint G f c) i x) (many V e q ∘ Subtype.val):=by
 intro i x; ext1 z
 have h:= acts_here (R:= Bump f c) (T:= (leave f G).disj (leave c G)) i x _ ( forms f c ) ( fuel T_ _ V H e q ) (fun i=>bound_cost (H i|>.sized e q) ) z
 simp_rw [Function.comp_apply, studied,Finset.sum_apply]; exact h.symm
-- transport casts between forecast.N.Truth
open Lift
abbrev addon (i:Flap M):Orders (Pins (Γ.S.side (P.vol i.next+1) p) (Γ.S.side (P.vol i.next) p) G):= Booth.studied (C.bore G Φ L i) _ _
lemma primes (i:Flap M)(e q:ℕ): let B:= C.bore G Φ L i; below atTop (many B e q) fun p=> offer ( (StepA P i).spring p ) (addon Φ P L p i e q):=by
 intro B; obtain ⟨C,hc,h⟩:= HeldFoot (B:=_) _ _ (fun i=> B i e q) (forms _ _) (fuel (U_ 0 i) _ B (See.poster_h Φ P L 0 i) e q) ( fun z=> bound_cost ( See.poster_h Φ P L 0 i z|>.sized e q ) ); exact ⟨_,Arch.EarnPivot (T:=StepA P i) (v:= many B e q) (V:=fun p=> addon Φ P L p i e q) (fun w a b=> floor_prim (U_ w i) B (See.poster_h Φ P L w i) e q a b ) h hc ⟩
lemma weights (Γ:History G)(i:ℕ)(V:Face ℤ→ Orders (Foot G)) (H: Plane σ G V)(e q:ℕ): below atTop (many V e q) fun p=> offer ( (HaloA (Γ:=Γ) i).spring p) (Boot.weights V (Γ.S.side i p) e q):=by
    obtain ⟨C,hC,h⟩:= HeldFoot (hibern (Γ.S.side i 0) PlaqAxes) _ _ _ (frames _) (tickets (Γ.S.side i 0) σ H e q) (fun z=>bound_cost ( H z |>.sized e q )); refine ⟨_,Arch.EarnPivot (T:=HaloA (Γ:=Γ) i) (V:=fun p=>Boot.weights V (Γ.S.side i p) e q) ?_ h hC⟩
    intro p y z; ext1 x; unfold Boot.weights; simp_rw [Function.comp_apply,Finset.sum_apply]; exact ( acts_here y z _ (frames (Γ.S.side i p)) ( tickets _ σ H e q ) (fun j=> bound_cost (H j|>.sized e q)) x).symm
lemma purchases (Γ:History G)(i:ℕ)(S:Boot.Scout (G:=G) m)(e q:ℕ): above atTop (S.gear e q) fun p=> offer ( (HaloA (Γ:=Γ) i ).spring p ) (Boot.view S (Γ.S.side i p) e q):=by exact ⟨_,Arch.EarnView (HaloA (Γ:=Γ) i) le_rfl (bound_cost (S.sight.canopy e q))⟩
end YM.RegulatorIR.FVAAlt2.Pipeline.Fees
