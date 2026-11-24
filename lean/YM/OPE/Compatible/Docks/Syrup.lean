import YM.OPE.Compatible.Docks.Cle
/-!
# Off shell rank P^real projection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Yolk
open MeasureTheory Function Filter Set
open Lattice RG Wilson Source Labels Source.Drops
open Pill Asymptotics
open Module Finset
open scoped Topology BigOperators Classical ContDiff
open Flume Flume.Page Flume.Script Silt.Float Silt -- adjust
open Spells Drift Stroke
open Score Cascade Silt Libra Next.Free Bloch FreeResolvent Precision MSbar.Tree MSbar.Tree.Resolvent Frequency Streamer Terp Paver -- ?
variable {I F E J:Type}{G:Gauge}{i m r k d:ℕ}{f:Filter I}{β:I→ℝ}
section
variable {X:Labels.Frame G d}{T:SectionData X}{P:Pad G}{C:KernelChoices}{H:Hol G}
local notation "J!"=> X.Index
structure Lineage (η:I→ℝ)(P:KernelChoices)(S:I→Train r)(hr:4 ≤ r)(ℓ:I→ℝ)(U:I→BudgetPoint)(W:I→ J!→ Asp T H k)(m:ℕ):Prop where
        born :Tendsto β f atTop
        wages j:Salary born (fun i=>W i j)
        seekers :Wax β f η (-1)
        cap (j:J!) : ∀ᶠ i in f,∀ x∈ Hoard G (4*(W i j).b) (k+6) m,
           ‖boostS (rentV G (S i) hr P (W i j|>.N)) (1/2) m (k+6) x-boostS (atlasF G (S i) hr P) (1/2) m (k+6) x‖ ≤ η i*‖x‖
        ink (j:J!): ∀ᶠ i in f,(W i j).xraw.x=Pi.single j 1
        time (j:J!) : ∀ i, (W i j).clipw=ℓ i
        rhythm (j:J!): ∀ i, (W i j).Φ.p=U i
end
-- M shipping parameters fixed
open Next.Free FreeResolvent MSbar.Tree MSbar.Tree.Resolvent Frequency Streamer
open Cascade.Paver Votive -- ?
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp
variable {K:Sponsor G}{Q:Patch}{v:ℝ}{τ:Char.Phase→ℕ} {X:Labels.Frame G d}{T:SectionData X}{H:Hol G}
local notation "J!"=>X.Index
section
open Stroke
open scoped Matrix.Norms.Frobenius
variable (W:I→ X.Index → Asp T H k)(P:Pad G)(u:I→Train r) (hr:4 ≤ r)(D:Stern K Q τ d (k+6) v)
variable {η ℓ : I→ℝ}{U:I→BudgetPoint}
local notation "Tw0"=>τ 0
local notation "λ!"=> bed G (k+6) (τ 0)
noncomputable abbrev MotionH (i:I)(j:J!)(A:ℂ→L[ℝ]ℝ): bed G (k+6) (τ 0):= Asp.MeshP T P K.K H (W i j) A (u i) hr (τ 0)
-- D implicit maybe ignored
noncomputable def Φort (i:I)(j:J!)(A:ℂ→L[ℝ]ℝ):bed G (k+6) (τ 0):=by
       let p:=MotionH (K:=K) W P u hr (τ:=τ) i j A
       let V:= (Fallix G D.aware K (u i) hr).symm (crestL G D.aware 0 p); exact V (0:Char.Phase)
lemma ΦortP (i:I)(j:J!)(A:ℂ→L[ℝ]ℝ): (Φort W P u hr D i j A).val= boostS (atlasF G (u i) hr K.K) (1/2) (τ 0) (k+6) (MotionH (K:=K) W P u hr (τ:=τ) i j A).val:=by
       let X:= MotionH (K:=K) W P u hr (τ:=τ) i j A; let t:= crestL G D.aware 0 X; have hv:t.val 0= X.val:=(crestP ..).1; exact (LapΩ D t (u i) hr).trans (congr_arg _ hv)
noncomputable def folψ (i:I)(j:J!)(A:ℂ→L[ℝ]ℝ):= Folt D (Φort W P u hr D i j A)
noncomputable def GaugeD (D:Stern K Q τ d (k+6) v)(p:Snap G d)(t:ℝ)(U:BudgetPoint) := (ζSig p t U (k+6) (τ 0) (sternCap D 0).le).comp ((bed G (k+6) (τ 0)).subtypeL.comp (FolU D)) -- invalid name
noncomputable def ζWide (i:I): X.Coeff→L[ℝ] (Folio G d×Folio G d):= Arco (fun j:J!=> ((folψ W P u hr D i j Complex.reCLM),(folψ W P u hr D i j Complex.imCLM)))
variable (h:Lineage (f:=f) (β:=β) η K.K u hr ℓ U W (τ 0))(hT:T.Sound H) (hD:d< k+6)
include h
omit hT in lemma Taken (p:Snap G d) :Wax β f (fun i=> GaugeD D p (ℓ i) (U i)) 0:=by
       let Z:= W; have hx(i):U i= (W i 0).Φ.p:= (h.rhythm 0 i).symm; have ht(i):ℓ i=(W i 0).clipw:= (h.time 0 i).symm; let F:=(bed G (k+6) (τ 0)).subtypeL.comp (FolU D); have hs:= Salary.ζF (fun i=>W i 0) (h.wages 0) p (k+6) (τ 0) (sternCap D 0).le; unfold GaugeD; simp_rw[hx,ht]; change RateLE _ _ (fun i=> _ ∘L F) _; simpa only[zero_add] using Paintζ _ (RateLE.const F (carth h.born)) _ hs
include hT hD
lemma salary_cost (p:Snap G d)(j:J!) (A:ℂ→L[ℝ]ℝ): Tendsto (fun i=> GaugeD D p (ℓ i) (U i) (folψ W P u hr D i j A)) f (𝓝 (A (JD p X (Pi.single j 1)))):=by
        let x(i):= W i j; have he:= Salary.Watch P K.K x (h.wages j) A u hr p η h.seekers hT hD (sternCap D 0).le (h.cap j); apply tendsto_iff_dist_tendsto_zero.mpr; refine he.congr' ?_; filter_upwards [h.ink j] with i hi; let z:= x i; let q:= Φort W P u hr D i j A; let Y:=ζSig p z.clipw z.Φ.p (k+6) (τ 0) (sternCap D 0).le
        rw [dist_comm, dist_eq_norm]; rw[show (x i).xraw.x=_ from hi]; rw [←h.rhythm j i,← h.time j i]; change _=‖_ - Y (_)‖; rw [show boostS _ (1/2) _ _ _=q.val from (ΦortP W P u hr D i j A).symm]; exact congr_arg (fun u=> ‖_ -u‖) (MintsQ z.Φ.p p z.clipw q (D₀:=D)) -- inspect underscores
set_option maxHeartbeats 200000
lemma spanROI : ∃ V:I→ (Folio G d × Folio G d)→L[ℝ] X.Coeff, Wax β f V 0∧ ∀ᶠ i in f,V i ∘L ζWide W P u hr D i=ContinuousLinearMap.id .. ∧ ζWide W P u hr D i ∘L V i=ContinuousLinearMap.id ..:=by
        let f(i:I)(t:X.Index) : Folio G d × Folio G d := (folψ W P u hr D i t Complex.reCLM,folψ W P u hr D i t Complex.imCLM); let Y(j:Snap G d)(i):= GaugeD D j (ℓ i) (U i); let Qt(p:Snap G d):=JD p X; have hrx: Nonempty (X.Coeff ≃ₗ[ℝ] (Folio G d× Folio G d)):=⟨(sCue X).symm⟩; unfold ζWide; refine Loans (J:=X.Index) Qt f Y ?_ ?_ (found X) β h.born ?_ hrx
        · intro i j; exact salary_cost W P u hr D h hT hD j i Complex.reCLM
        · intro i j; exact salary_cost W P u hr D h hT hD j i Complex.imCLM
        intro i; exact Taken W u hr D h i
end
end YM.OPE.Yolk
