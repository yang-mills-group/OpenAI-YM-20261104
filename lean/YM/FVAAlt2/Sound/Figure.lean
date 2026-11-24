import YM.FVAAlt2.Sound.Money
import YM.FVAAlt2.Sound.Tender
/-! # Adjusting period operators from raw Lift.Fk to Positions
 period independent of price Horizon; however paths evaluated are the entire held lattice marker cluster, not Atlas.ShapeList.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Sound.Figure
open Function Set Filter MeasureTheory Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Geometry Diagram Diagram.Formal PertExtension Series Series.Radial Series.Tested Chart Binding Ledger Gauge Booth Arm Pipeline Pipeline.See Pipeline.Crown Lodge Period.Field PhysicalNext.Repeat.Legato
open Lattice Precision RG Epoch Calibration Rocket Oracle Circuit FormalOPE.RG10
open PowerSeries Integration RunFormalChain FormalOPE
open scoped Topology ENNReal NNReal BigOperators PowerSeries Classical ContDiff Matrix.Norms.Frobenius
open Labels
variable {X I:Type}{G:Gauge}{Q:KernelChoices}{M:X→ℕ}{N:Page M→ Side}
variable (C:Run G){Φ:∀ P:Patch,P.Branches Q G}{B:Circuit M N}(Y:Program Q)(P:SeriesT B Q C.family.path)
local notation "Γ"=> (Integration.RunFormalChain.fromRun C)
local notation "R"=> Lodge.basisR C
local notation "L₀"=> (C.family.labels)
set_option quotPrecheck false
variable (Φ)
variable [LinearOrder I][Fintype I] (z:X→ I→ Cover)
local notation "PS"=> PowerSeries ℂ
variable (L:Page M→Binding.Scale)(F:Calibration.Tent M) (s:ℕ) -- period index, not depending on stop or stage
-- Psi independent at each insertion.I pure product of stencils. Could reuse taper.
def prop (d:I→ℕ)(v:(i:I)→ ((L₀).level (d i)).Index)(x:X): Boot.Scout (G:=G) (Kick.depthF Finset.univ d v):= Boot.scout C Finset.univ d v (z x)
-- period full history.PX.One.I tag
variable (k:Page M)
def perRead : Sound.Formal.Episode I C.family.labels:= fun d v=> PowerSeries.mk (fun e=> (↑(coeff e ( Sound.money Φ Γ P (Figure.prop C z d v) L s k )):ℂ))
open MS.Land MS.Local.Physical MS.Rake
local notation "Μ"=> Sound.Formal.Episode I C.family.labels
variable (σ:Ledger.Choice M)
def innerV (j:X): Μ := fun d v => PowerSeries.mk ( fun e=> Complex.ofReal (Rocket.stopped B Y Φ F (basisR C) Finset.univ d v σ z j e) )
variable {u:MS.Local.Physical.Deck G} (D:I→ MS.Rake.Label u)(T:MS.Land.Prescription u)(y ε:ℝ)
variable (j:X)
def runPer (j:X) : PS:= Sound.Formal.dated T y (basisR C) D ε ( perRead C Φ P z L s (σ.choose j) ) -- variable order? C Y if appears?
lemma clearing (θ ε:X→ℝ)(j:X): Rocket.adjust B Y Φ F (basisR C) σ D z T θ ε j= Sound.Formal.dated T (θ j) (basisR C) D (ε j) (innerV C (B:=B) Φ Y z F σ j):=rfl
lemma green (d:I→ℕ)(v:(i:I)→ ((L₀).level (d i)).Index) : Sound.Formal.Tends atTop ( innerV C Φ Y (B:=B) z F σ j d v ) fun i=> perRead C Φ P z ( Calibration.sheet F ) i (σ.choose j) d v:=by
 intro e; simp_rw [perRead, innerV,PowerSeries.coeff_mk]; have h:=tenders_all Y Φ Γ P (Figure.prop C z d v) (sheet F) (σ.choose j) e; simp_rw [Sound.money, PowerSeries.coeff_mk] at h; exact Complex.continuous_ofReal.continuousAt.tendsto.comp h
lemma tend (θ ε:X→ℝ) : Sound.Formal.Tends atTop ( Rocket.adjust B Y Φ F ( basisR C ) σ D z T θ ε j ) fun s=> runPer C Φ P z ( sheet F ) s σ D T (θ j) (ε j) j:=by rw [clearing]; exact Sound.Formal.tends _ _ _ _ _ _ _ (green C Φ Y P z F σ j) -- arguments
section Actual
variable {J:Type}[DecidableEq J][Fintype J] (i:J) (K:Marker.Census J) (r:ℕ)(W:See.Times L r)
-- do not need all positions and queries; definition of supplying has all finite currencies.Fiat. conclusion consistency
-- syntax redundant. 
abbrev Activation (S:Marker.Census J) :Type:= (d:I→ℕ) → ((i:I) → (C.family.labels.level (d i)).Index)→ Agenda P S s
def Course (U: Activation (I:=I) C P s K) : Prop:= ∀ d v, Setup Γ P K i (Figure.prop C z d v) L s r W (U d v)
def spoken (U: Activation (I:=I) C P s K) (t:Page M): Μ:= fun d v=> Sound.coins P L s K i W (U d v) t
variable (h:∀ x,L (Page.opening M x)=Clocks.flat) (U:Activation (I:=I) C P s K)(hs:Course C P z L s i K r W U)
include Φ Y h
lemma universal : ∃ G:Activation (I:=I) C P s K, Course C P z L s i K r W G:= by
 choose U g using fun d v=> See.hire Y Φ Γ P K i (Figure.prop C z d v) L s r W h; exact ⟨U,g⟩
include hs
lemma credits : Sound.Formal.Told r (Sound.Formal.dated T y (basisR C) D ε (spoken C P L s i K r W U (σ.choose j))) (runPer C Φ P z L s σ D T y ε j):=by
 apply Sound.Formal.told; intro d v e he; change coeff e _=coeff e (PowerSeries.mk _); rw [PowerSeries.coeff_mk]; exact Sound.gold Y Φ Γ P (Figure.prop C z d v) L h s K i (σ.choose j) W (U d v) (hs ..) e he
end Actual
-- money recognition across Notebook.Gears, in fact equality CORE Fk observed.Recolor when using choose.Today.
section Valid
variable (L':Page M→Binding.Scale) {q:ℕ} (h:∀ i:Page M, Ward.Squares q (Prim.tale (L i).beta) (Prim.tale (L' i).beta)) (φ:X→I → Cover)(he:z j=φ j)
include h he
lemma samePhase: Sound.Formal.Told q (runPer C Φ P z L s σ D T y ε j) (runPer C Φ P φ L' s σ D T y ε j):=by
 apply Sound.Formal.told; intro d v k hk; unfold perRead; have h':= Sound.recognizes Φ Γ P (Figure.prop C z d v) L s L' (Figure.prop C φ d v) h (σ.choose j) (show Figure.prop C z d v j = _ from ( congr_arg (Boot.scout C Finset.univ d v) he ) ) _ hk; rw [Sound.money, PowerSeries.coeff_mk, Sound.money, PowerSeries.coeff_mk] at h'; simpa only [PowerSeries.coeff_mk] using (congr_arg Complex.ofReal h')
-- across periods s selected after every horizon along moving schedules. Native positions at other x IR choices irrelevant.
end Valid
end YM.RegulatorIR.FVAAlt2.Sound.Figure
