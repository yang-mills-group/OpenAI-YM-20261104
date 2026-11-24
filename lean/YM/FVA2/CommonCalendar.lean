import YM.FVA2.CommonSources
import YM.FVA2.Deliver
/-!
# Assemble linked FULL↔INVERSION prescription with one canonical (LatticePT.side) schedule

If a consumer studies $\eta$ error in going between the full-period (kept pinned at open
 fields) and the inversion reader, can use arbitrarily many stages on THESE formal regulators
 (one explicit construction here together with Theta.Program.Count). They do not share the Wick
 output; the path-level House, truss, mean/cov and input vertices and transition corrections on
 the common period are identified in `Chain`. NO direct winding-error estimate asserted here
 via this supplementary comparison route. Do not conclude qlocal analytic estimates or bounds
 stated elsewhere *using* such a transfer. Our MS formal-comparison project uses the separate
 momentum route instead (including quantitative budget on cover vs inversion vs continuum
 transported exponents there). CommonCalendar also supplies nonemptiness of explicit prescription
 choices to use with that MS result. Warm & Depth thresholds.C.N
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.Both.Passage.CapReady
open Function Filter Topology MeasureTheory Lattice Gauge RG _root_.YM.Wilson
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10 FormalOPE.RG10.Inherit FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice FormalOPE.RG10.InversionTop FormalOPE.RG10.BlockGauge
open PertExtension.Orb Precision GaussianScore RGComparison.Core16 RGComparison.Core16.Descent Tree Exterior Push.BetaTransport Tandem Luggage
open MeasureTheory.Measure (IsAddHaarMeasure)
open Contacts.Lyre Contacts.Lyre.Align Fabric CityHistory Mirror Blocking PowerSeries Finset
open Exhibit Atoll.Main IteratedWilsonPrescription Pressure
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {f c n: Side} (P: RG.Patch)(κ: KernelChoices)(h:P.Branches κ G) (h':G.Simple)
open Cohort
lemma extent (i:ℕ) : 8*(1+i) ≤ (gradeSide P i).val:= by
     induction i with
     | zero=> exact le_of_eq (by rw [gradeSide]; simp)
     | succ i ih=> rw [stepSide]; apply le_trans (b:=8*(1+i)*2) (by omega); gcongr; exact ( show 2≤ P.L.val from (by have hv:=P.coarse; omega) ) -- cases simplifier.G consumes
include h
lemma earnedMany (i:ℕ)(hM : 100* Pressure.macroR P ≤ i): Bid.Larger (G:=G) ( stepData P κ i ):= by obtain hp:= extent P (i+1); obtain hx:= extent P i; exact ⟨ h, show 100* Pressure.macroR P≤ _ from (by omega), show 1 < _ from (by omega) ⟩
def covers {n:Side}(L:Fabric G n): Prop:= match L with
    | .endcap _ _=> True
    | .layer S _ _ _ L=> S.kernel=κ ∧ S.patch=P ∧ covers L

def depth {f:Side}(L:Fabric G f):ℕ:= match L with| .endcap _ _=>0 | .layer _ _ _ _ L => depth L+1
-- ladder. This can be constructed directly passing different tags; coverage all choices.N.R.Location irrelevant semantic.D

def terrace (d:ℕ) : (i:ℕ) → Fabric G (gradeSide P (d+i))
   | 0=> Fabric.endcap _ (evenSide P d)
   | i+1=> Fabric.layer ( stepData P κ (d+i) ) h ( Contacts.Milling.Garf.art _ ) (evenSide P (d+i+1)) (terrace d i)
lemma terrace_ok (d:ℕ) (he:100*Pressure.macroR P≤ d)(i:ℕ): let L:= terrace P κ h d i; covers P κ L∧ Long L∧CapReady.depth L=i:= by
     intro L; induction i with
     | zero=> exact ⟨trivial,trivial,rfl⟩
     | succ i ih=> exact ⟨ show covers P κ _ from ⟨rfl,rfl,ih.1⟩, ⟨ earnedMany P κ h (d+i) (by omega),ih.2.1⟩, congr_arg (·+1) ih.2.2 ⟩
lemma life (i:ℕ) : let k:=i+i*i+1; ∀ m:ℕ,m+100*Pressure.macroR P ≤ k→ ∃ L:Fabric G ( LatticePT.side P.L i ), covers P κ L ∧ Long L ∧ CapReady.depth L=m:= by
     intro k m H; rw [ Schedule.gradeAt ]; let q:=k-m; have hx: 100*Pressure.macroR P ≤ q:= by unfold q; omega
     change ∃ L:Fabric G (gradeSide P k), covers P κ L ∧ Long L ∧ CapReady.depth L=m; rw [← show q+m=k from (by unfold q; omega)]; exact ⟨ terrace P κ h q m, terrace_ok P κ h q hx m⟩
lemma as_many (m:ℕ): ∀ᶠ i:ℕ in atTop, ∃ (L:Fabric G (LatticePT.side P.L i)), covers P κ L∧ Long L ∧ CapReady.depth L ≥ m := by
     filter_upwards [eventually_ge_atTop (m+100*Pressure.macroR P)] with i hi; obtain ⟨L,hf,hv,hE⟩:= life P κ h i m ( by omega ); exact ⟨ L,hf,hv,hE.ge ⟩ -- life syntax let k explicit?
omit h

variable {L:Fabric G f}(w: Exhibit L)(hL: Long L)
local notation "Z"=> w.chart
local notation "I"=> w.capz

structure Article (Q:Warehouse G)(L:Fabric G f)(w: Exhibit L)(hL:Long L) : Prop where
 path : let X:= Exhibit.prescription w; Chain w.chart w.quotes L hL Descent.nil trivial (show (Descent.nil (top:=f)).Tags from () ) (initialFull G f 1) (X.z ∘ some) ( Open.protocol X ) -- type too
 voices (J:Type) [LinearOrder J] (s:Finset J) (B:MS.Local.Physical.Deck G)(d:J→ℕ)(x:J→Lattice.Cover)(a:Lattice.Cover)(t:MS.Book.Program.Team)(r:ℝ)(Λ:(i:J)→ MS.Menus.Acts B (d i))(O:MS.Book.Convolve.T ℂ) :
    let T':= tagPrice w d x s Λ t r Q a -- check
    MS.Fleet.PhysicalSum G t r f true s x a (Track.request Q d Λ t) O ↔ Score.netE T'=O
include hL
theorem issuance (Q:Warehouse G) : Article Q L w hL:= ⟨ Cohort.earns w hL, fun S _ K B d x a t r Θ F=> by intro V; exact Passage.stampV Q w d x a K Θ t r F ⟩ -- order
variable (Q: Warehouse G)
include h'
-- ties to only the matching supplier. debts in crew.Both vertices physical are the same choice.
theorem established : Atoll.Main.Packing h' Q ∧ Article Q L w hL:= ⟨Atoll.Main.joint_M h' Q, issuance w hL Q⟩
omit hL
-- witnessed pair.Clock:any chosen full sequence leading unit and top unity.
def exhibit {f:Side}{L:Fabric G f}(z:ℕ→PowerSeries ℝ) (H: CityHistory.Legacy.SoundZ z)(hz:z 0=1): Exhibit L:= ⟨ Orb.tray G,Orb.traySpec G,z,H,hz ⟩
include h
theorem every (m:ℕ) (z:ℕ→PowerSeries ℝ) (hz: Legacy.SoundZ z) (he:z 0=1): ∀ᶠ i:ℕ in atTop,∃ (L:Fabric G (LatticePT.side P.L i)) (X:Exhibit L)(H:Long L), covers P κ L ∧ m ≤ CapReady.depth L ∧ X.quotes=z ∧ Atoll.Main.Packing h' Q ∧ Article Q L X H:= by
     filter_upwards [ as_many P κ h m ] with i ⟨L,hp,H,hw⟩; exact ⟨ L,exhibit z hz he,H,hp,hw,rfl,established h' _ H Q ⟩
end YM.FVA2.Both.Passage.CapReady
