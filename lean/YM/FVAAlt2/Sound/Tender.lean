import YM.FVAAlt2.Pipeline.Hours
import YM.FVAAlt2.Pipeline.Urban
/-!
# Computing the marked output.At.Purchased.Stop on the AUTHENTIC PERIODIC PROGRAM
 Roaming x_i physically inserted through See.*
 The same outcome up to each horizon *regardless of* (a) choice of clock realizing the reset jets,
 (b) finite cutoff p' above announced order,
 (c) spatial/local choice of script step witnesses satisfying the *independent* reclosure contract `Setup`, 
 and (d) F choice within calibrated budgets on same geometry.
 Includes convergent identification with infinite-volume-cover `esprit`.
 Here no θ scheduling or MS estimates (see next).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Sound
open Function Set Filter MeasureTheory Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Geometry Prim Diagram Diagram.Formal PertExtension Series Series.Radial Series.Tested Chart Binding Ledger Gauge Booth Arm Pipeline Pipeline.See Pipeline.Crown Period.Field
open Ledger.Sky
open Lattice RG Precision Comparison.RG02.Bulk Oracle Circuit Step Clocks Epoch Calibration Rocket
open PowerSeries
open scoped ENNReal NNReal Topology BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{X:Type} {Q:KernelChoices}{M:X→ℕ}{N:Page M→Side}{Γ: History G}{m r:ℕ}
variable {C:Circuit M N}(Y:Oracle.Program Q)(Φ:∀ P:Patch,P.Branches Q G) (K: Comparison.RG02.Bulk.Chain Γ)(P: SeriesT C Q Γ)
variable (A: X→ Boot.Scout (G:=G) m)
variable (L:Page M→Binding.Scale)
variable (h:∀ w:X,L (Page.opening M w)=Clocks.flat)
variable {u:G.ColorIndex}{F:Calibration.Tent M} -- includes calculus.
variable (p:ℕ) -- period
local notation "G₀"=> ( C.payroll Y G Φ L )
lemma flatTop (H:Notebook C Y G Φ u (Rocket.native M) F r)(w:X): sheet F (Page.opening M w)=Clocks.flat:=by unfold sheet; rw [Function.comp_apply, show F (Page.opening M w)=_ from (H.reference w) ]; exact Rocket.still
abbrev money (i:Page M): PowerSeries ℝ:=PowerSeries.mk (fun e=> note ((See.observe Φ K P A L p i) e 0))
lemma tenders_all (i:Page M)(e:ℕ): Tendsto (fun p=> coeff e (money Φ K P A L p i )) atTop (𝓝 (note ( (Pipeline.Near.esprit (C:=C) Y Φ L A).main i e 0 ))):=by
 obtain ⟨C,hC⟩:= ( Pipeline.Near.activeM Y Φ K P L A i ).walks e 0; simp_rw [money,PowerSeries.coeff_mk]; refine ( hC.point Fin.elim0 ).congr (fun p => ?_)
 change Packet.offer _ _ _= _; let v:Tuple (Pin (Γ.S.side (P.vol i) p) G) 0:= Fin.elim0; exact (congr_arg _ (Subsingleton.elim Fin.elim0 (acrossT ( (HaloA (Γ:=Γ) (P.vol i)).spring p) v))).trans (Packet.offer_eq ..)
variable (L': Page M→Binding.Scale) (A':X→Boot.Scout (G:=G) m)
lemma recognizes (H:∀ w:Page M, Ward.Squares r (tale ( L w ).beta) (tale ( L' w ).beta))(i:Page M)(hx:A i.bindW=A' i.bindW): Ward.Squares r (money Φ K P A L p i) (money Φ K P A' L' p i):= by intro j hj; simp_rw [money,PowerSeries.coeff_mk]; exact congr_fun (congr_fun (Hours.aligns Φ K P p H i hx j hj) 0) Fin.elim0
-- literal∃ traces, NOT defined via heat.
section Any
variable {I:Type} [DecidableEq I][Fintype I](S: Marker.Census I)(i:I)
def coins (C':Times L r) (σ:Agenda P S p)(x:Page M) : PowerSeries ℂ:=PowerSeries.mk (fun e=> if e≤r then Pipeline.See.prime P S i L p r C' σ (x:=x) 0 e else 0)
include h Y Φ
lemma supplyT : ∀ r:ℕ, ∃ T : Times L r,∀ p:ℕ, ∃ F:Agenda P S p, Setup K P S i A L p r T F:= by
 intro r; obtain ⟨W,_⟩:= See.prices L r h; exact ⟨W, fun p=> See.hire Y Φ K P S i A L p r W h ⟩
lemma gold (w:Page M)(T₀:Times (L:=L) r)(σ: Agenda P S p)(hk:Setup K P S i A L p r T₀ σ) (e:ℕ)(he:e≤r) : coeff e (coins P L p S i T₀ σ w)=(↑(coeff e (money Φ K P A L p w)) :ℂ):= by
 rw [coins,money,PowerSeries.coeff_mk,if_pos he,PowerSeries.coeff_mk]; exact See.scalar_here Y Φ K P S i A L p r T₀ h hk w he
end Any
end YM.RegulatorIR.FVAAlt2.Sound
