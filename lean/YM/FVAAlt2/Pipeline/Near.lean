import YM.FVAAlt2.Pipeline.Fees
import YM.FVAAlt2.Winder.Draw
/-! # Winding life and announcements
Feed directly from native See.Setup. This proves the exact correct cover kernels at iterated limit, at fixed N and computational history/coupling convention. Not an estimate on long orbits or cover-to-MS regulators with these same clocks moving. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Pipeline.Near
open Function Set Filter MeasureTheory Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Geometry Prim Diagram Diagram.Formal PertExtension Series Series.Radial Series.Tested Chart Binding Ledger Gauge Booth Arm Crown
open Lattice RG Precision Comparison.RG02.Bulk Oracle Circuit Step
open PowerSeries
open scoped ENNReal NNReal Topology BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
open Budget.FVAAlt2.Wind Budget.FVAAlt2.Wind.Pine Budget.FVAAlt2.Wind.Seed Lift
variable {G:Gauge}{X:Type} {Q:KernelChoices}{M:X→ℕ}{N:Page M→Side}{Γ: History G}{m:ℕ}
open Period.Field
variable {C:Circuit M N}(Y:Oracle.Program Q)(Φ:∀ P:Patch,P.Branches Q G) (K: Comparison.RG02.Bulk.Chain Γ)(P: SeriesT C Q Γ)
variable (L:Page M→Binding.Scale)
variable (A: X→ Boot.Scout (G:=G) m) (p:ℕ) -- period
local notation:max "U_" p:max k:max=> P.stepData C Γ p k
local notation:max "F_" p:max k:max=> Halo.bios ( P.stepData C Γ p k )
set_option quotPrecheck false
local notation:max "K_" p:max k:max=> ( P.readyKin C Γ K p k )
local notation:max "f_" i:max p:max=> ( Γ.S.side ( P.vol i ) p )
local notation "G₀"=> ( C.payroll Y G Φ L )
abbrev esprit := Profiles.declaring (C.payroll Y G Φ L) (fun i=> (A i).gear) (fun i=> (A i).ranks)
local notation "V!" => ( See.work Φ K P L )
local notation "F!" => ( See.observe Φ K P A L )
def Lifted (i:ℕ) (p:ℕ) (x:Orders (Pin (Γ.S.side i p) G)) : Orders (Foot G):= dawn ( ( HaloA (Γ:=Γ) i ).spring p ) x
lemma Story (i:ℕ)(p:ℕ)(x:Orders (Pin (Γ.S.side i p) G))(y:ℕ)(h:i=y): Lifted (Γ:=Γ) i p x=Lifted y p (See.castF (X:=fun i=> Orders (Pin (Γ.S.side i p) G)) h x):=by subst y;rfl
-- declare rotation relation at each page. cast from Billing.A.Meta.
variable (s:Flap M)
local notation "T₁"=> (C.devices Y G Φ L s)
local notation "G!"=> ( C.bore G Φ L s )
noncomputable abbrev planetx (p:ℕ) := Arm.spins (U_ p s) (F_ p s) (K_ p s)
noncomputable abbrev transM (p:ℕ) := Arm.driftM (U_ p s) (F_ p s) (K_ p s)
abbrev frontV (p:ℕ):= See.Recv P p s (V! p s.prev)
abbrev frontM (p:ℕ):= See.Recv P p s (F! p s.prev)
abbrev forecastL p := Arm.layerSet (U_ p s) (C.bore G Φ L s) (frontV Φ K P L s p)
abbrev starP (p:ℕ):= (StepA P s).spring p
local notation:max "Ψ_" p:max=> ( frontV Φ K P L s p )
local notation:max "Ψ₁" p:max=> ( frontM Φ K P L A s p )
local notation:max "Γ₁" p:max=> ( starP P s p )
local notation:max "H_" p:max=> forecastL Φ K P L s p
-- across proof
local notation "T!" => (( C.payroll Y G Φ L ).bulk s.prev)
local notation "T'"=> (( C.dialect Y G Φ L ).frames s)
-- raw.F exact legislation
structure Holds (i:Page M):Prop where
   meets : ∀ e j, below atTop ((G₀).bulk i e j) fun p=> Lifted (Γ:=Γ) (P.vol i) p ( V! p i ) e j
structure Visited (i:Page M):Prop where
   walks : ∀ e j, above atTop ( ( esprit (C:=C) Y Φ L A ).main i e j ) fun p=> Lifted (Γ:=Γ) (P.vol i) p ( F! p i ) e j
variable (h: Holds Y Φ K P L s.prev)
local notation "k"=> ( P.vol s.next+1 )
include h
lemma utter (i j:ℕ): below atTop ( T! i j ) fun p=> Lifted (Γ:=Γ) (P.vol s.next+1) p ( Ψ_ p ) i j:=by have H:= h.meets i j; simp_rw [ fun p=> Story (Γ:=Γ) _ p ( V! p s.prev ) _ ( P.links s ) ] at H; exact H
lemma premium (i j:ℕ): below atTop ( (T').jVac ( T! ) i j ) fun p=> offer ( Γ₁ p ) (( H_ p ) i j):=by
 unfold forecastL layerSet supply; simp_rw [ Pi.add_apply,pushPlus,Cluster.present, show ∀ p,starP P s p=( ( Fore P s ).spring p ).sumMap ( ( After P s ).spring p ) from fun _=>rfl, Lift.fromFine ]; exact below.plus ( below.offer (utter Y Φ K P L s h i j) Function.Embedding.inl ) ( Fees.primes Φ P L s i j )
lemma paying : Holds Y Φ K P L s.next:=by
 refine ⟨fun i j=>?_⟩; rw [← (C.payroll Y G Φ L).step_v]
 let D:=(C.devices Y G Φ L s); let w:= D.jVac ( T! )
 -- heads on D recall T!
 by_cases hy:j=0; subst j; exact below.note ..
 obtain ⟨hu,h'⟩:= Crown.tendersK Y Φ K P L s
 unfold GridStep.pure; simp_rw [ if_neg hy, See.itinerary ]
 -- target
 have hp(p:ℕ):
  Lifted (Γ:=Γ) _ p (See.riseV Φ K P L p s (V! p s.prev)) i j=
  crop Function.Embedding.inr (Packet.draft (shore (Γ₁ p) (Γ₁ p) (transM K P s p)) (ceaseHeat (shore (Γ₁ p) (Γ₁ p) (planetx K P s p)) (dawn (Γ₁ p) ( H_ p )) true i j ) ):=by
    unfold Lifted Lift.dawn See.riseV Arm.OutputV Binding.pulp; rw [ if_neg hy ]; unfold Arm.scriptV Diagram.collectO; change offer ( ( After P s ).spring p ) (crop Function.Embedding.inr ( Packet.draft _ (_) ))= _
    rw [Lift.rightCrop ( ( Fore P s ).spring p ), Lift.pushDraft]; exact congr_arg₂ Packet.crop rfl ( congr_arg (Packet.draft _) ( congr_fun (congr_fun ( Lift.pose (Γ₁ p) ( H_ p ) (planetx K P s p) true) i) j ) ) -- implicit?
 -- avoid pre-unfold for rw
 simp_rw [hp]; exact below.crop ( below.pull ( closeV ( V:= w ) ( Τ:=fun p=> dawn (Γ₁ p) ( H_ p ) ) (premium Y Φ K P L s h) hu false true _ _ ) h' ) _
omit h
lemma activeV : ∀ i,Holds Y Φ K P L i:= Page.proves (fun x=> ⟨ fun i j=> Fees.weights Γ _ _ (Circuit.serene G L x) i j ⟩ ) (paying Y Φ K P L)
local notation "E"=> ( esprit (C:=C) Y Φ L A )
variable (hT:Visited Y Φ K P L A s.prev)
include hT
lemma billing (i j:ℕ): above atTop ((E).main s.prev i j) fun p=> Lifted (Γ:=Γ) (P.vol s.next+1) p (Ψ₁ p) i j:= by have hp:= hT.walks i j; simp_rw [ fun p=> Story (Γ:=Γ) _ p (F! p s.prev) _ ( P.links s ) ] at hp; exact hp
lemma buying: Visited Y Φ K P L A s.next:=by
 refine ⟨fun i j=>?_⟩; rw [ ← (E).step_m ]; simp_rw [ See.display ]; obtain ⟨hu,hv⟩:= Crown.tendersK Y Φ K P L s; let K₁:=(E).main s.prev -- parentheses
 let T (p:ℕ):= (Arm.columns ( U_ p s ) ( Ψ₁ p ))
 have h(p:ℕ): Lifted (Γ:=Γ) _ p ( See.riseM Φ K P L p s m (V! p s.prev) ( F! p s.prev ) ) i j=
  crop Function.Embedding.inr ( Packet.draft ( shore (Γ₁ p) (Γ₁ p) (transM K P s p) ) (endHeat m (shore (Γ₁ p) (Γ₁ p) (planetx K P s p)) (logHeat (shore (Γ₁ p) (Γ₁ p) (planetx K P s p)) (dawn (Γ₁ p) ( H_ p )) true) (dawn (Γ₁ p) (T p)) i j)):=by
    unfold Lifted Lift.dawn See.riseM Arm.OutputM collectO; change offer ( (After P s).spring p ) (crop Function.Embedding.inr (Packet.draft _ _))= _
    rw [Lift.rightCrop ( (Fore P s).spring p ),Lift.pushDraft]; exact congr_arg (Packet.crop Function.Embedding.inr) (congr_arg (Packet.draft _) (congr_fun (congr_fun ( Lift.dynamics (Γ₁ p) ( H_ p ) (planetx K P s p) true (T p) m) i) j))
 have he (i j:ℕ): above atTop ( ( offer Function.Embedding.inl (K₁ i j) ): Packet ((Foot G)⊕ (Foot G)) j ) fun p=> Lift.dawn (Γ₁ p) (T p) i j:=by
    unfold Lift.dawn T Arm.columns Cluster.present; simp_rw [ show ∀ p,starP P s p=( ( Fore P s ).spring p ).sumMap ( (After P s).spring p ) from fun _=>rfl, Lift.fromFine ]; exact above.offer (billing Y Φ K P L A s hT i j) _
 simp_rw [h]; exact above.crop (above.pull ( closeM (V:= (T').jVac ( T! )) (F₁:= fun i j=> offer Function.Embedding.inl ( (E).main s.prev i j)) (premium Y Φ K P L s (activeV Y Φ K P L s.prev)) he hu false true _ _ _) hv) _ -- binder order V
omit hT
lemma activeM: ∀ i,Visited Y Φ K P L A i:= Page.proves (fun x=> ⟨ fun i j=> Fees.purchases Γ _ (A x) i j ⟩ ) (buying Y Φ K P L A)
end YM.RegulatorIR.FVAAlt2.Pipeline.Near
