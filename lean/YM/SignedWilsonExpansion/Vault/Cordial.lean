import YM.Integration.WilsonMeasuredPublicEntranceTransferSubmitted
import YM.Integration.WilsonOriginalGeneralRosterFare
import YM.Integration.WilsonAddressedPublicGridRooms
import YM.SignedWilsonExpansion.Vault.Dossier
/-! literal conversion; ages paid prior to prescription.Seams. Harvest phase continuation on exact same mesh. -/
set_option autoImplicit false
set_option maxHeartbeats 280000
noncomputable section
namespace YM.Integration.Election.VaultM.Cordial
open Function Finset Set Filter MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonOriginalGeneralRosterFare (rotation debit)
open WilsonMeasuredPublicEntranceCellWords (physical submitted)
open WilsonMeasuredPublicEntranceTransferSubmitted (vector)
open WilsonMeasuredPublicEntranceTransferWord (field price)
open RG05Readout RG05Readout.Address RG05Readout.Records Marker Cells HeartT HeartT.Spritz
open WilsonReflectedPublicOrientedFaces (displayed)
open WilsonThermometerReflectedTrajectory (anchorAt)
open SignedWilsonExpansion Homes Purchases UVClock Schedules StageG Camera SignedWilsonExpansion.Vault Asymptotics
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {n:ℕ} {N per f K v pwr b t w:ℕ} {d:Fin n→ℕ}
variable {fk:f≤K}{cut:K≤N}{B:ℝ}
local notation "C₀"=> R.family
structure Pane (F:Filed R d K) (A:Panel R d N per f K fk cut t pwr b B) (x:Fin n→ Cover)
    (U Υ : (i:Fin n)→ R.family.label (d i)): Prop where
    namesEq : A.names=U
    seats : A.loc=wrap (C₀|>.side f per) ∘ x
    stations : A.slot=F.station
    home : A.axis=F.A N per
    motion : A.turn=fun _=>Motion.nil
    vote : Υ = vector R d A
namespace Pane
variable {F: Filed R d K} {A:Panel R d N per f K fk cut t pwr b B} {x:Fin n→ Cover} {U Υ : (i:Fin n)→ R.family.label (d i)}
variable (z:Pane R F A x U Υ) (s: Finset (Fin n))
include z
abbrev capM (s:Finset (Fin n)):(Stock.census (Fin n)).Mode:= ⟨s,Finset.mem_univ _⟩
omit z in
abbrev feeF (M:Fin n→ℝ)(s: Finset (Fin n)) := ( ∏i∈s,Motion.orbitCost ((C₀).labels.level (d i))*M i ) + ( ∏i∈s, WilsonAddressedHomeDose.ceiling (R:=R) (d i) ( M i ) )
omit z in
lemma debitF (M: Fin n→ℝ)(s: Finset (Fin n)) : debit (R:=R) d M f w (capM s)= feeF (d:=d) R M s* (( boilerM C₀ f)^w)⁻¹:= (add_mul ..).symm -- verifies add_mul
omit z in
lemma aimF (h:A.turn=fun _=>Motion.nil) : vector R d A= fun i=> states C₀ (d i) ( A.slot i ) N per K ( A.names i ) ( A.axis i ) :=by
    funext i; unfold vector states; rw [ h,Motion.patch_id ]; rfl
lemma mic_stem : physical ( f:= f ) R d (N:=N) ( per:=per ) A.names A.turn A.loc ( capM s )= stemN C₀ d x U f N per s:=by
    rw [z.namesEq,z.motion,z.seats]; unfold physical stemN stroke micT; funext X; apply Finset.prod_congr rfl; intro i _; rw [WilsonAddressedPublicGridRooms.top R ( fk.trans cut ), show displayed R (d i) (U i) Motion.nil=U i from by simp [Motion.nil,displayed, show (1:Signed).ortho=1 from map_one Signed.inclusionO] ]; unfold location; rw[dif_pos (fk.trans cut) ]; rfl
lemma home_stem : field (N:=N) R d (vector R d A) (location (C₀).S f K per∘ x ) s= stemK C₀ d x Υ f N per K s:=by rw [z.vote]; rfl
lemma K_stem : submitted R d (N:=N) (per:=per) F fk A.names A.turn A.loc (capM s) = stemK C₀ d x Υ f N per K s:=by
    rw [WilsonMeasuredPublicEntranceTransferSubmitted.original R d A F z.stations z.home (capM s),z.seats]; have h: (fun i=> (( C₀|>.S.toDepth fk per ).embed ( ( wrap (C₀|>.side f per) ∘ x ) i )))= location (( C₀ ).S) f K per∘ x :=by funext i; unfold Function.comp location; rw[dif_pos fk]
    rw [h]; exact z.home_stem R s
lemma planted {q:ℕ} (h:q≤K) (M:Fin n→ℝ) (pay:‖(C₀).omega N per (physical R d (N:=N) A.names A.turn A.loc (capM s))-actualTransport C₀ (N:=N) (submitted R d (N:=N) F fk A.names A.turn A.loc (capM s)) h 1‖≤debit (R:=R) d M f w (capM s)) : ‖natureL C₀ d x U f N per s-born₀ C₀ d x Υ f N per q K s‖≤ feeF R (d:=d) M s*((boilerM C₀ f)^w)⁻¹:=by
     rw [z.mic_stem R s, lodgeTop C₀ _ R.makes, z.K_stem R s, debitF] at pay; rw [ born₀,dif_pos h]; exact pay
-- retire restored uniform cap; every s
lemma permit (hv:0≤B)(L:ℕ)(h:WilsonAddressedFiniteGuardCapital.power R d pwr s≤L)(y:Config G (R.family.side K per)) : ‖stemK C₀ d x Υ f N per K s y‖ ≤ WilsonAddressedFiniteGuardCapital.price R d B s * (boilerM C₀ K)^L :=by
    rw [← z.home_stem R]; let P:= price (N:=N) (K:=K) (p:=per) R d (vector R d A) s; have hP:= WilsonMeasuredPublicEntranceTransferWord.gross (N:=N) (K:=K) (p:=per) R d (vector R d A) (location ((C₀).S) f K per ∘ x) s y; exact hP.trans ( ( ( le_mul_of_one_le_left ((norm_nonneg _).trans hP) one_le_two ).trans (WilsonMeasuredPublicEntranceTransferSubmitted.capital R d A s hv) ).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ((C₀).path.levels.fits.delayed K).le h) ( WilsonAddressedFiniteGuardCapital.price_nonneg R d hv s )) )
end Pane
end YM.Integration.Election.VaultM.Cordial
end
