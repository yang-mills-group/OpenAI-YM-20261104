import YM.Integration.WilsonIndependentFreshFiniteWage
import YM.Integration.WilsonIndependentFreshReel
import YM.RegulatorIR.Tape.Poles
import YM.RegulatorIR.Ledger.Terminal

/-! Reuse the genuine terminal Gaussian and Haar invoice after inserting a
mark at an interior date. The actual quiet at that date can have winding. -/
noncomputable section
namespace YM.Integration.WilsonIndependentFreshQuietEnding
open RegulatorIR RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Taping
open RegulatorIR.StopB Lattice RegulatorIR.Binding RegulatorIR.Laplace RegulatorIR.Quadratic RegulatorIR.Geometry
open Budget Budget.Packet Budget.Layer Budget.Tuple Budget.Deck Budget.Tariff Uniform Uniform.Post Function Step Diagram Gradient Spatial
open scoped ENNReal Classical
variable {W : Type} {M : W → ℕ} {G : Gauge} {n : Page M → Side} {L : Meter W}
variable {S : Heir n G} (H : Reel S) {p u q e r : ℕ}

private def endpoint (j : W → Page M) (u p : ℕ) : Prop :=
  Beam L (fun w => S.maximal.per u (j w)) (fun w => H.vapors (j w)) ∧
  (∀ i, i ≤ p → ∀ r, Workday L (fun w => S.maximal.per u (j w))
    (fun w => charter G (n (j w)) i r)) ∧ (∀ w, Vacuum (charter G (n (j w))))

theorem actual (stop : Choice M) (ending : H.Endings L) :
    (stop.after.expanse S).Epoch (WilsonIndependentFreshReel.margins H stop.after) L u p := by
  have year := H.year L ending u p
  have paid : endpoint H (L := L) (Page.finallyW M) u p := ⟨year.vane, year.sphere, year.positive⟩
  have same : (fun w => stop.after.page (Page.finallyW stop.after.spans w)) = Page.finallyW M :=
    funext stop.finalPage
  rw [← same] at paid
  exact ⟨paid.1, paid.2.1, paid.2.2⟩

section Quiet
variable {X Y : Page M → Type} (S : Sky X Y) (T : S.Accounts) (F : Margins Y)
variable (fin : S.Epoch F L 0 p)

include fin in
theorem salary (R : WilsonIndependentResidentWinding.Resident S T 1 q p L)
    (he : e ≤ p) : Workday L (S.landQ 0) (fun w => S.stump T F w e r) := by
 apply Workday.add _ (fin.sphere e he r)
 have hhR :Workday (coverL M L) (S.census.per 1) (fun w=> (S.maps w).deckSum (T.bulk w e r)):= S.census.deck_work (S.census.writes (R.space.bulk_price e he r) (by omega)) fun w=>R.space.bulk_deck w e r he
 have hp : Workday (coverL M L) (S.census.per 1) (fun w=>T.orb w e r):=by
   by_cases h:0<r
   · have hf:= Claim.submits (R.prior e he r h) (Poly.oneQ ..)
     convert Workday.add hf hhR using 1; ext1 w; unfold Accounts.change; rw [sub_add_cancel]
   have hh:r=0:= by omega
   subst r
   exact ⟨_,Poly.zeroQ _,fun _ i=>Fin.elim0 i⟩
 obtain ⟨f,hf,Hf⟩:= hp.us (Page.finallyW M)
 refine ⟨_,hf,fun w i z=>?_⟩
 let j:= Page.finallyW M w
 apply le_trans _ (Hf w i z)
 refine quota_mono _ (fun y : Hold i z=> Tariff.diam_mono ?_ _)
 intro x y
 let d:= Spatial.distance (S.P w) ((S.maps j).atO x) ((S.maps j).atO y)
 change amount (S.radius j) 0 d ≤ amount (S.l j) 1 d
 apply le_trans _ (moment_mono (S.hl j) (show 0≤1 from by omega) (show 0≤d from Spatial.distance_nonneg ..))
 have hv:0≤d:= Spatial.distance_nonneg ..; have hp':S.l j ≤ S.radius j:=le_max_right ..; have h₁:= S.hl j; unfold amount; gcongr

end Quiet

end YM.Integration.WilsonIndependentFreshQuietEnding
