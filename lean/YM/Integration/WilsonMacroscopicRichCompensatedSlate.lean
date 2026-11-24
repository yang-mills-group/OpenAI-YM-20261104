import YM.Integration.WilsonMeasuredReportingProduct
import YM.Integration.ActualFoundryDetectorReadout

/-! The same fixed-scale coefficient in the complete incoming product and a separated physical slate. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichCompensatedSlate
open Function Filter Set Lattice Wilson Cells Extraction OPE OPE.Cards PhysMS
open RG MergeProof OPE.Orbits Spec RG16 RG16.Literal Trace.Physical.GermGraph MergeProof.Accent PhysicalNext.Repeat.Legato
open FilteredIntrinsicGramReadout WilsonMixedPlacement WilsonExteriorTrains
open Frontier6.Road StressFlux.Matching ActualFoundryDetectorSource
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I E : Type} [Fintype I] [Nonempty I] [Fintype E] {d : I → ℕ}

def gap (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → tower S) (h u m : ℕ) (w : ℕ×ℕ) (door : Opened C h u w.2) (live : u ≤ w.1)
    (ρ : ℝ) (x : I → Cover) (v : (i : I) → (Climb.Bel C.book).Field (d i)) :
    Config G (C.side w.1 w.2) → ℂ :=
  let Y := FilteredWilsonProduct.field F R J v (C.S.a m*ρ) m x w
  Y - C.O w.1 w.2 ((C.factory h w.1 w.2).terminal
    (topReport C w.1 w.2 h F.room.cutoff u door live Y)) 0

/-- Arbitrary adjoint choices at different replicas and on different exterior fields. -/
def orient {n : Side} (a : Bool) (A : Config G n → ℂ) : Config G n → ℂ :=
  if a then fun U => star (A U) else A

private theorem funded {N p j : ℕ} {B : ℝ} {A : Config G (C.side N p) → ℂ}
    (ticket : PaidAt C.S N p j (C.beta N p) B A) (a : Bool) :
    PaidAt C.S N p j (C.beta N p) B (orient a A) := by
  cases a
  · exact ticket
  · exact ticket.stars

/-- The signed, normalized mixed Wilson integral. Each copy may contain its own incoming product. -/
def trainMoment (C : Family G) {copies : ℕ} (b t : ℕ) (w : ℕ×ℕ) (outside : E → E4)
    (A : Fin copies → Config G (C.side w.1 w.2) → ℂ) (de : E → ℕ)
    (z : Fin copies → (i : E) → C.label (de i)) (hand : Fin copies → Bool)
    (extHand : Fin copies → E → Bool) : ℂ :=
  moment (C.beta w.1 w.2) (fun U =>
    (∏ i : Fin copies × Unit, orient (hand i.1) (A i.1)
      (translate (ceilSite C w.1 w.2 (train C b t i.1 0)) U)) *
    ∏ e : Fin copies × E, orient (extHand e.1 e.2) (C.O w.1 w.2 (z e.1 e.2) 0)
      (translate (ceilSite C w.1 w.2 (train C b t e.1 (outside e.2))) U))

/-- The exterior registration, $b$, $u$, and its tariff precede the inner scale and all UV regulators. -/
theorem original (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → tower S) (H : Leading F J) (fac : Facilities C f S)
    (pace : ∀ m, ((C.S.block m).val : ℝ) ≤ Real.log (Lambda C.path.levels m))
    (h : ℕ) (η M B : ℝ) (hη : 0<η) (hM : 0<M) (hB : 20<B)
    (outside : E → E4) (sep : Injective (Sum.elim (fun _ : Unit => (0:E4)) outside))
    (de : E → ℕ) (cap : E → ℝ) (positive : ∀ i,0<cap i) (δ : ℝ) (hδ : 0<δ) :
    ∃ b n top u : ℕ, ∃ T : Stop C h top u, ∃ K : E → ℝ, (∀ e,0 ≤ K e) ∧
      ∀ σ : ℝ, 0 ≤ σ → σ < 1 / 16 → ∀ᶠ m : ℕ in atTop, 
        ∃ (hstop : u ≤ m),
      ∀ copies : ℕ, ∀ᶠ t : ℕ in atTop, ∀ᶠ w : ℕ×ℕ in f.fuse, ∃ (live : m < w.1),
      ∀ (ρ : Fin copies → ℝ) (x : Fin copies → I → Cover)
        (v : Fin copies → (i : I) → (Climb.Bel C.book).Field (d i))
        (z : Fin copies → (e : E) → C.label (de e)) (hand : Fin copies → Bool)
        (extHand : Fin copies → E → Bool),
        (∀ j, Tuple C M η B m (ρ j) (x j)) → (∀ j i, ‖v j i‖≤1) → (∀ j e, ‖z j e‖≤cap e) →
        let Y j := FilteredWilsonProduct.field F R J (v j) (C.S.a m*ρ j) m (x j) w
        let A j := gap F R J h u m w (T.doors w.2) (hstop.trans live.le) (ρ j) (x j) (v j)
        let fee := (Fintype.card (Grades d):ℝ)*((C.S.a m)^h * Real.exp (-σ*C.S.scale m))
        (∀ j, Booked C w.1 w.2 h (Y j) u (hstop.trans live.le) ∧
          PaidAt C.S w.1 w.2 top (C.beta w.1 w.2) fee (A j)) ∧
        ‖trainMoment C b t w outside A de z hand extHand‖ ≤
          (fee*(∏ e, (K e*C.S.a n^(-(de e:ℝ)-δ)+1)))^copies := by
  obtain ⟨n₀,K,positiveK,ext⟩ := exterior_bounds F de cap positive δ hδ
  obtain ⟨b,_,q,_,n,hn,hbq,hqn,sited⟩ := placements (C:=C) f (fun _ : Unit => 0) outside sep 0 0 n₀
  obtain ⟨_,_,_,L⟩ := fac.costlier
  obtain ⟨top,⟨⟨u,hu⟩,htop⟩⟩ := ((forStop C fac.simpleGate L.toPackage h).and (eventually_ge_atTop q)).exists
  let T := hu h le_rfl
  refine ⟨b,n,top,u,T,K,positiveK,?_⟩
  intro σ hσ low
  filter_upwards [WilsonMeasuredReportingProduct.measured (d:=d) F R J H fac pace h top u T η M B hη hM hB σ hσ low] with m bought
  obtain ⟨hstop,branches⟩ := bought
  refine ⟨hstop,fun copies => ?_⟩
  filter_upwards [sited copies] with t placed
  filter_upwards [placed,(largeMesh f).eventually_ge_atTop (m+1),(largeMesh f).eventually_ge_atTop top,ext n ((le_max_right q n₀).trans hn) 1 one_pos] with w seat late topLive outer
  obtain ⟨seat⟩ := seat
  obtain ⟨op,read⟩ := branches w.2
  refine ⟨late,?_⟩
  intro ρ x v z hand extHand geometry norm exterior
  let A j := gap F R J h u m w (T.doors w.2) (hstop.trans (Nat.le_of_lt late)) (ρ j) (x j) (v j)
  let fee := (Fintype.card (Grades d):ℝ)*((C.S.a m)^h * Real.exp (-σ*C.S.scale m))
  have paid (j : Fin copies) := read w.1 late (ρ j) (x j) (v j) (geometry j) (norm j)
  simp only [receipt,dress_inverse] at paid
  refine ⟨fun j => paid j,?_⟩
  exact (by
    have bound := seat.price F.room.cutoff htop topLive
      (fun _ : Unit => fee) (fun e => K e*C.S.a n^(-(de e:ℝ)-δ)+1)
      (fun i => orient (hand i.1) (A i.1))
      (fun j => orient (extHand j.1 j.2) (C.O w.1 w.2 (z j.1 j.2) 0))
      (fun i => funded (paid i.1).2 _) (fun j => funded (outer (z j.1) (exterior j.1) j.2) _)
    simpa only [trainMoment,Fintype.prod_unique] using bound)

end YM.Integration.WilsonMacroscopicRichCompensatedSlate
