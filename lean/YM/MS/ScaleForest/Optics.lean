import YM.MS.ScaleForest.Inputs
import YangMills.WilsonProof.NativeSupport.YM.FVA2.Position.Table
import YM.Integration.FVA1Physical.Exchange.ContinuumLimitDeck

/-!
# Fixing the physical source (including its continuation)

The two apparently independent lift prescriptions actually agree on all the
auxiliary dimensions and all BIndex columns, *before* using the measured
frames. This doesn't rely on a gauge transformation or follow just by matching their
four-dimensional labels. Nor is it needed in using some of the existing
calibrations. We want to know it to describe our graph and match the Laurent
germs, and because all the lower-column counterterms have to act on the
same operand.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Function Real
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color
open Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Motif Literal Mach Halo Emit Local.Physical Land
open FVA2.Position FVA2.Position.OpenAxis WilsonMS
open scoped Topology ContDiff

variable {G : Gauge} {m h n : ℕ}

theorem axes_ray (z : ℂ) (a b : Axis) (x : E4) (n : ℕ) :
    graft (G:=G) (m:=m) z a b x n = JRad.rayF z x a b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [JRad.rayF, pow_succ']; change _= JRad.direction G m z x (JRad.rayF z x a b n)
    rw [graft_add, ih, JRad.direction, LinearMap.sum_apply]; rfl

theorem common_ramp (X : OpenAxis.Coord G h) : Ramp G h (asC G h X) = JRad.factor G h X := by
  let L := (Ramp G h).restrictScalars ℝ ∘ₗ asC G h
  have he : X ∈ Submodule.span ℝ (Samples G h) := by rw [many]; exact Submodule.mem_top
  change L X = _
  refine Submodule.span_induction (p:= fun X _ => L X=JRad.factor G h X) ?_ ?_ ?_ ?_ he
  · rintro _ ⟨a,x,c,rfl⟩; funext z m
    change Ramp G h (asC G h (Prong a x c)) z m= JRad.factor G h (JRad.reading G h x a c) z m
    rw [ramp_Jrad, JRad.corresponding]
    simp_rw [OpenAxis.Ray,JRad.node,axes_ray]; rfl
  · rw [map_zero,map_zero]
  · intro a b ha hb hx hy; rw [map_add,map_add,hx,hy]
  intro c i hi hx; rw [map_smul,map_smul,hx]

theorem common_X (i : Labels.Key G) : seed G (MvPolynomial.X i) = JRad.optic G (MvPolynomial.X i) := by
  rw [seed_x, sampleC, common_ramp,JRad.names]

theorem common_label (A : Labels.Pol G) : seed G A = JRad.optic G A := by
  induction A using MvPolynomial.induction_on with
  | C a => rw [sightC]; exact funext fun z => funext fun n => (JRad.constV a).symm
  | mul_X A i ih => funext z m; rw [seed_p, JRad.productV,ih,common_X]
  | add A B hA hB => rw [map_add,map_add,hA,hB]

theorem common_column (A : Theater.Film0 G h n) :
    invoice G h n A = (JRad.literature A.property).choose := by
  refine OpenAxis.ticket_eq _ _ fun z => ?_
  rw [OpenAxis.priceR,common_label]
  exact (congr_fun ((JRad.literature A.property).choose_spec.1) z).symm

theorem common_optics (G : Gauge) : Plot (Ensure.deck G)= JRad.book G := by
  have ext {B : Deck G} (T X : Land.Booked B) (he : T.optics=X.optics) : T=X := by
    cases T; cases X; cases he; rfl
  apply ext
  funext d i
  exact common_column _

local notation "Π" G=> FVA2.Press.portDeck G

theorem common_native (G : Gauge) :
    Integration.FVA1Physical.Exchange.continuumLimit_deck G ▸ Plot (Π G) = JRad.book G := by
  have note {A B : Deck G} (h : A=B) : (h ▸ Plot A : Land.Booked B)=Plot B := by cases h; rfl
  exact (note (Integration.FVA1Physical.Exchange.continuumLimit_deck G)).trans (common_optics G)


theorem across_ensure (T : MS_Data G (Plot (Ensure.deck G))) (F : MS_Data G (JRad.book G))
    (v : Land.Plaid (Ensure.deck G) h) :
    T.poles h v=F.poles h v ∧ ∀ n, Pact (T.marks h v n) (F.marks h v n) := by
  have ht := T.markOK h v
  have hV : (Plot (Ensure.deck G)).optics h v=(JRad.book G).optics h v := by rw [common_optics]
  rw [hV] at ht
  exact unique_M ht (F.markOK h v) (unique_B T.bulkOK F.bulkOK).2

theorem across_decks (T : MS_Data G (Plot (Π G))) (F : MS_Data G (JRad.book G))
    (u : Plaid (Π G) h) :
    let v : Plaid (Ensure.deck G) h := Integration.FVA1Physical.Exchange.continuumLimit_deck G ▸ u
    T.poles h u = F.poles h v ∧ ∀ i, Pact (T.marks h u i) (F.marks h v i) := by
  intro v
  have he : (Plot (Π G)).optics h u = (JRad.book G).optics h v := by
    have H {B B' : Deck G} (hX : B=B') (i : Plaid B h) :
        (Plot B).optics h i = (Plot B').optics h (hX ▸ i) := by cases hX; rfl
    rw [← common_optics]; exact H _ _
  have hx := T.markOK h u
  rw [he] at hx
  exact unique_M hx (F.markOK h v) (unique_B T.bulkOK F.bulkOK).2

end YM.MS.ScaleForest
