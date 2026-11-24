import YM.Integration.FilteredIntrinsicGramReadout

/-! Assembly of the complete physical product of graded moving-frame
inputs and the canonical counterterm of its actual signed density. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FilteredWilsonProduct
open Function Filter MeasureTheory Lattice Wilson RG Cells OPE OPE.Orbits OPE.Cards 
open StressFlux.Matching Frontier6.Road EngineeringWeightedReadout WilsonWholeLimit ActualFoundryDetectorSource
open Trace.Pilot Trace.Physical.GermGraph RG16.Literal MultilinearCellCapture
open FilteredIntrinsicGramReadout IntrinsicGramReadout
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] {d : I → ℕ} {D : ℕ}

/-- Physical moving-frame field formed by summing each slot's genuine
homogeneous cutoff representatives before multiplying the original insertions. -/
def field (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (v : (i : I) → (Climb.Bel C.book).Field (d i))
    (t : ℝ) (j : ℕ) (x : I → Cover) (w : ℕ × ℕ) : Config G (C.side w.1 w.2) → ℂ :=
  ∏ i, ∑ u : Fin (d i+1), C.O w.1 w.2
    (S.representative _ (R.cutTest u.val (d i) (J t (d i) (v i)))) (location C.S j w.1 w.2 (x i))

theorem field_expansion (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (v : (i : I) → (Climb.Bel C.book).Field (d i))
    (t : ℝ) (j : ℕ) (x : I → Cover) (w : ℕ × ℕ) :
    field F R J v t j x w = ∑ g : Grades d, leaves C j (levels g) x (component F R J v g t) w.1 w.2 := by
  funext V
  simp only [field,leaves,component,levels,Finset.prod_apply,Finset.sum_apply,Fintype.prod_sum]

def listen (U : Detector S D) (i : Fin U.size) (w : ℕ × ℕ) : Config G (C.side w.1 w.2) → ℂ :=
  ∏ k, C.O w.1 w.2 (detectorRaw S (tags S (U.listen i) k)).2
    (ceilSite C w.1 w.2 ((OPE.positions S (U.listen i)).ofLp k))

private theorem factor_cont {K : Type} [Fintype K] {m : K → ℕ} (w : ℕ × ℕ)
    (v : (k : K) → C.label (m k)) (x : K → Site (C.side w.1 w.2)) :
    Continuous (∏ k, C.O w.1 w.2 (v k) (x k)) := by
  rw [show (∏ k, C.O w.1 w.2 (v k) (x k)) =
    fun U => ∏ k, C.O w.1 w.2 (v k) (x k) U from funext fun U => Finset.prod_apply ..]
  exact continuous_finsetProd _ fun k _ => C.continuousO ..

private theorem row_formula {m : I → ℕ} (H : C.Makes) (U : Detector S D) (j : ℕ) (x : I → Cover)
    (v : (i : I) → C.label (m i)) (w : ℕ × ℕ) (z : C.label D) (hunit : C.ref 0 ≤ w.1) (hj : j≤w.1)
    (a : ℕ) (ha : a ≤ w.1) (i : Fin U.size) :
    rows U j x v w z a ha i = moment (C.beta w.1 w.2) ((leaves C j m x v w.1 w.2 -
      C.O w.1 w.2 z 0) * listen U i w) := by
  rw [row_moment H U j x v w z hunit a ha i]
  apply congrArg (moment (C.beta w.1 w.2))
  have zero : ceilSite C w.1 w.2 (0:E4) = 0 := by
    change Lattice.wrap _ (fun _ => ⌈(0:ℝ)/C.S.a w.1⌉) = 0
    simp only [zero_div,Int.ceil_zero]
    exact (Lattice.wrap _).map_zero
  have sample (y : Cover) : ceilSite C w.1 w.2 (C.S.gridPoint j y) = location C.S j w.1 w.2 y := by
    simpa only [zero_add,zero] using WilsonExteriorGeometry.ceilSite_add_grid (C:=C) (p:=w.2) hj (0:E4) y
  funext V
  simp only [physical, padded_product H 0 hunit, leaves,listen,Pi.sub_apply,Pi.mul_apply,
    Finset.prod_apply,zero,sample]

def label (H : C.Makes) {w : ℕ × ℕ} {b : ℕ} (ho : Opened C D b w.2) (hb : b ≤ w.1)
    (u : Config G (C.side w.1 w.2) → ℂ) :=
  (C.factory D w.1 w.2).terminal (topReport C w.1 w.2 D H b ho hb u)

/-- One original signed physical moment with one counterterm, paired with
each full exterior train in the prescribed detector. -/
def original (U : Detector S D) (w : ℕ × ℕ) (Y : Config G (C.side w.1 w.2) → ℂ)
    (z : C.label D) (i : Fin U.size) :=
  moment (C.beta w.1 w.2) ((Y - C.O w.1 w.2 z 0) * listen U i w)

def Finished (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (U : Detector S D) (v : (i : I) → (Climb.Bel C.book).Field (d i))
    (t : ℝ) (b j : ℕ) (x : I → Cover) (w : ℕ × ℕ) (price : ℝ) : Prop :=
  ∃ (ho : Opened C D b w.2) (live : b ≤ w.1),
    let Y := field F R J v t j x w
    let Yg (g : Grades d) := leaves C j (levels g) x (component F R J v g t) w.1 w.2
    let Z := label F.room.cutoff ho live Y
    let Zg (g : Grades d) := label F.room.cutoff ho live (Yg g)
    Booked C w.1 w.2 D Y b live ∧ Z = ∑ g, Zg g ∧
      (∀ (a : ℕ) (ha : a ≤ w.1), original U w Y Z =
        ∑ g : Grades d, rows U j x (component F R J v g t) w (Zg g) a ha) ∧
      ‖wholeReadout U J t (original U w Y Z)‖ ≤ price

/-- Finite signed assembly holds for every cutoff in the common sector bank. -/
theorem assemble (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (U : Detector S D) (v : (i : I) → (Climb.Bel C.book).Field (d i))
    (t : ℝ) (b j : ℕ) (x : I → Cover) (w : ℕ × ℕ) (hunit : C.ref 0 ≤ w.1) (hj : j ≤ w.1)
    (price : Grades d → ℝ)
    (paid : ∀ g, Decoded F.room.cutoff U J t b j x (component F R J v g t) w (price g)) :
    Finished F R J U v t b j x w (∑ g, ‖price g‖) := by
  obtain ⟨ho,live,_⟩ := paid (fun _ => 0)
  let Y := field F R J v t j x w
  let Yg (g : Grades d) := leaves C j (levels g) x (component F R J v g t) w.1 w.2
  let Z := label F.room.cutoff ho live Y
  let Zg (g : Grades d) := label F.room.cutoff ho live (Yg g)
  have hsum : Y = ∑ g, Yg g := field_expansion F R J v t j x w
  have hct (g : Grades d) : Continuous (Yg g) :=
    factor_cont w (component F R J v g t) _
  have hg (g : Grades d) : Booked C w.1 w.2 D (Yg g) b live ∧
      ∀ a (ha : a ≤ w.1), ‖wholeReadout U J t (rows U j x (component F R J v g t) w (Zg g) a ha)‖ ≤ price g := by
    obtain ⟨_,_,book,reading⟩ := paid g
    exact ⟨book,reading⟩
  have receipts := IntrinsicProductLinearity.booked_sum C w.1 w.2 D b F.room.cutoff ho live
    (fun _ : Grades d => (1:ℂ)) Yg hct (fun g => (hg g).1)
  simp only [one_smul, ← hsum] at receipts
  have counter : Z = ∑ g, Zg g := by
    dsimp only [Z,Zg,label]
    rw [receipts.2,map_sum]
  have read (a : ℕ) (ha : a ≤ w.1) : original U w Y Z =
      ∑ g : Grades d, rows U j x (component F R J v g t) w (Zg g) a ha := by
    funext i
    simp only [Finset.sum_apply, row_formula F.room.cutoff U j x _ w _ hunit hj a ha i]
    let phi := (C.linearO w.1 w.2 D 0).mk' _
    let spec := listen U i w
    have hc : Continuous spec :=
      factor_cont w (fun k => (detectorRaw S (tags S (U.listen i) k)).2) _
    have hi (g : Grades d) : Integrable ((Yg g - phi (Zg g)) * spec) (law G (C.side w.1 w.2) (C.beta w.1 w.2)) :=
      Wilson.continuous_integrable _ ((hct g).sub (C.continuousO ..) |>.mul hc)
    change (∫ V, ((Y - phi Z) * spec) V ∂law G _ _) = ∑ g,
      ∫ V, ((Yg g - phi (Zg g)) * spec) V ∂law G _ _
    rw [← integral_finsetSum Finset.univ (fun g _ => hi g)]
    apply integral_congr_ae
    filter_upwards with V
    rw [hsum,counter,map_sum]
    simp only [Finset.sum_apply,Pi.mul_apply,Pi.sub_apply]
    rw [← Finset.sum_sub_distrib,Finset.sum_mul]
  refine ⟨ho,live,receipts.1,counter,read,?_⟩
  change ‖wholeReadout U J t (original U w Y Z)‖ ≤ _
  rw [read 0 (Nat.zero_le _),map_sum]
  exact (norm_sum_le ..).trans (Finset.sum_le_sum (fun g _ =>
    ((hg g).2 0 (Nat.zero_le _)).trans (Real.le_norm_self _)))

theorem engineering (F : Spec.Final C f S) (fac : Facilities C f S) (anchor : I)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (U : Detector S D) (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J)
    (v : (i : I) → (Climb.Bel C.book).Field (d i)) :
    ∃ b m j : ℝ → ℕ, ∃ h a c : ℝ, Height C.S trail LogV b h ∧ Height C.S trail LogV m a ∧
      Height C.S trail LogV j c ∧ 0 < h ∧ h < a ∧ a < 1 ∧ 1 < c ∧
      ∃ e : ℝ → ℝ, RateLE trail LogV e (-(1:ℝ)/32) ∧
      (∀ n : ℕ, Tendsto (fun t => C.path.levels.clock.hatBeta (j t)^n * e t) trail (𝓝 0)) ∧
      ∀ᶠ t in trail, ∀ x : I → Cover, Plot C (b t) (m t) (j t) x → ∀ᶠ w in f.fuse,
        Finished F R J U v t (b t) (j t) x w (e t) := by
  obtain ⟨b,m,j,h,a,c,hb,hm,hj,hh,ha,h₁,hc,e,he,hloop,paid⟩ :=
    FilteredIntrinsicGramReadout.sectors F fac anchor R U J H v
  refine ⟨b,m,j,h,a,c,hb,hm,hj,hh,ha,h₁,hc,fun t => ∑ g, ‖e g t‖,
    RateLE.sum PhysMS.to_log_zoom (fun g _ => (he g).norm),hloop,?_⟩
  filter_upwards [paid] with t hp
  intro x hx
  filter_upwards [hp x hx,(Cards.largeMesh f).eventually_ge_atTop (C.ref 0),
    (Cards.largeMesh f).eventually_ge_atTop (j t)] with w rows hu hj'
  exact assemble F R J U v t (b t) (j t) x w hu hj' _ rows

end YM.Integration.FilteredWilsonProduct
