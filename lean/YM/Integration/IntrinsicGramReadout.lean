import YM.Integration.IntrinsicPhysicalCell

/-! Complete signed regional Wilson integrals at every readout depth, with
the intrinsic counterterm, all exterior factors and the actual finite
inverse detector on the physical horizon. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.IntrinsicGramReadout
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Cells Extraction
open MergeProof MergeProof.Accent MergeProof.Replicum OPE OPE.Orbits OPE.Therm OPE.Cards
open StressFlux.Matching Frontier6.Road ActualFoundryDetectorSource WilsonWholeLimit EngineeringWeightedReadout
open Trace.Physical.GermGraph RG16.Literal IntrinsicPhysicalCell
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] {d : I → ℕ} {D : ℕ}

/-- The complete regular, forced and exterior source after the same
physical transport to level `m`. -/
def rows (U : Detector S D) (j : ℕ) (x : I → Cover) (v : (i : I) → C.label (d i))
    (w : ℕ × ℕ) (z : C.label D) (m : ℕ) (hm : m ≤ w.1) (i : Fin U.size) : ℂ :=
  ∫ V, (actualSignedTransport C (N:=w.1)
    (numerator C w.1 w.2 (paddedLabels C 0 (fun i => ⟨d i,v i⟩)) ⟨D,z⟩
      (fun k => detectorRaw S (tags S (U.listen i) k)) 0 0
      (paddedPositions (fun k => C.S.gridPoint j (x k))) (OPE.positions S (U.listen i)).ofLp) hm V).part
        (Stock.final (Region (Fin (U.listen i).length))) ∂scene C.path w.1 w.2 m

theorem row_moment (H : C.Makes) (U : Detector S D) (j : ℕ) (x : I → Cover)
    (v : (i : I) → C.label (d i)) (w : ℕ × ℕ) (z : C.label D) (hunit : C.ref 0 ≤ w.1)
    (m : ℕ) (hm : m ≤ w.1) (i : Fin U.size) :
    rows U j x v w z m hm i = moment (C.beta w.1 w.2)
      (physical C w.1 w.2 (paddedLabels C 0 (fun i => ⟨d i,v i⟩)) ⟨D,z⟩
        (fun k => detectorRaw S (tags S (U.listen i) k))
        (paddedPositions (fun k => C.S.gridPoint j (x k))) (OPE.positions S (U.listen i)).ofLp) :=
  normalized_mean C H w.1 w.2 _ _ _ 0 0 hunit _ _ hm

private theorem padded_grid (H : C.Makes) {j N p : ℕ} (hj : j ≤ N) (hunit : C.ref 0 ≤ N)
    (x : I → Cover) (v : (i : I) → C.label (d i)) (z : C.label D) :
    central N p (paddedLabels C 0 (fun i => ⟨d i,v i⟩)) ⟨D,z⟩
      (paddedPositions (fun i => C.S.gridPoint j (x i))) = leafGap C j D d x v N p z := by
  have hz : ceilSite C N p (0 : E4) = 0 := by
    change Lattice.wrap _ (fun _ => ⌈(0:ℝ) / C.S.a N⌉) = 0
    simp only [zero_div, Int.ceil_zero]
    exact (Lattice.wrap _).map_zero
  have site (y : Cover) : ceilSite C N p (C.S.gridPoint j y) = Cells.location C.S j N p y := by
    simpa only [zero_add, hz] using
      (WilsonExteriorGeometry.ceilSite_add_grid (C:=C) (p:=p) hj (0:E4) y)
  funext V
  simp only [central, padded_product H 0 hunit, leafGap, leaves, Pi.sub_apply, Finset.prod_apply,
    site, hz]

/-- This is a bound on the full original marked integral at every
intermediate depth with the same canonical counterterm. -/
def Decoded (H : C.Makes) (U : Detector S D) (J : ℝ → PhysMS.tower S) (r : ℝ)
    (b j : ℕ) (x : I → Cover) (v : (i : I) → C.label (d i)) (w : ℕ × ℕ) (cost : ℝ) : Prop :=
  ∃ (ho : Opened C D b w.2) (live : b ≤ w.1),
    let raw := leaves C j d x v w.1 w.2
    let z := (C.factory D w.1 w.2).terminal (topReport C w.1 w.2 D H b ho live raw)
    Booked C w.1 w.2 D raw b live ∧ ∀ (m : ℕ) (hm : m ≤ w.1),
      ‖wholeReadout U J r (rows U j x v w z m hm)‖ ≤ cost

/-- The physical exterior trains precede all central data. Each actual
inverse column and each exterior engineering dimension retains its price. -/
theorem bank (F : Spec.Final C f S) (U : Detector S D) (δ : ℝ) (hδ : 0 < δ) :
    ∃ b₀ : ℕ, ∃ n : Fin U.size → ℕ, ∃ A : (i : Fin U.size) → Fin (U.listen i).length → ℝ,
      (∀ i k, 0 ≤ A i k) ∧ ∀ᶠ w : ℕ × ℕ in f.fuse,
        ∀ (b j : ℕ), b₀ ≤ b → j ≤ w.1 → ∀ (x : I → Cover) (v : (i : I) → C.label (d i))
          (e : ℝ), Observed F.room.cutoff b j D x v w e → ∀ (J : ℝ → PhysMS.tower S) (r : ℝ),
            Decoded F.room.cutoff U J r b j x v w (columnPrice (wholeReadout U J r)
              (fun i => ∏ k, (A i k * C.S.a (n i) ^ (-((tags S (U.listen i) k).1:ℝ)-δ)+1)) * e) := by
  let dE (i : Fin U.size) (k : Fin (U.listen i).length) := (tags S (U.listen i) k).1
  let ext (i : Fin U.size) (k : Fin (U.listen i).length) : C.label (dE i k) :=
    S.representative _ (tags S (U.listen i) k).2
  let R (i : Fin U.size) (k : Fin (U.listen i).length) : ℝ := 1 + ‖ext i k‖
  have hR (i : Fin U.size) (k : Fin (U.listen i).length) : 0 < R i k :=
    add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _)
  have sep (i : Fin U.size) : Injective (Sum.elim (fun _ : Unit => (0:E4)) (OPE.positions S (U.listen i)).ofLp) :=
    (consIn 0 (OPE.positions S (U.listen i)).ofLp (e:=Equiv.refl _)).mp (generic_conf _ (U.awake i))
  choose t ht q hq n hn A hA H using fun i : Fin U.size =>
    complete_readout (arity:=Fintype.card I) F (dE i) (R i) (hR i) δ hδ
      (OPE.positions S (U.listen i)).ofLp (sep i) 0 0
  refine ⟨Finset.univ.sup q,n,A,hA,?_⟩
  filter_upwards [eventually_all.mpr H,(Cards.largeMesh f).eventually_ge_atTop (C.ref 0)] with w paid hUnit
  intro b j hb hj x v e observed J r
  obtain ⟨ho, live, booked, localGap, rootGap⟩ := observed
  let raw := leaves C j d x v w.1 w.2
  let z := (C.factory D w.1 w.2).terminal (topReport C w.1 w.2 D F.room.cutoff b ho live raw)
  have centralPaid : PaidAt C.S w.1 w.2 b (C.beta w.1 w.2) e
      (central w.1 w.2 (paddedLabels C 0 (fun i => ⟨d i,v i⟩)) ⟨D,z⟩
        (paddedPositions (fun i => C.S.gridPoint j (x i)))) := by
    rw [padded_grid F.room.cutoff hj hUnit]
    exact ⟨live,localGap,rootGap⟩
  refine ⟨ho,live,booked,?_⟩
  intro level hlevel
  apply column_bound_scaled
  intro i
  have he (k : Fin (U.listen i).length) : ‖ext i k‖ ≤ R i k := le_add_of_nonneg_left zero_le_one
  have bound := paid i b ((Finset.le_sup (s:=Finset.univ) (f:=q) (Finset.mem_univ i)).trans hb)
    live (ext i) he _ _ _ e centralPaid 0 0 hUnit level hlevel
  rw [mul_comm] at bound
  exact bound

/-- The full inverse-field conversion costs its exact engineering power.
Each original detector column is scaled against its own exterior price. -/
theorem price_rate (F : Spec.Final C f S) (U : Detector S D) (J : ℝ → PhysMS.tower S)
    (hJ : PhysMS.Leading F J) (A : Fin U.size → ℝ) (hA : ∀ i, 0 ≤ A i) :
    RateLE Trace.Pilot.trail Trace.Pilot.LogV (fun r => columnPrice (wholeReadout U J r) A) (D:ℝ) := by
  let k : ℝ := ∑ i : Fin U.size, A i *
    (‖LinearMap.toContinuousLinearMap U.report‖ * ‖(Pi.single i (1:ℂ) : Fin U.size → ℂ)‖)
  have h := (RateLE.norm (X := S.Field D →L[ℂ] (Climb.Bel C.book).Field D) (PhysMS.Frame.inverse_rate F D J hJ)).mul (RateLE.const k PhysMS.to_log_zoom)
  rw [add_zero] at h
  apply h.transfer
  filter_upwards with r
  have hn : 0 ≤ columnPrice (wholeReadout U J r) A :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hA i) (norm_nonneg _)
  rw [Real.norm_of_nonneg hn]
  apply le_trans _ (Real.le_norm_self _)
  unfold columnPrice k
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact (mul_le_mul_of_nonneg_left (wholeReadout_norm U J r (Pi.single i 1)) (hA i)).trans_eq (by ring)

/-- The finite original row estimate survives the actual inverse Gram
readout, has a 1/32 exponential margin and pays every finite inverse
coupling order on one and the same constructed hierarchy. -/
theorem engineering (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (D : ℕ) (U : Detector S D) (J : ℝ → PhysMS.tower S) (hJ : PhysMS.Leading F J)
    (v : ℝ → (i : I) → C.label (d i))
    (hv : ∀ i k, RateLE Trace.Pilot.trail Trace.Pilot.LogV (fun t => v t i k) (-(d i:ℝ))) :
    ∃ b m j : ℝ → ℕ, ∃ h a c : ℝ, Height C.S Trace.Pilot.trail Trace.Pilot.LogV b h ∧
      Height C.S Trace.Pilot.trail Trace.Pilot.LogV m a ∧ Height C.S Trace.Pilot.trail Trace.Pilot.LogV j c ∧
      0 < h ∧ h < a ∧ a < 1 ∧ 1 < c ∧ ∃ e : ℝ → ℝ,
        RateLE Trace.Pilot.trail Trace.Pilot.LogV e (-(1:ℝ)/32) ∧
        (∀ loop : ℕ, Tendsto (fun r => C.path.levels.clock.hatBeta (j r)^loop * e r)
          Trace.Pilot.trail (𝓝 0)) ∧
        ∀ᶠ r in Trace.Pilot.trail, ∀ x : I → Cover, Plot C (b r) (m r) (j r) x →
          ∀ᶠ w in f.fuse, Decoded F.room.cutoff U J r (b r) (j r) x (v r) w (e r) := by
  obtain ⟨b,m,j,h,a,c,hb,hm,hj,hh,ha,ha₁,hc,e,he,paid⟩ :=
    IntrinsicPhysicalCell.engineering F facility anchor PhysMS.to_log_zoom D v hv
  obtain ⟨b₀,n,A,hA,prices⟩ := bank (d:=d) F U 1 one_pos
  let K (i : Fin U.size) := ∏ k, (A i k * C.S.a (n i)^(-((tags S (U.listen i) k).1:ℝ)-1) + 1)
  have hK (i : Fin U.size) : 0 ≤ K i := Finset.prod_nonneg (fun k _ =>
    add_nonneg (mul_nonneg (hA i k) (Real.rpow_nonneg (C.S.a_pos _).le _)) zero_le_one)
  let out (r : ℝ) := columnPrice (wholeReadout U J r) K * e r
  have result : RateLE Trace.Pilot.trail Trace.Pilot.LogV out (-(1:ℝ)/32) := by
    apply ((price_rate F U J hJ K hK).mul he).mono
    linarith
  refine ⟨b,m,j,h,a,c,hb,hm,hj,hh,ha,ha₁,hc,out,result,?_,?_⟩
  · intro n
    have hh' : RateLE Trace.Pilot.trail Trace.Pilot.LogV out (-((0:ℕ):ℝ)-1/32) := by
      convert result using 1
      norm_num
    simpa only [Nat.cast_zero,zero_mul,Real.exp_zero,one_mul] using
      MultilinearCellCapture.all_loop_orders PhysMS.to_log_zoom 0 out hh' hj n
  · filter_upwards [paid,hb.grows.eventually_ge_atTop b₀] with t good large
    intro x hx
    filter_upwards [good x hx,prices,(Cards.largeMesh f).eventually_ge_atTop (j t)] with w observed bankAt hw
    exact bankAt (b t) (j t) large hw x (v t) _ observed J t

end YM.Integration.IntrinsicGramReadout
