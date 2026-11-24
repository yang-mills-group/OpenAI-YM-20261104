import YM.Integration.IntrinsicGramReadout
import YM.PhysMS.Frame.Apply

/-! Degree-resolved physical moving-frame inputs on a single finite
hierarchy. The sector cuts are the ones supplied by the actual Reader. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FilteredIntrinsicGramReadout
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Cells Extraction
open MergeProof MergeProof.Accent MergeProof.Replicum OPE OPE.Orbits OPE.Therm OPE.Cards
open StressFlux.Matching Frontier6.Road ActualFoundryDetectorSource WilsonWholeLimit EngineeringWeightedReadout
open Trace.Pilot Trace.Physical.GermGraph RG16.Literal IntrinsicPhysicalCell
open MultilinearCellCapture FundedIntrinsicProduct FundedIntrinsicReadout
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I : Type} {d : I → ℕ} {D : ℕ}

abbrev Grades (m : I → ℕ) := (i : I) → Fin (m i + 1)
abbrev levels (g : Grades d) (i : I) : ℕ := (g i).val

/-- Raw representative of the actual moving-frame sector selected by a Reader. -/
def component (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (v : (i : I) → (Climb.Bel C.book).Field (d i))
    (g : Grades d) (t : ℝ) (i : I) : C.label (levels g i) :=
  S.representative _ (R.cutTest (levels g i) (d i) (J t (d i) (v i)))

/-- Each coordinate acquires the actual sector degree, including degree zero. -/
theorem component_rate (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J) (v : (i : I) → (Climb.Bel C.book).Field (d i))
    (g : Grades d) (i : I) (k : (C.labels.level (levels g i)).Index) :
    RateLE trail LogV (fun t => component F R J v g t i k) (-(levels g i:ℝ)) := by
  let L : S.Field (levels g i) →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj k) ∘L (S.representative _).toContinuousLinearMap
  have h : RateLE trail LogV (fun t => R.cutTest (levels g i) (d i) (J t (d i) (v i))) (-(levels g i:ℝ)) := by
    simpa only [Function.comp_id, id_eq] using
      PhysMS.Frame.entrust F R J H (r:=id) tendsto_id _ _ (Nat.le_of_lt_succ (g i).isLt) (v i)
  have p := (RateLE.const ‖L‖ PhysMS.to_log_zoom).mul (RateLE.norm (X:=S.Field (levels g i)) h)
  rw [zero_add] at p
  exact p.of_norm_le (Eventually.of_forall fun t => L.le_opNorm _)

def Margin (D n m : ℕ) (h a c : ℝ) : Prop :=
  D + (1:ℝ)/32 ≤ ((D:ℝ)+1/16)*(a-h) - m*c - 4*n*(c-a) + m

private theorem lower_margin {D n m k : ℕ} {h a c : ℝ} (hc : 1 ≤ c) (hk : k ≤ m)
    (hm : Margin D n m h a c) : Margin D n k h a c := by
  have hl : (k:ℝ)*(c-1) ≤ (m:ℝ)*(c-1) :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) (sub_nonneg.mpr hc)
  dsimp [Margin] at hm ⊢
  linarith

variable [Fintype I]

/-- One prescribed grid can serve a whole finite set of capped input sectors. -/
theorem on_grid (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (D : ℕ) {h a c : ℝ} {b m j : ℝ → ℕ}
    (hb : Height C.S trail LogV b h) (hm : Height C.S trail LogV m a) (hj : Height C.S trail LogV j c)
    (hh : 0 < h) (ha : h < a) (h₁ : a < 1) (hc : 1 < c)
    (hmarg : Margin D (Fintype.card I) (∑ i, d i) h a c)
    (v : ℝ → (i : I) → C.label (d i))
    (hv : ∀ i k, RateLE trail LogV (fun t => v t i k) (-(d i:ℝ))) :
    ∃ fee : ℝ → ℝ, RateLE trail LogV fee (-(D:ℝ)-1/32) ∧
      ∀ᶠ t in trail, ∀ x : I → Cover, Plot C (b t) (m t) (j t) x → ∀ᶠ w in f.fuse,
        Observed F.room.cutoff (b t) (j t) D x (v t) w (fee t) := by
  let hT := PhysMS.to_log_zoom
  obtain ⟨W,r,μ,L,g,e,Z,hr, stages⟩ :=
    FundedIntrinsicProduct.basis (d:=d) F facility anchor hT D hb hm hj hh ha (h₁.trans hc)
  obtain ⟨b₀, _, B, hB, bank⟩ := StampedPhysicalDetector.label_bound F D 1 one_pos
  let q := -(D:ℝ)-1/32
  let s := q-D*h-((D:ℝ)+1)*h-1
  let ρ := ∑ i, -(d i:ℝ)
  let r₀ := s-ρ-1
  let bill (t : ℝ) := B * C.S.a (b t)^(-(D:ℝ)-1) + 1
  let fee (t : ℝ) := ∑ u, ‖weight (v t) u‖*e t u
  have hfee : RateLE trail LogV fee q := by
    apply (weighted_rate hT v e (fun i => -(d i:ℝ)) _ hv (fun u => (hr u).2)).mono
    dsimp [Margin] at hmarg
    dsimp [q]
    push_cast at hmarg ⊢
    rw [Finset.sum_neg_distrib]
    linarith only [hmarg]
  have hfirst := (RateLE.const B hT).mul ((hb.mesh.rpow (-(D:ℝ)-1)).pays hT)
  have hbill : RateLE trail LogV bill (((D:ℝ)+1)*h) := by
    apply RateLE.add (F:=fun t => B*C.S.a (b t)^(-(D:ℝ)-1)) (F':=fun _ => 1) _ _ hT
    · apply hfirst.mono; linarith
    · apply (RateLE.const (1:ℝ) hT).mono
      positivity
  have chartPrice := (((chart_rate hT D hb).pays hT).mul hbill).mul ((RateIs.exp s hT).pays hT)
  have hs : (D:ℝ)*h+((D:ℝ)+1)*h+s < q := by dsimp [s]; linarith
  have wallet := weighted_rate hT v (fun t _ => Real.exp (r₀*LogV t)) (fun i => -(d i:ℝ))
    r₀ hv (fun _ => (RateIs.exp r₀ hT).pays hT)
  have hs' : ρ+r₀ < s := by dsimp [r₀]; linarith
  refine ⟨fun t => fee t + Real.exp (q*LogV t),hfee.add ((RateIs.exp q hT).pays hT) hT,?_⟩
  filter_upwards [hm.grows.eventually_ge_atTop (C.ref D),stages r₀,wallet s hs',
    hb.grows.eventually_ge_atTop b₀,chartPrice q hs] with t stock funded stockCost bankLevel chartCost
  intro x hx
  filter_upwards [FundedIntrinsicReadout.combine L.toPackage F.room.cutoff stock x (v t) (g t) (e t) _
    (Z t x) (funded x hx), bank (b t) bankLevel 1 one_pos] with w current voucher
  obtain ⟨hl, useLabel⟩ := voucher
  have positive : 0 ≤ bill t :=
    add_nonneg (mul_nonneg hB (Real.rpow_nonneg (C.S.a_pos _).le _)) zero_le_one
  exact (IntrinsicPhysicalCell.canonical F facility
    (current.weaken ((le_abs_self _).trans stockCost)) hl positive (fun z => useLabel z 0)).weaken
    (add_le_add_right ((le_abs_self _).trans chartCost) _)

/-- All profiles share one hierarchy and one readout date. Distinct grades
keep their own physical labels and their own exact finite report. -/
theorem sectors (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (U : Detector S D) (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J)
    (v : (i : I) → (Climb.Bel C.book).Field (d i)) :
    ∃ b m j : ℝ → ℕ, ∃ h a c : ℝ, Height C.S trail LogV b h ∧ Height C.S trail LogV m a ∧
      Height C.S trail LogV j c ∧ 0 < h ∧ h < a ∧ a < 1 ∧ 1 < c ∧
      ∃ e : Grades d → ℝ → ℝ, (∀ g, RateLE trail LogV (e g) (-(1:ℝ)/32)) ∧
      (∀ loop : ℕ, Tendsto (fun t => C.path.levels.clock.hatBeta (j t)^loop * (∑ g, ‖e g t‖)) trail (𝓝 0)) ∧
      ∀ᶠ t in trail, ∀ x : I → Cover, Plot C (b t) (m t) (j t) x → ∀ᶠ w in f.fuse,
        ∀ g : Grades d, IntrinsicGramReadout.Decoded F.room.cutoff U J t (b t) (j t) x
          (component F R J v g t) w (e g t) := by
  obtain ⟨h,a,c,hh,ha,h₁,hc,hmarg⟩ := engineering_margin D (∑ i, d i) (Fintype.card I)
  obtain ⟨b,hb⟩ := found PhysMS.to_log_zoom C.path.levels.fits.mesh hh.le
  obtain ⟨m,hm⟩ := found PhysMS.to_log_zoom C.path.levels.fits.mesh (hh.trans ha).le
  obtain ⟨j,hj⟩ := found PhysMS.to_log_zoom C.path.levels.fits.mesh (zero_lt_one.trans hc).le
  have margin (g : Grades d) : Margin D (Fintype.card I) (∑ i, levels g i) h a c :=
    lower_margin hc.le (Finset.sum_le_sum fun i _ => Nat.le_of_lt_succ (g i).isLt) hmarg
  choose fee expense paid using fun g : Grades d =>
    on_grid F facility anchor D hb hm hj hh ha h₁ hc (margin g)
      (component F R J v g) (component_rate F R J H v g)
  choose b₀ n A hA prices using fun g : Grades d => IntrinsicGramReadout.bank (d:=levels g) F U 1 one_pos
  let K (g : Grades d) (i : Fin U.size) := ∏ k, (A g i k * C.S.a (n g i)^(-((tags S (U.listen i) k).1:ℝ)-1)+1)
  have pos (g : Grades d) (i : Fin U.size) : 0 ≤ K g i := Finset.prod_nonneg (fun k _ =>
    add_nonneg (mul_nonneg (hA g i k) (Real.rpow_nonneg (C.S.a_pos _).le _)) zero_le_one)
  let cost (g : Grades d) (t : ℝ) := columnPrice (wholeReadout U J t) (K g) * fee g t
  have horizon (g : Grades d) : RateLE trail LogV (cost g) (-(1:ℝ)/32) := by
    apply ((IntrinsicGramReadout.price_rate F U J H (K g) (pos g)).mul (expense g)).mono
    linarith
  refine ⟨b,m,j,h,a,c,hb,hm,hj,hh,ha,h₁,hc,cost,horizon,?_,?_⟩
  · intro loop
    have hs : RateLE trail LogV (fun t => ∑ g, ‖cost g t‖) (-((0:ℕ):ℝ)-1/32) := by
      have hq : -(1:ℝ)/32 = -((0:ℕ):ℝ)-1/32 := by norm_num
      rw [← hq]
      exact RateLE.sum PhysMS.to_log_zoom fun g _ => (horizon g).norm
    simpa only [Nat.cast_zero,zero_mul,Real.exp_zero,one_mul] using
      all_loop_orders PhysMS.to_log_zoom 0 _ hs hj loop
  · filter_upwards [eventually_all.mpr paid,hb.grows.eventually_ge_atTop (Finset.univ.sup b₀)] with t funded large
    intro x hx
    filter_upwards [eventually_all.mpr (fun g => funded g x hx),eventually_all.mpr prices,
      (Cards.largeMesh f).eventually_ge_atTop (j t)] with w every bank hw
    intro g
    exact bank g (b t) (j t) ((Finset.le_sup (s:=Finset.univ) (f:=b₀) (Finset.mem_univ g)).trans large) hw x (component F R J v g t) _ (every g) J t

end YM.Integration.FilteredIntrinsicGramReadout
