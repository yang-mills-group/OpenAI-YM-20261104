import YM.Integration.WilsonCapturedPrimaryReporter

/-! Positive-horizon finite recovery before taking either regulator limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryOnRun
open Function Filter Finset Set Labels Lattice Wilson RG Source Push.Local
open Next.Foundations ProjectorNext.Equivariance Trace.Physical.Germ
open PhysicalNext.Repeat.Legato Pert.Asymptotics Stationary Comparison.RG02
open WilsonCapturedPrimaryAngles WilsonCapturedPrimaryAperture WilsonCapturedPrimaryPotential
open WilsonCapturedPrimaryPaid WilsonCapturedPrimaryCollar WilsonCapturedPrimaryEstimate
open WilsonCapturedPrimaryReading WilsonFirstReceivedRadialStencil
open scoped Classical Topology
variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d}

private def reach (B : SectionData F) :=
  B.stencil.sup fun x => univ.sup fun a : Axis => (x a).natAbs

private theorem footprint (B : SectionData F) {n : Side} (o : Site n) (x : Site n)
    (hx : x∈B.footprint o) : separation x o ≤ reach B := by
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
  rw [separation,add_sub_cancel_right,pdist]
  apply Finset.sup_le
  intro k hk
  exact ((Lattice.Corona.lap a k).trans (Finset.le_sup (f:=fun j:Axis => (a j).natAbs) hk)).trans
    (Finset.le_sup (f:=fun x : Cover => univ.sup fun j : Axis => (x j).natAbs) ha)

private theorem enrolled (R : Run G) (simple : G.Simple) (B : SectionData F) :
    ∀ᶠ i : ℕ in atTop, ∀ (K : ℕ) (n : Side) (o : Site n), ∀ x∈B.footprint o,
      separation x o ≤ radius (R.family.path.levels.budget i) K := by
  have grows := Real.tendsto_log_atTop.comp (RG01.Physical.hats simple R.family.path.levels)
  filter_upwards [grows.eventually_ge_atTop ((reach B:ℝ)+1)] with i hi
  let β := R.family.path.levels.clock.hatBeta i
  have hs : (reach B:ℝ)+1 ≤ Real.log β := hi
  have non : 0≤(reach B:ℝ) := Nat.cast_nonneg _
  have lim : (reach B:ℝ) ≤ (R.family.path.levels.budget i).B := by
    apply le_trans _ (Nat.le_ceil ((Real.log β)^2))
    nlinarith only [hs,non,sq_nonneg (Real.log β-1)]
  have cap : reach B ≤ (R.family.path.levels.budget i).B := by exact_mod_cast lim
  intro K n o x hx
  exact (footprint B o x hx).trans (cap.trans (by unfold radius;omega))

/-- On the same funded reporting run the spacing and field horizon are
chosen before N and the period. The source invoice is asked only at the
actual stationary potential of each physical field. -/
theorem readouts (R : Run G) (simple : G.Simple) (F : Labels.Frame G d)
    (A : Hol G) (B : SectionData F) (P u : ℕ) (cap : ℝ) (capOne : 1≤cap) :
    let v := u+1
    let Q := grade P d v
    ∀ᶠ i : ℕ in atTop, ∀ (N per : ℕ), i+1≤N →
      let b := R.family.path.levels.budget i
      let g := regulatorRun R.family N per (i+1)
      let K := cutoff b g (Q+u)
      let r := radius b K
      let t := g^gap P v
      let n := R.family.side i per
      1≤b.supportExponent → d+1≤b.order →
      ∀ (Ψ : Rep G n), Ψ.p=b → ∀ (o : Site n) (q : Coefficient F n) (w κ s C : ℝ),
      Readable A B Ψ.p n w → q.Format o A Ψ → q.remBound o Ψ κ s → 0≤C →
      w*F.coeffSize (F.core q.x)+s ≤ C/g^u →
      ∀ (D : ℕ), d≤D → ∀ (y : Probe G d → Polynomial ℂ),
      (∀ p∈tests F, (y p).natDegree≤D) →
      (∀ p∈tests F, ∀ j≤D,
        let z := t*node D j
        let V := lifted A b o r p g z
        let angle := Stationary.arm G n 1 V
        |bound G b g cap| ≤ (b.B:ℝ)^2*b.threshold/g →
        (∀ e, ‖Exterior.collect G angle e‖ ≤ cap*|bound G b g cap|) →
        flags Ψ.p.threshold (Integral.sample g angle)=∅ →
        ‖reading B Ψ o q (Integral.sample g angle)-(y p).eval (z:ℂ)‖ ≤ C*g^Q) →
      ∀ p∈tests F, ‖runProbe F p (projection F A Ψ.p.threshold o q)-p.2.val.factorial*(y p).coeff p.2.val‖ ≤
        WilsonCapturedPrimaryOriginal.fieldFee A p D*C*g^P := by
  intro v Q
  filter_upwards [WilsonCapturedPrimaryReporter.panel R simple F A (Q+u) P v (by dsimp [v];omega),
    WilsonCapturedPrimaryCourse.original R simple (Q+u) 0 (C:=0) (ε:=1) le_rfl zero_lt_one,
    enrolled R simple B] with i panel base footprint
  intro N per hi b g K r t n support extra Ψ actual o q w κ s C read form paid cc invoice D rk y deg values
  have b0 := base N per hi support
  have gp : 0<g := b0.1
  have g1 : g≤1 := b0.2.1.trans (by norm_num)
  have w0 : 0≤w*F.coeffSize (F.core q.x) := mul_nonneg read.nonneg (by unfold Labels.Frame.coeffSize;positivity)
  have rent : s≤C/g^u := (le_add_of_nonneg_left w0).trans invoice
  have ss : 0 ≤ s := by
    obtain ⟨a,b,ha,hb,fee,_⟩ := paid
    exact (add_nonneg ha hb).trans fee
  have gross0 : 0≤w*F.coeffSize (F.core q.x)+s := add_nonneg w0 ss
  have prices p hp := panel p hp N per hi support
  have fit : 2*t≤1 := by
    have mono : t≤g := pow_le_of_le_one gp.le g1 (by
      unfold gap;omega)
    linarith only [mono,b0.2.1]
  intro p hp
  apply WilsonCapturedPrimaryOriginal.original read form paid (actual ▸ extra) gp g1 cc P v u rent p (y p)
    D (deg p hp) ((Nat.le_of_lt_succ p.2.isLt).trans rk)
  · rw [actual];exact footprint K n o
  · rw [actual];exact b0.2.2.2.1
  · exact fit
  · rw [actual];exact (prices p hp).2.2.2.2.1
  · rw [actual]
    calc
      _ ≤ g⁻¹*(C/g^u) := mul_le_mul ((prices p hp).2.2.2.2.2) invoice gross0 (inv_nonneg.mpr gp.le)
      _ = C/g^v := by dsimp only [v];rw [pow_succ];ring
  · rw [actual];intro j hj
    let z := t*node D j
    have t0 : 0<t := pow_pos gp _
    have z0 : 0≤z := mul_nonneg t0.le (node_mem hj).1
    have z1 : z≤2*t := (mul_le_of_le_one_right t0.le (node_mem hj).2).trans (by linarith only [t0])
    have a := resolved A b o r p gp (zero_lt_one.trans_le capOne) (t:=z)
      (by rw [abs_of_nonneg z0];exact z1.trans fit) b0.2.2.2.1
      (by rw [abs_of_nonneg z0];exact (mul_le_mul_of_nonneg_right z1
        (zero_le_one.trans (wallet_one A p r))).trans (prices p hp).2.2.2.2.1)
    obtain ⟨same,clear,bounded⟩ := a
    have ans := values p hp j hj (window G b gp capOne) bounded (actual ▸ clear)
    rw [same] at ans;exact ans


/-- Return a filed vector in the original finite field frame. -/
theorem original (R : Run G) (simple : G.Simple) (F : Labels.Frame G d)
    (A : Hol G) (B : SectionData F) (P u : ℕ) (cap : ℝ) (capOne : 1≤cap) :
    let v := u+1
    let Q := grade P d v
    ∀ᶠ i : ℕ in atTop, ∀ (N per : ℕ), i+1≤N →
      let b := R.family.path.levels.budget i
      let g := regulatorRun R.family N per (i+1)
      let K := cutoff b g (Q+u)
      let r := radius b K
      let t := g^gap P v
      let n := R.family.side i per
      1≤b.supportExponent → d+1≤b.order →
      ∀ (Ψ : Rep G n), Ψ.p=b → ∀ (o : Site n) (q : Coefficient F n) (w κ s C : ℝ),
      Readable A B Ψ.p n w → q.Format o A Ψ → q.remBound o Ψ κ s → 0≤C →
      w*F.coeffSize (F.core q.x)+s ≤ C/g^u →
      ∀ (b' : F.Coeff) (D : ℕ), d≤D → ∀ (y : Probe G d → Polynomial ℂ),
      (∀ p∈tests F, (y p).natDegree≤D ∧ runProbe F p b'=p.2.val.factorial*(y p).coeff p.2.val) →
      (∀ p∈tests F, ∀ j≤D,
        let z := t*node D j
        let V := lifted A b o r p g z
        let angle := Stationary.arm G n 1 V
        |bound G b g cap| ≤ (b.B:ℝ)^2*b.threshold/g →
        (∀ e, ‖Exterior.collect G angle e‖ ≤ cap*|bound G b g cap|) →
        flags Ψ.p.threshold (Integral.sample g angle)=∅ →
        ‖reading B Ψ o q (Integral.sample g angle)-(y p).eval (z:ℂ)‖ ≤ C*g^Q) →
      F.coeffSize (projection F A Ψ.p.threshold o q-b') ≤ WilsonCapturedPrimaryPanel.invoice F A D*C*g^P := by
  intro v Q
  filter_upwards [readouts R simple F A B P u cap capOne] with i h
  intro N per hi b g K r t n support extra Ψ actual o q w κ s C read form paid cc rent b' D rk y filed values
  have values' := h N per hi support extra Ψ actual o q w κ s C read form paid cc rent D rk y
    (fun p hp => (filed p hp).1) values
  have answer := WilsonCapturedPrimaryEstimate.returned (A:=A) (R:=Ψ) (o:=o) q b'
    (fun p => WilsonCapturedPrimaryOriginal.fieldFee A p D*C*g^P)
    (fun p hp => (norm_nonneg _).trans (values' p hp))
    (fun p hp => by rw [(filed p hp).2]; exact values' p hp)
  exact answer.trans_eq (by unfold WilsonCapturedPrimaryPanel.invoice;rw [←sum_mul,←sum_mul];ring)

end YM.Integration.WilsonCapturedPrimaryOnRun
