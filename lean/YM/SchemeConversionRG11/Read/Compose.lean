import YM.SchemeConversionRG11.Read.Reset

/-!
# Formal comparison via a common regulator and finite retuning

These are adapter theorems. Convergence of the retuned *regulator diagrams* to an
independently prescribed output is a substantial remaining input. The component proves
how to **eliminate** the regulator retunings (including divergent coefficients) from that
comparison. The external hard and IR comparisons, the WilsonX diagram-prescription
constructions, and identifying the actual estimates are not included here.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Bridge
open Function Filter Maxwell Issue Series Tape Detector Pert.Position Horizon Affine Orbit Coupling
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {F : Labels.Frames G} {n d : ℕ} {α : Type*} {l : Filter α}

-- API for convergence using only the necessary orders/arity per theorem
lemma smaller {B : α → Issue F d} {X : Issue F d} (h : Limits n l B X) {p : ℕ} (hp : p ≤ n) :
    Limits p l B X := fun m t ↦ (h m t).mono (E:=Tape F d m ℂ) hp
lemma higher {B : α → Issue F d} {A : Issue F d} (h : Limits n l B A)
    {V : Series (Buffer F d)} {w : α → Series (Buffer F d)} (hw : Converges n l w V) :
    Limits n l (fun i ↦ imprint (w i) (B i)) (imprint V A) := by
  intro m s; exact (hw.both (h m s)).lift Tape.placing.contDiffAt
lemma exchanged {z : α → Series ℝ} {x : Series ℝ} {B : α → Issue F d} {A : Issue F d}
    (hz : Converges n l z x) (h : Limits n l B A) :
    Limits n l (fun i ↦ insertSeries (z i) (B i)) (insertSeries x A) :=
  fun m s ↦ (h m s).subJet hz

section turn
variable {B L : α → Issue F 6} {z : α → Series ℝ}
  {X : α → Series (Buffer F 6)}
  {P : Poll F 6} {M : Issue F 6}

lemma free_entry (ht : Limits n l L M) (hM : Twist M) :
    Tendsto (fun i ↦ P.getTest (L i) 0) l (𝓝 P.blank) := by
  convert! P.converges_test ht 0 (Nat.zero_le _) using 2
  exact (funext fun i ↦ hM (P.table i).r _).symm

/-- Compute external normalization using minimal input: convergence through order ONE on the
 retuned arrays and nonsingularity *from the bare side*. No positive-order convergence of bare
 correlation arrays used (only zeroth in the poll and the diagnostic assumption on the framed
 scalar). Inputs do not involve actual readout/sharp Gram bounds. -/
theorem fixing [l.NeBot]
    (hz : ∀ᶠ a in l, z a 0 = 0) (hc : Tendsto (fun a ↦ X a 0) l (𝓝 0))
    (hEq : ∀ᶠ a in l, Identifies 1 (L a) (tune (B a) (z a) (X a)))
    (hL : Twist M) (hl : Limits 1 l L M)
    (hb : Tendsto (fun a ↦ P.getTest (B a) 0) l (𝓝 P.blank))
    (s t : ℝ) (hs : Tendsto (fun a ↦ scaleMeter P (B a) 1) l (𝓝 s))
    (hv : Tendsto (fun a ↦ z a 1) l (𝓝 t)) : scaleMeter P M 1 = s * t := by
  have hn := eventual_normal_through hz hc hEq hb (free_entry hl hL)
  have he := higher hl (P.convergence hL hl)
  have h := powering he 1 le_rfl
  refine tendsto_nhds_unique h ((hs.mul hv).congr' ?_)
  filter_upwards [hz, hn] with a ha hN
  have hM := meter_through hN 1 le_rfl
  rw [meter_sub _ ha, subJet_tangent _ _ ha] at hM
  exact hM.symm

/-- Conversely calibrate from the external diagnosis. Obtain bare tangent in the limit;
  no connection to the historical effective-coupling estimates is assumed. -/
theorem setting (hz : ∀ᶠ a in l, z a 0 = 0) (hc : Tendsto (fun a ↦ X a 0) l (𝓝 0))
    (hEq : ∀ᶠ a in l, Identifies 1 (L a) (tune (B a) (z a) (X a)))
    (hL : Twist M) (hl : Limits 1 l L M)
    (hb : Tendsto (fun a ↦ P.getTest (B a) 0) l (𝓝 P.blank))
    {t : ℝ} (ht : t ≠ 0) (hv : Tendsto (fun a ↦ z a 1) l (𝓝 t)) :
    Tendsto (fun a ↦ scaleMeter P (B a) 1) l (𝓝 (scaleMeter P M 1 / t)) := by
  have hn := eventual_normal_through hz hc hEq hb (free_entry hl hL)
  have he := higher hl (P.convergence hL hl)
  refine ((powering he 1 le_rfl).div hv ht).congr' ?_
  filter_upwards [hz, hn, hv.eventually (isOpen_ne.mem_nhds ht)] with a ha hN hb
  have hM := meter_through hN 1 le_rfl
  rw [meter_sub _ ha, subJet_tangent _ _ ha] at hM
  exact (congrArg (· / z a 1) hM).trans (mul_div_cancel_right₀ _ hb)
end turn

lemma coupling_inverse {u v w : Series ℝ} {p : ℕ} (hp : 1 ≤ p)
    (hu : Good u) (hw : w 0 = 0) (hv : Through p (subJet v w) u) :
    Through p (subJet w (reversion u)) (reversion v) := by
  have h0 : v 0 = 0 := (subJet_base hw).symm.trans (hv.zero.trans hu.1)
  have heq : v 1 * w 1 ≠ 0 := (subJet_tangent v w hw).symm.trans_ne ((hv 1 hp).trans_ne hu.2)
  have hk : Good v := ⟨h0,left_ne_zero_of_mul heq⟩
  apply Through.symm
  apply (hk.reversion_inverts p).unique ((subJet_base hu.rev.1).trans hw)
  rw [subJet_assoc hw hu.rev.1]
  exact (hv.subst_jet Through.rfl hu.rev.1).trans (hu.reversion_inverts p).forward

section Common
-- Coupling conversions here at common subtraction length of both. Independence of the
-- resulting coefficients from the comparison regulator follows given the stated limits.
variable {P : Poll F 6}
  {B L : (i : ℕ) → α → Issue F i} {z : α → Series ℝ} {Z : (i : ℕ) → α → Series (Buffer F i)}
  {M : (i : ℕ) → Issue F i}

/-- The finite X prescription step used here. No assertion that it's a legal inverse unless
 accompanied by `Good`. -/
def inputReset (p : Poll F 6) (V : Issue F 6) (q : Poll F d) (A : Issue F d) :=
    insertSeries (reversion (scaleMeter p V)) (positions q A)

lemma converge_moved {L : α → Issue F 6} {M : Issue F 6} (hn : 1 ≤ n)
    (hl : Limits n l L M) (hM : Twist M) (hm : Good (scaleMeter P M)) :
    (∀ᶠ i in l, Good (scaleMeter P (L i))) ∧
      Converges n l (fun i ↦ reversion (scaleMeter P (L i))) (reversion (scaleMeter P M)) := by
  have ht : Converges n l (fun i ↦ scaleMeter P (L i)) (scaleMeter P M) := powering (higher hl (P.convergence hM hl))
  have he : ∀ᶠ i in l, Good (scaleMeter P (L i)) :=
    ((ht 1 hn).eventually (isOpen_ne.mem_nhds hm.2)).mono fun _ h ↦ ⟨meter_at_zero _, h⟩
  exact ⟨he,tends_rev hn hm he ht⟩

theorem same_base [l.NeBot] (hn : 1 ≤ n)
    (hz : ∀ᶠ a in l, z a 0 = 0)
    (hm6 : Tendsto (fun a ↦ P.getTest (B 6 a) 0) l (𝓝 P.blank))
    (hZ : Tendsto (fun a ↦ Z 6 a 0) l (𝓝 0))
    (hM6 : Twist (M 6)) (hl6 : Limits n l (L 6) (M 6))
    (hL6 : ∀ᶠ i in l, Identifies n (L 6 i) (tune (B 6 i) (z i) (Z 6 i)))
    (hv : Good (scaleMeter P (M 6)))
    -- can now compare at any fixed horizon with matching to same regulator, even below 6
    (q : Poll F d)
    (hm : Tendsto (fun a ↦ q.getTest (B d a) 0) l (𝓝 q.blank))
    (hj : Tendsto (fun a ↦ Z d a 0) l (𝓝 0))
    (hM : Twist (M d)) (hl : Limits n l (L d) (M d))
    (hEq : ∀ᶠ i in l, Identifies n (L d i) (tune (B d i) (z i) (Z d i))) :
    (∀ᶠ i in l, Good (scaleMeter P (B 6 i))) ∧ Limits n l (fun i ↦ inputReset P (B 6 i) q (B d i))
      (inputReset P (M 6) q (M d)) := by
  have ha : Tendsto (fun a ↦ q.getTest (L d a) 0) l (𝓝 q.blank) := by
    convert! q.converges_test hl 0 (Nat.zero_le _) using 2
    exact (funext fun i ↦ hM (q.table i).r _).symm
  have hx := eventual_normal_through hz hZ hL6 hm6 (free_entry hl6 hM6)
  have hd := eventual_normal_through hz hj hEq hm ha
  obtain ⟨ho,hk⟩ := converge_moved hn hl6 hM6 hv
  have hC : ∀ᶠ a in l, Through n (scaleMeter P (L 6 a)) (subJet (scaleMeter P (B 6 a)) (z a)) := by
    filter_upwards [hz,hx] with a hu hw
    exact meter_sub _ hu ▸ meter_through hw
  have hw : ∀ᶠ a in l, Good (scaleMeter P (B 6 a)) := by
    filter_upwards [ho,hC,hz] with a he e' ho
    refine ⟨meter_at_zero _, left_ne_zero_of_mul (show _ * (z a 1) ≠ 0 from ?_)⟩
    have H := e' 1 hn
    rw [subJet_tangent _ _ ho] at H; exact H.symm.trans_ne he.2
  refine ⟨hw,?_⟩
  have hu := exchanged hk (higher hl (q.convergence hM hl))
  intro m t
  refine Converges.through (E:=Tape F d m ℂ) (hu m t) ?_
  filter_upwards [hz, ho,hC,hd] with i hi hg hi' hP
  have HE := coupling_inverse hn hg hi hi'.symm
  let g := scaleMeter P (L 6 i)
  let X := positions q (B d i) m t
  have hp : Through n _ (subJet X (reversion (scaleMeter P (B 6 i)))) := Through.rfl.subst_jet HE
    ((subJet_base (x:=reversion g) (a:=z i) hg.rev.1).trans hi)
  rw [subJet_assoc hi hg.rev.1] at hp
  exact ((hP m t).subst_jet Through.rfl hg.rev.1).trans hp

/-- On both prescriptions' stated convergence data, one conversion (from the external arrays
  only), not the regulator-dependent column matrices. Still assumes the difficult `hl` limits. -/
theorem compare_published [l.NeBot] (hn : 1 ≤ n) {q : (i : ℕ) → Poll F i}
    (hz : ∀ᶠ a in l, z a 0 = 0) (hd : 6 ≤ d)
    (hV : ∀ i ≤ d, Tendsto (fun a ↦ (q i).getTest (B i a) 0) l (𝓝 (q i).blank))
    (hZ : ∀ i ≤ d, Tendsto (fun a ↦ Z i a 0) l (𝓝 0))
    (hM : ∀ i ≤ d, Twist (M i)) (hl : ∀ i ≤ d, Limits n l (L i) (M i))
    (hEq : ∀ i ≤ d, ∀ᶠ a in l, Identifies n (L i a) (tune (B i a) (z a) (Z i a)))
    -- e.g. obtain from minimal-order diagnosis lemmata
    (hPos : 0 < scaleMeter (q 6) (M 6) 1) (hQ : Poll.FamilyMenu q) (hN : Poll.Crossing M n d)
    -- WilsonX input independent limit at unadjusted position frame
    {X : (i : ℕ) → Issue F i} (hX : ∀ i ≤ d, Limits n l (fun a ↦ inputReset (q 6) (B 6 a) (q i) (B i a)) (X i)) :
    let t := scaleMeter (q 6) (M 6)
    let g := reversion t
    let P (i : ℕ) := subJet ((q i).press (M i)) g
    Good t ∧ Inverts n t g ∧ 0 < g 1 ∧
      Guided n P d ∧ (∀ i ≤ d, P i 0 = 0) ∧
      ∀ i ≤ d, Identifies n (X i) (imprint (P i) (insertSeries g (M i))) := by
  intro t g P
  have ht : Good t := ⟨meter_at_zero _,hPos.ne'⟩
  have hg : g 0=0 := ht.rev.1
  refine ⟨ht,ht.reversion_inverts n,ht.orientation hPos, coupling_guides hg (Poll.across hQ hM hN), fun i hi ↦
    (subJet_base hg).trans ((q i).starts_zero (hM i hi)),?_⟩
  intro i hi
  have H := same_base hn hz (hV _ hd) (hZ _ hd) (hM _ hd) (hl _ hd) (hEq _ hd) ht (q i)
    (hV _ hi) (hZ _ hi) (hM _ hi) (hl _ hi) (hEq _ hi)
  have he : imprint (P i) (insertSeries g (M i)) = inputReset (q 6) (M 6) (q i) (M i) :=
    (survives (M i) ((q i).press (M i)) hg).symm
  rw [he]
  exact fun m t ↦ Converges.unique (E:=Tape F i m ℂ) (hX i hi m t) (H.2 m t)
end Common

end YM.SchemeConversionRG11.Bridge
