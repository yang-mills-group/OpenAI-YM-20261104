import YangMills.WilsonProof.NativeSupport.ThermalJets

/-! Two Gaussian integrations by parts for a full quadratic temperature
insertion. The connected recursion never takes a trace bound. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ThermalShortcuts.ConnectedWick
open MeasureTheory Filter Function
open scoped Topology ContDiff BigOperators Classical
open PertExtension PertExtension.Series PertExtension.GaussianScore
open ThermalJets

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E] [DecidableEq I]
local notation "V" => Module.Dual ℝ E
local notation "Z" => Radial.zone (E:=E)
variable (Γ : Law E) (μ : Measure E) [μ.HasTemperateGrowth] [μ.IsAddRightInvariant]

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.HasTemperateGrowth] [μ.IsAddRightInvariant] in
private theorem avg_add {A B : E→ℝ} (a : Integrable (A * Γ.kern) μ) (b : Integrable (B * Γ.kern) μ) :
    Γ.average μ (A+B)=Γ.average μ A+Γ.average μ B := by
  unfold Law.average; rw [add_mul]; simp only [Pi.add_apply]; rw [integral_add a b,add_div]

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.HasTemperateGrowth] [μ.IsAddRightInvariant] in
omit [DecidableEq I] in
private theorem avg_sum (s : Finset I) (F : I → E → ℝ) (hf : ∀ i∈s, Integrable (F i*Γ.kern) μ) :
    Γ.average μ (∑ i∈s,F i) = ∑ i∈s,Γ.average μ (F i) := by
  unfold Law.average
  rw [Finset.sum_mul]; simp only [Finset.sum_apply]; rw [MeasureTheory.integral_finsetSum _ hf,Finset.sum_div]

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.HasTemperateGrowth] [μ.IsAddRightInvariant] in
private theorem avg_scale (F : E→ℝ) (b : ℝ) :
    Γ.average μ (fun x=>F x*b) = Γ.average μ F*b := by
  unfold Law.average
  have p : (fun x=>F x*b)*Γ.kern = fun x=>(F*Γ.kern) x*b := by ext x; dsimp; ring
  rw [p,MeasureTheory.integral_mul_const]; ring

private theorem parts {A L : E→ℝ} (v : E) (a : Zone.Invoice Z A) (ac : Continuous A)
    (l : Zone.Invoice Z L) (lc : Continuous L)
    (hd : ∀ x t, HasDerivAt (fun r : ℝ => A (x+r•v)) (L (x+t•v)) t) :
    Γ.average μ (fun x=>A x*Γ.P v x)=Γ.average μ L := by
  have h := Γ.translation_lemma v a ac l lc hd μ
  have ia := Γ.integrable_entry μ (a.mul (Law.linearInvoice (Γ.P v))) (ac.mul (Γ.P v).continuous_of_finiteDimensional)
  have il := Γ.integrable_entry μ l lc
  rw [sub_mul] at h
  simp only [Pi.sub_apply] at h
  rw [integral_sub il ia,sub_eq_zero] at h
  exact congrArg (· / ∫ x,Γ.kern x ∂μ) h.symm

def quadratic (D : E →ₗ[ℝ] V) (x : E) := D x x / 2

omit [FiniteDimensional ℝ E] [BorelSpace E] [MeasurableSpace E] in
private theorem along (D : E →ₗ[ℝ] V) (sym : ∀ x y,D x y=D y x) (x v : E) (t : ℝ) :
    HasDerivAt (fun r : ℝ => quadratic D (x+r•v)) (D v (x+t•v)) t := by
  have pol : (fun r : ℝ => quadratic D (x+r•v)) =
      fun r=>quadratic D x + D v x*r + quadratic D v*(r*r) := by
    ext r; unfold quadratic
    simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,sym x v]; ring
  rw [pol]
  convert! ((hasDerivAt_const t (quadratic D x)).add ((hasDerivAt_id' t).const_mul (D v x))).add
    (((hasDerivAt_id' t).mul (hasDerivAt_id' t)).const_mul (quadratic D v)) using 1
  simp [quadratic]; ring

def connected (D : E →ₗ[ℝ] V) (F : E→ℝ) :=
  Γ.average μ (F * quadratic D) - Γ.average μ F * Γ.average μ (quadratic D)

omit [BorelSpace E] [MeasurableSpace E] in
private theorem wick_swap (a b : V) : Γ.wick a b = Γ.wick b a := by
  have eq := Γ.turns (Γ.inverse b) (Γ.inverse a)
  simpa only [Γ.applies,Law.wick] using eq

/-- Remove one marked leg. If it hits the quadratic vertex, its second leg
must also hit a mark. The vacuum contraction cancels in the normalized quotient. -/
theorem recursion (D : E →ₗ[ℝ] V) (sym : ∀ x y,D x y=D y x)
    (hQ : Zone.Invoice Z (quadratic D)) (hQc : Continuous (quadratic D))
    (a : V) (ℓ : I → V) (s : Finset I) :
    connected Γ μ D (fun x=>Law.product ℓ s x*a x) =
    ∑ i∈s, (connected Γ μ D (Law.product ℓ (s.erase i))*Γ.wick a (ℓ i) +
      Γ.average μ (Law.product ℓ (s.erase i))*D (Γ.inverse a) (Γ.inverse (ℓ i))) := by
  let v := Γ.inverse a
  let F := Law.product ℓ s
  let Q := quadratic D
  let A := F*Q
  let K (i : I) := (Law.product ℓ (s.erase i))*Q
  let K' (i : I) := fun x=>K i x * ℓ i v
  let J := F*(fun x=>D v x)
  have hi (i : I) : Integrable (K i*Γ.kern) μ :=
    Γ.integrable_entry μ ((Law.product_bound ℓ _).mul hQ) ((Law.product_cont ..).mul hQc)
  have hi' (i : I) : Integrable (K' i*Γ.kern) μ := by
    have e : K' i*Γ.kern = fun x=>(K i*Γ.kern) x *ℓ i v := by ext; dsimp [K']; ring
    rw [e]; exact (hi i).mul_const _
  have Jb : Zone.Invoice Z J := (Law.product_bound ℓ s).mul (Law.linearInvoice (D v))
  have Jc : Continuous J := (Law.product_cont ..).mul (D v).continuous_of_finiteDimensional
  let L := Law.diffSum ℓ s v*Q+J
  have Lsum : L = (∑ i∈s,K' i)+J := by
    ext x; simp only [L, Law.diffSum,Pi.add_apply,Pi.mul_apply,Finset.sum_apply,Finset.sum_mul]
    apply congrArg (· + J x)
    apply Finset.sum_congr rfl; intro i _; dsimp [K',K]; ring
  have ib := parts Γ μ (A:=A) (L:=L) v ((Law.product_bound ℓ s).mul hQ) ((Law.product_cont ..).mul hQc)
    (((Law.diffSum_bound ..).mul hQ).add Jb) (((Law.diffSum_cont ..).mul hQc).add Jc) (fun x r=>by
      exact (Law.diffSum_on ℓ s v x r).mul (along D sym x v r))
  have flat : (fun x => A x*(Γ.P v) x) = (fun x=>F x*a x)*Q := by
    ext x; dsimp [A,v]; rw [Γ.applies]; ring
  rw [flat,Lsum,avg_add Γ μ] at ib
  · rw [avg_sum Γ μ s K' (fun i _=>hi' i)] at ib
    have pk (i) : Γ.average μ (K' i) = Γ.average μ (K i) * Γ.wick a (ℓ i) :=
      avg_scale Γ μ (K i) _
    have pj : Γ.average μ J = ∑ i∈s, Γ.average μ (Law.product ℓ (s.erase i))*D v (Γ.inverse (ℓ i)) := by
      have h := Γ.recursion μ (D v) ℓ s
      apply h.trans
      apply Finset.sum_congr rfl; intro i _
      rw [wick_swap Γ (D v) (ℓ i)]; rfl
    simp_rw [pk] at ib
    rw [pj] at ib
    change Γ.average μ ((fun x=>F x*a x)*Q) - Γ.average μ (fun x=>Law.product ℓ s x*a x)*Γ.average μ Q=_
    rw [ib,Γ.recursion μ a ℓ s,Finset.sum_mul,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _; unfold connected; dsimp only [K,Q,v]; ring
  · rw [Finset.sum_mul]; simpa only [← Finset.sum_apply] using integrable_finsetSum s (fun i _=>hi' i)
  · exact Γ.integrable_entry μ Jb Jc

/-- Number of pairings and of pairings with one distinguished occupied pair. -/
def pairings : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | j+2 => (j+1)*pairings j

def markedPairings : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | j+2 => (j+1)*(markedPairings j+pairings j)

private theorem pairs_succ (j : ℕ) : pairings (j+1) = j * pairings (j-1) := by
  cases j <;> rfl

private theorem marked_succ (j : ℕ) : markedPairings (j+1) =
    j * (markedPairings (j-1)+pairings (j-1)) := by
  cases j <;> rfl

/-- Bounds with the count of Wick pairings and the count of choices of a
distinguished contracted pair. These counts vanish at odd degree. -/
theorem bounds [NeZero μ] (D : E →ₗ[ℝ] V) (sym : ∀ x y,D x y=D y x)
    (hQ : Zone.Invoice Z (quadratic D)) (hQc : Continuous (quadratic D))
    {M : ℝ} (hM : 0 ≤ M) (dom : ∀ x, |D x x| ≤ M * Γ.P x x)
    (ℓ : I → V) (s : Finset I) (legs : ∀ i∈s, UnitLeg Γ (ℓ i)) :
    |Γ.average μ (Law.product ℓ s)| ≤ (pairings s.card : ℝ) ∧
    |connected Γ μ D (Law.product ℓ s)| ≤ M * (markedPairings s.card : ℝ) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases nonempty : s.Nonempty
    · obtain ⟨a,ha⟩ := nonempty
      let p := s.erase a
      have hps : p ⊂ s := Finset.erase_ssubset ha
      have smaller (i : I) (hi : i∈p) := ih (p.erase i)
        (lt_of_le_of_lt (Finset.erase_subset i p) hps)
        (fun j hj => legs j (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hj)))
      have mark (i : I) (hi : i∈p) := legs i (Finset.mem_of_mem_erase hi)
      have pr : Law.product ℓ s = fun x => Law.product ℓ p x * ℓ a x := by
        funext x; exact (Finset.prod_erase_mul s (fun i=>ℓ i x) ha).symm
      have counts : s.card = p.card+1 := (Finset.card_erase_add_one ha).symm
      rw [pr,Γ.recursion μ (ℓ a) ℓ p,recursion Γ μ D sym hQ hQc (ℓ a) ℓ p,counts,
        pairs_succ,marked_succ,Nat.cast_mul,Nat.cast_mul,Nat.cast_add]
      constructor
      · refine (Finset.abs_sum_le_sum_abs ..).trans ?_
        calc
          _ ≤ ∑ _i∈p,(pairings (p.card-1):ℝ) := by
            apply Finset.sum_le_sum; intro i hi
            rw [abs_mul]
            have hp := (smaller i hi).1
            rw [Finset.card_erase_of_mem hi] at hp
            exact (mul_le_mul hp (wick_le_one Γ (legs a ha) (mark i hi)) (abs_nonneg _) (Nat.cast_nonneg _)).trans_eq (mul_one _)
          _ = _ := by simp
      · refine (Finset.abs_sum_le_sum_abs ..).trans ?_
        calc
          _ ≤ ∑ _i∈p,(M * markedPairings (p.card-1)+pairings (p.card-1)*M) := by
            apply Finset.sum_le_sum; intro i hi
            apply (abs_add_le ..).trans
            rw [abs_mul,abs_mul]
            obtain ⟨hp,hc⟩ := smaller i hi
            rw [Finset.card_erase_of_mem hi] at hp hc
            apply add_le_add
            · exact (mul_le_mul hc (wick_le_one Γ (legs a ha) (mark i hi)) (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
            exact mul_le_mul hp (sandwich Γ hM sym dom (legs a ha) (mark i hi)) (abs_nonneg _) (Nat.cast_nonneg _)
          _ = _ := by simp; ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp nonempty]
      have emp : Law.product ℓ ∅=1 := by funext x; simp [Law.product]
      rw [emp,connected,one_mul,Γ.empty μ,one_mul,sub_self]
      simp [pairings,markedPairings]

section Physical
open Lattice RGComparison.Core16 Descent
variable {G : Gauge} {n c : Side} {d : Descent n c}

theorem physical (room : d.Room G) (t : d.Tags) {v : ℕ → ℝ} {M : ℝ}
    (hb : d.Band M v) (faces : I→Face (Per n)) (colors : I→G.ColorIndex) (s : Finset I) :
    let Γ := ambient t room
    let μ := Chart.tangent G d.Links
    let ℓ := fun i=>leg G d (faces i) (colors i)
    |connected Γ μ (signedForm G d t v) (Law.product ℓ s)| ≤ M * (markedPairings s.card : ℝ) := by
  have price : quadratic (signedForm G d t v) = Radial.jet (charged G d t v) 2 :=
    funext fun x=>(signed_half t v x).symm
  exact (bounds (ambient t room) (Chart.tangent G d.Links) (signedForm G d t v)
    (fun _ _=>(account_smooth (room_ok d room) t v).isSymmSndFDerivAt_of_omega.eq ..)
    (price ▸ Radial.jetInvoice ..) (price ▸ Radial.Smooth.continuousJet ..)
    (nonnegativeBand hb) (signed_le_precision (room_ok d room) t hb)
    (fun i=>leg G d (faces i) (colors i)) s
    (fun i _=>leg_le_precision (room_ok d room) t (faces i) (colors i))).2

end Physical

end YM.Integration.ThermalShortcuts.ConnectedWick
