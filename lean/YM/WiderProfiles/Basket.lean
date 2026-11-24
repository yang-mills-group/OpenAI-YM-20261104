import YM.WiderProfiles.Capacity
/-!
# Apply also with the formal OPE coefficient

The `FarCoefficients` prescription *still* uses continuum coefficients after
independent regulator removal. Even if in evaluating its corresponding formal OPE
comparison one replaces both the full and the singleton kernels by finite Mesh
values of the (independent) correlation coefficients, at the same exterior shapes,
we can estimate the error from those replacements.

Thus the application supports the prediction side including uses on full and singleton coefficient rows.
NO OPE coefficient is defined as a function of the finite regulator. This is
not `G.9` or an `M.2`/`M.3` physical estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.WiderProfiles
open Function Filter Set Real Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Arrival Dframe O.Enh O.Score O.Canon
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus PowerSeries
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} {d n m : ℕ} (N : WilsonPrescription G) (h : G.Simple)
    (T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    (A : Prescription (Press.portDeck G)) (H : Main.Match N h T A true)
local notation "Y" => N.scheme
local notation "κ" => N.criterion
local notation "V" => (Scale.Measure.outlook Y κ)
local notation "ν" => Teller.logNu 1
variable (u : Scan G n) (v : Scan G m)
local notation "Drock" => (FarCoefficients V u)

def replacements (x : Points n) (w : Q G → PowerSeries ℂ) (d : ℕ) : PowerSeries ℂ :=
  ∑ i∈Finset.range (d+1), Settle i (fun q => Drock x q * w q)
def replaced (x : Points n) (s : Sample (1+m)) (d : ℕ) : PowerSeries ℂ :=
  replacements N u x (fun q => at_mesh N s (Fin.append (Single q) v)) d
def retained (x : Points n) (y : Points (1+m)) (d : ℕ) : PowerSeries ℂ :=
  replacements N u x (fun q => install V _ y (Fin.append (Single q) v)) d

include H

lemma lamp_delta (K : Set (Points n)) (hK : IsCompact K) (hx : K ⊆ conf n)
    (a k d : ℕ) (c D : ℝ) (hc : 0 < c) (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ p in Front, ∀ s : Sample (1+m), grab s=p → Admits a c D s →
    ∀ x ∈ K,
        ‖coeff k (replaced N u v x s d) - coeff k (retained N u v x (familiar s) d)‖ ≤
          C * cost p := by
  let I := Domain (1+m) a c D
  let F := along (1+m) a c D
  let X := I × ↥K
  let ℓ : Filter X := comap Prod.fst F
  let mesh (i : X) := XSpace.Cirrus.grab i.1.val
  have hp : Tendsto (fun i : X => i.1) ℓ F := tendsto_comap
  have hnn (i : X) : ‖cost (mesh i)‖ = cost (mesh i) := Real.norm_of_nonneg (Real.rpow_nonneg (mesh i).positive.le _)
  have hW (q : Q G) (j : ℕ) : Expense.Cap ℓ
      (fun i : X => coeff j (FarCoefficients V u i.2.val q)) := by
    obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn ((((H.separatedOPE ν).wilson.far u).2.1 q j).mono hx)
    exact Expense.Cap.of_bounds C (Eventually.of_forall fun i => hC _ i.2.property)
  have hR (v : Scan G (1+m)) (k : ℕ) :
      (fun i : X => coeff k (at_mesh N i.1.val v) - coeff k (install V (1+m) (familiar i.1.val) v)) =O[ℓ]
        (fun i => cost (mesh i)) := by
    obtain ⟨C,hC,hp'⟩ := absorb (at_mesh_bond N h T A H a k c D hc hD v).delta
    apply IsBigO.of_bound C
    filter_upwards [hp.eventually hp'] with i hi
    rw [hnn]; exact hi
  have hd : (fun i : X => coeff k (replaced N u v i.2.val i.1.val d) -
      coeff k (retained N u v i.2.val (familiar i.1.val) d)) =O[ℓ] fun i => cost (mesh i) := by
    simp only [replaced,retained,replacements,Settle,map_sum, coeff_mul,
      ← Finset.sum_sub_distrib, ← mul_sub]
    refine IsBigO.sum (fun i hi => IsBigO.sum (fun b _ => IsBigO.sum (fun w _ => ?_)))
    exact (IsBigO.mul (hW (own b) w.1) (hR _ w.2)).congr_right (fun i => one_mul _)
  obtain ⟨C,hC,H⟩ := hd.exists_pos
  have hh := H.bound
  simp_rw [hnn] at hh
  unfold ℓ F along at hh; rw [eventually_comap,eventually_comap] at hh
  exact ⟨C,hC,hh.mono fun p h s he ha x hx => by
    subst p; exact h ⟨s,ha⟩ rfl (⟨⟨s,ha⟩,⟨x,hx⟩⟩ : X) rfl⟩

omit H in
def meshBasket (x : Points n) (s : Sample (n+m)) (w : Sample (1+m)) (d : ℕ) :=
  at_mesh N s (Fin.append u v) - replaced N u v x w d

/-- Norm error comparing the coefficient in the independent formal Near/Far residual,
for full layouts and output-centre layouts on the same Mesh at the same `T` with that
identical exterior, arbitrary sizes up to the polynomial envelope. -/
theorem basket_delta (K : Set (Points n)) (S : Set (Points m))
    (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ O.Enh.Outside m)
    (E : ℝ) (hE : 0 < E) (a k d : ℕ) : ∃ t0 C : ℝ, 0 < C ∧
    ∀ᶠ p in Front, ∀ t ≥ t0, exp t ≤ E*(1+Schedule.theta p)^a →
      ∀ x ∈ K, ∀ y ∈ S, ∀ s : Sample (n+m), XSpace.Cirrus.grab s=p → Schedule.Sized s →
        familiar s=forest x (squeeze (-t) y) → ∀ w : Sample (1+m),
          XSpace.Cirrus.grab w=p → Schedule.Sized w → familiar w=outgoing (squeeze (-t) y) →
        ‖coeff k (meshBasket N u v x s w d) -
          coeff k (Basket (install V) u v (Drock x) d x (squeeze (-t) y))‖ ≤ C * cost p := by
  obtain ⟨c,D,hc,hD,r⟩ := forest_admits hK hx hS hy E hE
  obtain ⟨t0,h0⟩ := r.exists
  obtain ⟨c',D',hc',hD',r'⟩ := forest_admits (isCompact_singleton (x:=(0:Points 1)))
    (singleton_subset_iff.mpr (show (0:Points 1) ∈ conf 1 from fun _ _ _ => Subsingleton.elim ..)) hS hy E hE
  obtain ⟨t1,h1⟩ := r'.exists
  obtain ⟨C,hC,hf⟩ := absorb (at_mesh_bond N h T A H a k c D hc hD (Fin.append u v)).delta
  rw [along,eventually_comap] at hf
  obtain ⟨B,hB,hf'⟩ := lamp_delta N h T A H u v K hK hx a k d c' D' hc' hD'
  refine ⟨max t0 t1,C+B,add_pos hC hB, ?_⟩
  filter_upwards [hf,hf'] with p hp hP t ht he x hx y hy s hs hv hr w hsw hvw hrw
  subst p
  obtain ha := h0 t ((le_max_left ..).trans ht) a x hx y hy s hv he hr
  have ht' : exp t ≤ E*(1+Schedule.theta w.F)^a := by change w.F=s.F at hsw; rw [hsw]; exact he
  obtain ha' := h1 t ((le_max_right ..).trans ht) a _ (Set.mem_singleton _) y hy w hvw ht' hrw
  unfold meshBasket Basket party; rw [show Lamp (install V) d (squeeze (-t) y) v (Drock x) = _
    from (show _ = retained N u v x (familiar w) d by rw [hrw]; rfl), ← hr, map_sub, map_sub,
    sub_sub_sub_comm, add_mul]
  exact (norm_sub_le ..).trans (add_le_add (hp ⟨s,ha⟩ rfl) (hP w hsw ha' x hx))

/-- Separate inputs on the *predictor* side -- tail (F.O), prices of the
formal OPE coefficients on inner shapes, and (F.1) prices of individual output-centre
kernels (`T = exp t`, `ChargeP` includes grades and a polynomial in *t*, not θ).
These do **not** come from WiderProfiles. `Canon.Physical` is a formal array property. -/
lemma separate_predictor_inputs (K : Set (Points n)) (S : Set (Points m))
    (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ O.Enh.Outside m)
    (k d : ℕ) :
    RangeP (install V) K S u v Drock d 1 (k+1) ∧ O.Bind.PaceX Drock ∧
    ∀ q : Q G, O.Enh.ChargeP (k+1) ((heft q : ℝ) + (totalG v : ℝ))
      (fun (i : ↥S) t => lonelyG (install V) (squeeze (-t) i.val) q v) := by
  have hw := (H.separatedOPE ν).wilson
  obtain hall := hw.far u
  exact ⟨hall.2.2 K hK hx d (k+1) m S v hS hy, hall.2.1,
    fun q => O.Enh.Uniform.teeth_P hw.scope hw.dimensions hS hy hw.awake v q (k+1)⟩
end YM.FVA2.WiderProfiles
