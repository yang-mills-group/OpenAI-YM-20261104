import YM.Comparison.Stencils.Symbol
import YM.Push.RELAY_MARK.Rising
import YM.Next.FOUNDATIONS.Readout

/-!
# The radial projection used on the bare formal symbols

Use the actual lattice log-holonomy test and both order indices. Even smooth
(in particular nonlinear) components of an operator density can be projected
before applying an EOM or all-spectator test. This is the finite-support,
test-address-zero calculation; coupling and test-degree extensions on top of
it separately. No gradient/dynamical equation imposed on polynomial data.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Stencils.Feed
open CubicMatch Lattice Function RG Wilson Symbols Labels Source Source.Drops Filter Push.Mark
open Next.Foundations
open Planned.PrimaryIntegral295.Place (Spot Dev slant placeEdge pore pore_site polynomial_smooth)
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {d : ℕ} {S : Finset Cover}

section Radial

/-- Local patch log of the actual holonomies (near zero radial amplitude).
Must use germ for reexponentiation; no branch agreement far away. -/
def rule (S : Finset Cover) (H : Hol G) (d : ℕ) (X : Snap G d) : Dev S G :=
  Symbols.patch S (fun e => G.plog (G.mat (H.links d (expand d X) 1 e)))

theorem rule_zero (S : Finset Cover) (H : Hol G) (d : ℕ) : rule S H d 0 = 0 := by
  funext e
  change G.plog (G.mat (H.links d _ _ (placeEdge e))) = 0
  rw [(Work.G02.linkGerm H d (placeEdge e)).2.1, G.mat_one, G.plog_one]

lemma rule_diff (S : Finset Cover) (H : Hol G) (d : ℕ) : ContDiffAt ℝ ω (rule S H d) 0 := by
  refine contDiffAt_pi.mpr fun i => ?_
  have hx := Work.G02.linkGerm H d (placeEdge i)
  exact (show ContDiffAt ℝ ω G.plog (G.mat (H.links d (expand d 0) 1 (placeEdge i))) by
    rw [hx.2.1,G.mat_one]; exact G.plog_diff).comp 0 hx.1.contDiffAt

lemma germ (S : Finset Cover) (H : Hol G) (d : ℕ) :
    ∀ᶠ v in 𝓝 (0 : Snap G d), Agrees S (pore (rule S H d v)) (H.links d (expand d v) 1) := by
  classical
  have hp (i : Spot S) : ∀ᶠ v in 𝓝 (0 : Snap G d),
      pore (rule S H d v) (placeEdge i) = H.links d (expand d v) 1 (placeEdge i) := by
    have he := Work.G02.linkGerm H d (placeEdge i)
    let U (p : Snap G d) := H.links d (expand d p) 1 (placeEdge i)
    have hh : ContinuousAt U 0 :=
      (G.continuous_mat.isClosedEmbedding G.mat_injective).isInducing.continuousAt_iff.mpr he.1.continuousAt
    have hf : Tendsto U (𝓝 0) (𝓝 1) := he.2.1 ▸ hh.tendsto
    filter_upwards [hf.eventually G.plog_right] with v hv
    rw [pore_site]; exact hv
  filter_upwards [eventually_all.mpr hp] with v hv
  intro e he he'
  exact hv ⟨(⟨e.1,he⟩,e.2),he'⟩

/-- Contact-unrelated scale test on formal symbols of finite support. -/
def reading (H : Hol G) (d : ℕ) (P : LocalPol G S) : Snap G d → ℂ := fun x =>
  inscribe (rule S H d x) P

lemma program_smooth (P : LocalPol G S) : ContDiff ℝ ω (fun x : Dev S G => inscribe x P) :=
  polynomial_smooth P _ fun i : Var G S =>
    (Complex.ofRealCLM.contDiff).comp (coordinate i).contDiff

lemma reads_smooth (H : Hol G) (d : ℕ) (P : LocalPol G S) : ContDiffAt ℝ ω (reading H d P) 0 :=
  (program_smooth P).contDiffAt.comp 0 (rule_diff S H d)
end Radial

section Projection
abbrev Dot (G : Gauge) (d : ℕ) := (j : Fin (d-1)) × Fin (dim G j.val)

def toKey (i : Dot G d) : Key G := ⟨i.1.val, i.2⟩
def rayPin (i : Dot G d) : Snap G d := Pi.single i.1 (axes G i.1.val i.2)

def coefficient (X : Snap G d) (i : Dot G d) : ℝ := (axes G i.1.val).repr (X i.1) i.2
lemma plotted (J : Jet G) (i : Dot G d) : coord J (toKey i) = ↑(coefficient (trunk d J) i) := rfl
lemma rayPin_sum (x : Snap G d) : ∑ i : Dot G d, coefficient x i • rayPin i = x := by
  classical
  unfold Dot
  funext k
  rw [Fintype.sum_sigma,Finset.sum_apply,Finset.sum_eq_single k]
  · simp only [Finset.sum_apply, rayPin, Pi.smul_apply, Pi.single_eq_same, coefficient]; exact (axes G k.val).sum_repr _
  · intro j _ hj; simp [Finset.sum_apply, rayPin, Pi.single_eq_of_ne hj.symm]
  simp

/-- Finite Taylor test in *amplitude* of independent (radial) slot variables. -/
def band (u : Snap G d → ℂ) (k : ℕ) : Pol G :=
  stencilPol (E := Snap G d) rayPin toKey k (Tensor.coeff u k 0)

lemma band_degree (u : Snap G d → ℂ) (k : ℕ) : Rank (band u k) k :=
  stencilPol_rank ..
lemma band_value (u : Snap G d → ℂ) (k : ℕ) (J : Jet G) :
    Labels.read J (band u k) = Tensor.diagonal (Tensor.coeff u k 0) (trunk d J) :=
  stencilPol_value _ _ _ _ _ _ _ (rayPin_sum _).symm (plotted J)

def letter (H : Hol G) (d : ℕ) (P : LocalPol G S) (k : ℕ) : Labels.Pol G :=
  band (reading H d P) k

lemma radial_amplitude (H : Hol G) (d : ℕ) (P : LocalPol G S) (k : ℕ) (J : Jet G) :
    Labels.read J (letter H d P k) = term k (fun t : ℝ => reading H d P (t • trunk d J)) :=
  (band_value _ _ _).trans ((term_ray ((reads_smooth H d P).of_le le_top) (trunk d J)).symm)

def polynomial (H : Hol G) (d : ℕ) (P : LocalPol G S) : Pol G :=
  ∑ k ∈ Finset.range (d+1), letter H d P k

theorem polynomial_exact (H : Hol G) (d : ℕ) (P : LocalPol G S) (J : Jet G) :
    Labels.read J (polynomial H d P) = Work.G05.blockTaylor d (reading H d P) (trunk d J) := by
  rw [polynomial, Work.G05.blockTaylor, map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl; intro i _; exact band_value _ _ _

def trail (J : Jet G) (d : ℕ) (t : ℝ) := trunk d (scaleJet J t)

lemma trail_root (J : Jet G) (d : ℕ) : trail J d 0 = 0 := by funext i; simp [trail, trunk, scaleJet]
lemma trail_smooth (J : Jet G) (d : ℕ) : ContDiff ℝ ω (trail J d) := by
  apply contDiff_pi.mpr; intro i
  have hv {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (j : ℕ) (c : F) : ContDiff ℝ ω (fun t : ℝ => t^j • c) := (contDiff_id.pow _).smul contDiff_const
  exact hv _ _

def rawPi (H : Hol G) (d : ℕ) (P : LocalPol G S) := capRead d (polynomial H d P)

lemma raw_cap (H : Hol G) (d : ℕ) (P : LocalPol G S) : rawPi H d P ∈ limited G d :=
  cap_limited ..

theorem geometry (H : Hol G) (d : ℕ) (P : LocalPol G S) (J : Jet G) (k : ℕ) (hk : k ≤ d) :
    iteratedDeriv k (fun t => Labels.read (scaleJet J t) (rawPi H d P)) 0 =
      iteratedDeriv k (fun t => reading H d P (trail J d t)) 0 := by
  let X := polynomial H d P
  let f := reading H d P
  have hu : ContDiffAt ℝ d (trail J d) 0 := (trail_smooth J d).contDiffAt.of_le le_top
  have ht : ContDiffAt ℝ d f 0 := (reads_smooth H d P).of_le le_top
  have ht' : ContDiffAt ℝ d f (trail J d 0) := (trail_root J d).symm ▸ ht
  have he : iteratedFDeriv ℝ k (Work.G05.blockTaylor d f ∘ trail J d) 0 =
      iteratedFDeriv ℝ k (f ∘ trail J d) 0 :=
    Work.G05.jets_comp hu hu (Work.G05.blockTaylor_contDiff d f _).contDiffAt ht' rfl
      (fun _ _ => rfl) (fun i hi => by rw [trail_root]; exact Work.G05.blockTaylor_jets ht i hi) k hk
  rw [rawPi, deriv_read, tier_capRead d _ k hk, ← deriv_read]
  simp_rw [polynomial_exact]
  exact DFunLike.congr_fun he _

lemma unwrap (H : Hol G) (d : ℕ) (J : Jet G) (t : ℝ) :
    rule S H d (trail J d t) = Symbols.patch S (fun e => G.plog (G.mat (H.links d J t e))) := by
  rw [scales H J]; rfl

/-- Finite-support form of the jet bracket, before coupling
powers. Native link coordinates; `P` takes log variables in physical
Lie algebra normalization. Evaluate `plog` only in this test germ. -/
theorem jet_reads (H : Hol G) (d : ℕ) (P : LocalPol G S) (J : Jet G) (k : ℕ) (hk : k ≤ d) :
    iteratedDeriv k (fun t => Labels.read (scaleJet J t) (rawPi H d P)) 0 =
      iteratedDeriv k (fun t => inscribe (Symbols.patch S (fun e => G.plog (G.mat (H.links d J t e)))) P) 0 := by
  rw [geometry H d P J k hk]; simp_rw [reading, unwrap]

/-- Uniqueness even off-shell and with non-invariant polynomials (e.g. color
legs before combination). -/
lemma sole_poly (H : Pol G) (J : Pol G) (d : ℕ) (h : H ∈ limited G d) (g : J ∈ limited G d)
    (e : ∀ X : Jet G, ∀ k ≤ d,
      iteratedDeriv k (fun t => Labels.read (scaleJet X t) H) 0 =
      iteratedDeriv k (fun t => Labels.read (scaleJet X t) J) 0) : H = J := by
  have he (k : ℕ) (hk : k ≤ d) : tier k H = tier k J := by
    apply Labels.eval_ext
    intro A
    have hu := e A k hk
    rw [deriv_read, deriv_read] at hu
    exact smul_right_injective ℂ (show (k.factorial : ℝ) ≠ 0 by positivity) hu
  rw [← limited_cap d H h, ← limited_cap d J g]
  exact Finset.sum_congr rfl fun i hi => he i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

lemma ray_smooth (H : Hol G) (d : ℕ) (J : Jet G) (P : LocalPol G S) :
    ContDiffAt ℝ ω (fun t => reading H d P (trail J d t)) 0 := by
  refine ContDiffAt.comp (g := reading H d P) _ ?_ (trail_smooth J d).contDiffAt
  rw [trail_root]; exact reads_smooth ..

/-- Projection into the ambient polynomial space. For invariant data,
will also have membership in `localFields`. -/
def projector (H : Hol G) (d : ℕ) : LocalPol G S →ₗ[ℂ] Pol G where
  toFun P := rawPi H d P
  map_add' P Q := by
    refine sole_poly _ _ d (raw_cap ..) (Submodule.add_mem _ (raw_cap ..) (raw_cap ..)) ?_
    intro J k hk
    simp only [map_add]
    rw [geometry _ _ _ J k hk, iteratedDeriv_fun_add (Next.Foundations.read_smooth J _ _).contDiffAt
      (Next.Foundations.read_smooth J _ _).contDiffAt, geometry _ _ _ J k hk, geometry _ _ _ J k hk]
    simp only [reading, map_add]
    exact iteratedDeriv_fun_add ((ray_smooth H d J P).of_le le_top) ((ray_smooth H d J Q).of_le le_top)
  map_smul' c P := by
    refine sole_poly _ _ d (raw_cap ..) (Submodule.smul_mem _ _ (raw_cap ..)) ?_
    intro J k hk
    simp only [map_smul]
    rw [geometry _ _ _ J k hk, iteratedDeriv_fun_const_smul_field, geometry _ _ _ J k hk]
    simp_rw [reading, map_smul]; rw [iteratedDeriv_fun_const_smul_field]; rfl
end Projection
end YM.Comparison.Stencils.Feed
