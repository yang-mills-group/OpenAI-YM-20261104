import YM.MS.ScaleForest.UV
import YM.MS.Dock.Dance

/-!
# Single line sewing in an ordered-scale graph

Graph readings use full external lists (color, ghost data, dynamical momenta).
Sector `m` is real momentum with `(4 + 2*m)` axes. Use it to TEST the
external data; the dimension of integration and tracing is `4 + 2*z`.
Weights in the Flats leg-array are indexed by number of **explicit** loops
(loops still to be counted as integrations in the graphs being evaluated,
not inside inserted counterterms). For this convention we use the following
elementary Feynman rules, including for an edge in a quotient graph:

* Bare action, single mark, and Wick half-line input are specified in `Mob`
  tensor conventions. The half-line is a Polchinski shell with the half from
  the second-order Wick operator. Use **both** orientations in a cross
  (in `bridgeG` they combine to give twice one kernel); impose conservation on the *first*
  component, which is
  unmarked. This fixes the continuation off the conservation locus as well.
  An ordered bulk/bulk forcing has a further factor `1/2`, but a join to a
  component with marks (ordinary, commuting sources) uses the **whole**
  cross. Use `scatter` (Koszul shuffle); external lists are in symbol
  convention (derivatives starting with the *first* element).
* A self join uses **ordered** half edges (left derivatives; the half-line
  already includes its factor). For our germs use the split-radial definition of
  dimensional integration. `innerTrace` uses exactly the open tensor trace
  including the extra direction trace `yeast`, and `closeG` does actual
  integration (NOT linear extension on arbitrary data). This fixes the
  evanescent prescription at noninteger dimension. No claim about doing
  dimensional regularization some other way. Use it also if the physical
  component of a field is all that is requested. We verify recovery of the
  ordinary-dimensional integral for integer dimension parameter, whenever the
  input is admissible and test axes fit. Also see `PolarView`: recovers the
  familiar radial weight `r^(codimension - 1)` in continuous dimension,
  including the complex parameter in a half-plane.

Scales: symbols stored at log length `s=0` and `y=0`. `y` is log mass in
`Train.tenorK` convention. At other values test with `Parade`. Prove that
the integrand scales back to the physical-momenta integral, including all
per-loop measure factors.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color
open Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick
open scoped Topology ContDiff

variable {G : Gauge} {K : Rip G} {F : Mob G} {b : Bool} {z : ℂ} {m n : ℕ}

/-- Ordered two-child contraction. `K` includes momentum/color kernel and is
already **halved**; include both terms of the Wick cross. -/
def bridgeG (K : Rip G) (F H : Mob G) : Mob G :=
  fun m w => scatter (field parity) w (fun l r =>
    let q := -net l
    ∑ i : Cfield G m, ∑ j : Cfield G m,
      (2 * K m i j q) * (cross (parity j) (degree (field parity) l) * F m ((i,q)::l)) * H m ((j,-q)::r))

/-- Actual dimension trace at supplied loop momentum in the test sector.
`yeast` is in `Arts/Tall`: sum a pair of vector legs in a new dimension,
accounted at *dimension parameter* `z`, not at the test sector's dimension. -/
def innerTrace (K : Rip G) (F : Mob G) (z : ℂ) (q : SectorP m) (w : Legs (Shore G m)) : ℂ :=
  (∑ i, ∑ j, K m i j q * F m ((i,q)::(j,-q)::w)) +
    (2*(z-m)) * yeast K F q w

/-- For evaluating the split integral on an external list, put the extra
radial variable in one new test axis. Keep the whole external ray to
parameterize the differentiations in `pruning`. -/
def loopCarpet (K : Rip G) (F : Mob G) (z : ℂ) (w : Legs (Shore G m)) (p : ℝ × ℝ) : ℂ :=
  ∫ q : SectorP m,
    innerTrace K F z (slideA (Nat.lt_succ_self m) (q,p.1)) (Arts.lift (Nat.le_succ m) (sail (ray w) p.2))
    ∂(Px m)

/-- Last edge closes a loop. Integrate the primary projection with radial
weight `r^(2*z+1)` and the m+1 chopping derivatives (`Arc.restore`, namely
`1/r * d/dr` with smooth extension to zero). -/
def closeG (K : Rip G) (z : ℂ) (y : ℝ) (F : Mob G) : Mob G :=
  fun m w => tenorK z y • (gage m • ∫ r : ℝ,
    (r:ℂ) ^ (2*z+1) * pruning (m+1) (loopCarpet K F z w) (r,1) ∂μhalf)

theorem bridgeG_eq (hu : reverseF K) (F H : Mob G) : bridgeG K F H = arbor K F H := by
  funext m w
  unfold bridgeG arbor tree
  exact scatter_congr _ w _ _ fun _ _ _ => Eq.symm (convertR (hu m))

theorem innerTrace_eq (K : Rip G) (F : Mob G) (z : ℂ) (q : SectorP m) (w : Legs (Shore G m)) :
    innerTrace K F z q w = Wtr z K F q w := by rw [Wtr,Pi.add_apply,Pi.smul_apply,at_trc]; rfl

theorem loopCarpet_eq (K : Rip G) (F : Mob G) (z : ℂ) (w : Legs (Shore G m)) :
    loopCarpet K F z w = carpet (Px m) (wing z K F (ray w)) := by
  funext p
  unfold loopCarpet carpet
  simp_rw [innerTrace_eq]
  rfl

theorem closeG_eq (K : Rip G) (F : Mob G) (z : ℂ) (y : ℝ) : closeG K z y F = tenorK z y • ocean z K F := by
  funext m w
  rw [closeG,loopCarpet_eq]; rfl

theorem loopCarpet_integrable (hK : rPrice K) (hF : kPrice F) (z : ℂ) (w : Legs (Shore G m)) (p : ℝ × ℝ) :
    Integrable (fun q : SectorP m =>
      innerTrace K F z (slideA (Nat.lt_succ_self m) (q,p.1)) (Arts.lift (Nat.le_succ m) (sail (ray w) p.2)))
      (Px m) := by
  simp_rw [innerTrace_eq]
  exact (Arc.Q.Gmajor (Px m) (exact_test hF hK (ray w) z) ()).values p

/-- Prices and convergence of all the operations in closing the loop. -/
theorem loop_converges (hK : Knot b K) (hF : Form0 b F) (hz : z ∈ Town) (w : Legs (Shore G m)) :
    (∀ p : ℝ × ℝ, Integrable (fun q : SectorP m =>
      innerTrace K F z (slideA (Nat.lt_succ_self m) (q,p.1)) (Arts.lift (Nat.le_succ m) (sail (ray w) p.2)))
      (Px m)) ∧
    (∀ j, Ultra (pruning j (loopCarpet K F z w)) ∧ Reflect (pruning j (loopCarpet K F z w)) ∧
      ∀ p : ℝ × ℝ, IntervalIntegrable (fun t : ℝ => Arc.d (Arc.d (pruning j (loopCarpet K F z w)))
        (t*p.1,p.2)) MeasureTheory.volume 0 1) ∧
    Integrable (fun r : ℝ => (r:ℂ)^(2*z+1) * pruning (m+1) (loopCarpet K F z w) (r,1)) μhalf := by
  refine ⟨loopCarpet_integrable hK.price hF.price z w,?_⟩
  rw [loopCarpet_eq]
  let g := carpet (Px m) (wing z K F (ray w))
  have ht : Ultra g := carpet_test hF.price hK.price _ z
  have hv : Reflect g := mirror_r (Px m) (wing_mirror hF.token hK.token z _)
  refine ⟨fun j => ⟨(pruned ht (fun _ => hv) j).1,(pruned ht (fun _ => hv) j).2 (), fun p => ?_ ⟩,
    meets ((pruned ht (fun _ => hv) _).1) hz 1⟩
  exact ((fresh (fresh ((pruned ht (fun _ => hv) j).1.smooth ()))).continuous.comp
    (show Continuous (fun t : ℝ => (t*p.1,p.2)) by fun_prop)).intervalIntegrable 0 1

theorem feeD_pitch (m : ℕ) : feeD m * (pitch m : ℝ) = (↑(((2*π)^ (4 + 2*m))⁻¹) : ℂ) := by
  have ht : 0 < 2 * π := by positivity
  have h : 0 < π := Real.pi_pos
  have he := Nat.factorial_ne_zero m
  unfold feeD room Arc.pitch
  rw [Complex.Gamma_nat_eq_factorial, Complex.exp_nat_mul, ← Complex.ofReal_exp,
    Real.exp_sub, Real.exp_log h, show (2:ℝ) * log (2*π) = log (2*π) + log (2*π) from two_mul _,
    Real.exp_add, Real.exp_log ht]
  push_cast
  rw [div_pow,pow_add,pow_mul]
  field_simp
  ring_nf
  rw [inv_pow,mul_inv_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr h.ne'))]

theorem closeG_integer (hK : Knot b K) (hF : Form0 b F) (hL : m ≤ n) (w : Legs (Shore G m)) (y : ℝ) :
    (Integrable (fun q => ∑ i, ∑ j, K n i j q * F n ((i,q)::(j,-q):: Arts.lift hL w)) (Px n)) ∧
    closeG K n y F m w = Complex.exp (-(y:ℂ)*2*n) * ((↑(((2*π)^ (4 + 2*n))⁻¹) : ℂ) *
      ∫ q, ∑ i, ∑ j, K n i j q * F n ((i,q)::(j,-q):: Arts.lift hL w) ∂(Px n)) := by
  simp_rw [← at_trc]
  constructor
  · exact theory hF.price hK.price n (Arts.lift hL w)
  rw [closeG_eq, Pi.smul_apply, Pi.smul_apply, reg_proj hF.price hK.price hF.token hK.token hL,
    Complex.real_smul, smul_eq_mul, restore_tape]
  unfold Ccy
  rw [mul_comm (feeD _), mul_assoc, ← mul_assoc (feeD _), feeD_pitch]

/-- Force entries in the forest's representation at unit length and y=0. -/
def bridgePages (K : Rip G) (X Y : Flats G) : Flats G :=
  X.sum fun m x => Y.sum fun n y => Finsupp.single (n+m) (fun z : ℂ => bridgeG K (x z) (y z))
def closePages (K : Rip G) (X : Flats G) : Flats G :=
  X.sum fun m x => Finsupp.single (m+1) (fun z : ℂ => closeG K z 0 (x z))

theorem bridgePages_eq (hu : reverseF K) (X Y : Flats G) : bridgePages K X Y = TreeN K X Y := by
  rw [TreeN, explodeL, bridgePages]
  simp_rw [bridgeG_eq hu]
  rfl

theorem bridge_meter (hu : reverseF K) (X Y : Flats G) (z : ℂ) (h : ℕ) (y s : ℝ) :
    Parade (bridgePages K X Y) h y s z = bridgeG (pulse 4 s K) (Parade X 4 y s z) (Parade Y h y s z) := by
  rw [bridgeG_eq (a_rev s 4 hu), bridgePages_eq hu]
  exact tree_at hu (by norm_num) y s z

theorem closeG_valid (hK : Knot b K) (hF : Form0 b F) (hz : z ∈ Town) (y : ℝ) :
    closeG K z y F = unitC z y K F := by
  rw [closeG_eq,unitC,LinearMap.smul_apply,dollar hK hF hz]

theorem closeG_swamp (hK : Knot b K) {f : Coat G} (hF : Form0 b (f z)) (hz : z ∈ Town) :
    closeG K z 0 (f z) = swamp K f z := by
  rw [closeG_eq,swamp_spec hK hF hz,restore_tape]
  simp

theorem closePages_pact (hK : Knot b K) {X : Flats G} (hp : Moony b X) : Pact (closePages K X) (CycleN K X) := by
  intro i
  filter_upwards [Moony.sunup hp,high0] with z hz hv
  rw [CycleN,blap,closePages,Finsupp.sum,Finsupp.sum,Finsupp.finsetSum_apply,Finsupp.finsetSum_apply,
    Finset.sum_apply,Finset.sum_apply]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finsupp.single_apply, Finsupp.single_apply]
  split
  · exact closeG_swamp hK (hz j) hv
  rfl

/-- In particular the z dependence in the cycle operation is precisely the
dimensional momentum *integral*, including when used on contracted child
graphs. Scale back to the retained-cutoff kernel and its log mass variable. -/
theorem close_meter (hK : Knot b K) {X : Flats G} (hp : Moony b X) (h : ℕ) :
    ∀ᶠ z in dotty, ∀ y s, Parade (closePages K X) h y s z = closeG (pulse 4 s K) z y (Parade X h y s z) := by
  filter_upwards [took (closePages_pact hK hp), Moony.sunup (all0 hp), Moony.march (all0 hp) h,
    high0] with z hz hu hF hv
  intro y s
  rw [treaty z hz h y s, closeG_valid (fze (heed hK) _ _) (hF y s) hv]
  exact length_at hv (heed hK) hu (by norm_num) s y

end YM.MS.ScaleForest
