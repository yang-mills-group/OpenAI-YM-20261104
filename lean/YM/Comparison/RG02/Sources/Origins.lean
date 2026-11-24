import YM.Comparison.RG02.Step.History
import YM.Comparison.RG02.Sources.Smaller
import YM.Comparison.RG02.Sources.Dilation
import YM.Extra.MULTISOURCE_TRAJECTORIES.Initial
import YM.Extra.MULTISOURCE_TRAJECTORIES.Trials
import YM.Next.MULTISOURCE.Off
import YM.Next.MULTISOURCE.Single
/-!
# Source bridges on the actual History

 R.Home is the same MarkedVac. `array` wraps Insertions.total (including engineering units on
  arrays; careful to use in smul direction). At all levels preserves true full vacuum, regular
 or flagged. `along` transmits to the local step; `law_read` on unnormalized charge; `any_lane`
 for comparing same Works data; `singleton` aligns exact product with open calibration direction
 of Same Family. Reweight for use at designated source scheduling and readout. No independence
 or distinct stencil-name requirement. Sparse horizon deletion no budget changes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Sources
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree Overlay
open YM.Marker YM.Multi YM.Comparison.RG02.Order Integral Actual Local
open YM.Extra.Trajectories (Names Insertions Probes matrixField matrixField_cont thermal observable)
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {H : History G} {N p m : ℕ} {V V' : Type}
   [DecidableEq V] [DecidableEq V'] {C : Census V} {C' : Census V'}
   (I : Insertions H V N p) (J : Insertions H V' N p)

def array (C : Census V) (m : ℕ) (x : Config G (H.S.side m p)): Poly C:= Poly.inject fun j => I.total j m (matrixField x)
lemma array_on (j : C.Mode) (m : ℕ) : atMark j (array I C m) = I.total j m ∘ matrixField:= rfl
variable (hm : m ≤ N)
local notation "S"=> (H.levels.clock.op m p)
local notation "R"=> (H.rep N p m)
local notation "R'"=> (H.rep N p (m+1))
variable (C)
def zoom (m : ℕ) (i : V) := ( ( (↑(H.S.block m).val:ℝ) : ℂ)) ^ (I.load i)
lemma along (h : m<N) : times (zoom I m) (yield (R') (array I C (m+1)) S)= array I C m := by
  ext x i
  rw [times,comp_apply,dilation_part, yield,grades]
  dsimp only
  change _= I.total i m (matrixField x); rw [I.total_step i m h, Pi.smul_apply,Insertions.step_push m (I.smooth_total i h).continuous]; rfl
include hm
lemma fits_array : Leaf.All (array I C m):= fun i=> Envelope.compactC ((I.smooth_total i hm).continuous.comp matrixField_cont)
lemma deposit (u : Names C' C) : remap u (array I C m)=array (I.subset u) C' m:= by
   ext x s; exact congrFun (I.total_shared u s m hm) (matrixField x)

variable (hH : H.Selected)
include hH
lemma ledger (x : Config G (H.S.side m p)) : (array I C m x).part C.quiet = (R|>.eval x:ℂ) := by
   rw [← Insertions.vac_eq hH hm]; exact congrFun (I.quiet_eq hm) (matrixField x)
lemma gives (hI : I.Symmetric) : Floor R (array I C m) :=
 ⟨ledger C I hm hH,fits_array C I hm, fun t y=> Marker.Poly.ext fun i=> (I.total_gauge hI i hm) t y⟩
lemma income (x : Config G (H.S.side m p)) : I.ratios C m (matrixField x)= unitScale (array I C m x) := by
  ext i; rw [unitScale,ledger C I hm hH x, ← Insertions.vac_eq hH hm, Poly.part_smul, Insertions.part_ratios,Complex.ofReal_inv]; exact mul_comm ..
omit hH hm in
lemma top (s : C.Mode) (x) : (array I C N x).part s= Ride.bump (H.S.a N) s I.load * (bare (H.β N p N) x : ℂ) * Ride.Product I.uses s x := by change I.total s N _=_; rw [Insertions.total_top]; exact I.source_eq ..
-- Price and reporting supports still open. No required ordering/conjugacy pairing, any moment.
omit hm hH in
lemma units (s : C.Mode) (m : ℕ): Ride.bump (H.S.a m) s I.load= Ride.bump ((H.S.block m).val : ℝ) s I.load * Ride.bump (H.S.a (m+1)) s I.load := by
   unfold Ride.bump; rw [← prod_mul_distrib]; apply prod_congr rfl; intro i _; rw [← mul_pow,← Complex.ofReal_mul,H.S.a_step, mul_div_cancel₀ _ (by exact_mod_cast (H.S.block m).2.ne')]

-- global Wilson moment normalization exactly (compare Lane.from_/Signals, no
-- assumptions of a lane having been selected). No approximation at any marked order.
omit hH in
lemma law_read (s : C.Mode) : (charge (prior G _) (array I C m)).part s = Ride.bump (H.S.a m) s I.load * (partition G (H.S.side N p) (H.β N p N):ℂ) * moment (H.β N p N) (Ride.Product I.uses s) := by
   induction hm using Nat.decreasingInduction with
   | self=>
     rw [moment_formula _ _ (I.reads s), components]; unfold atMark; simp_rw [top,mul_assoc,integral_const_mul]; rw [mul_inv_cancel_left₀]; exact Complex.ofReal_ne_zero.mpr (partition_pos _).ne'
   | of_succ i hi IH=>
     rw [← along C I hi, ← measure_times, dilation_part, units C I s i, mul_assoc (Ride.bump _ _ _),mul_assoc (Ride.bump _ _ _),← IH]
     congr 1
     -- full charge all tags retained; equality across levels by History.
     have h:=fits_array C I hi
     rw [components,components]; unfold yield
     rw [ (show atMark s (Actual.Push (H.levels.clock.op i p) (H.rep N p (i+1)).beta (array I C (i+1))) = _ from funext fun V=> congrFun (grades (D:=array I C (i+1)) V (H.rep N p (i+1)).beta) s),StepData.push_integral (H.levels.transition_mass i p _) _ ((h s).integrableC _)]

-- whole G phase transfer C anchored through normalized Tables. record gauge support.
omit hH hm in
lemma units_nonzero (s : C.Mode) (m : ℕ) : Ride.bump (H.S.a m) s I.load ≠ 0 := prod_ne_zero_iff.mpr fun _ _=> pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (H.S.a_pos m).ne')
lemma report (s : C.Mode): (unitScale (charge (prior G _) (array I C m))).part s= Ride.bump (H.S.a m) s I.load * moment (H.β N p N) (Ride.Product I.uses s) := by
   have h : (charge (prior G _) (array I C m)).part C.quiet = (partition G (H.S.side N p) (H.β N p N):ℂ) := by
     rw [components]; unfold atMark; simp_rw [ledger C I hm hH]; rw [← H.partition_eq hH N p m hm]; exact integral_ofReal
   rw [unitScale,Poly.part_smul,h, law_read C I hm]; have hz := Complex.ofReal_ne_zero.mpr (partition_pos (G:=G) (n:=H.S.side N p) (H.β N p N)).ne'; field_simp

omit hH hm in
lemma communicate [Fintype V] (level : ℕ) (hM : level≤ m) (hmN : m≤N) (L : Lane H C N p) (h : L.Works level)
   (hp : L.uses=I.uses) (hL : L.load=I.load): (L.sites m).density=array I C m := by
   induction hmN using Nat.decreasingInduction with
   | self=>
       ext V s; have he := h.first s V; rw [hp,hL] at he; exact he.trans (top C I s V).symm
   | of_succ j hj IH=>
       have he:∀ s, L.signal (j+1) s=atMark s (array I C (j+1)):= fun s=>by change atMark s (L.sites (j+1)).density=_; rw [IH (hM.trans j.le_succ)]
       ext V s; rw [← along C I hj]; change L.signal j s V=atMark s (times (zoom I j) _ ) V; rw [at_times,h.step j hM hj s, hL,he]
       exact congrArg ( (Ride.bump (H.S.block j).val s I.load) • ·) (congrFun (grades (D:=array I C (j+1)) V _) s).symm

variable {M : Family G} (A : Probes M V N p) (h : M.Makes)
include h
omit hH in
lemma probed : Floor (M.path.rep N p m) (array A.toInsertions C m):= gives C _ hm h.wilson (A.symmetric h)
omit hH in
lemma records (s : C.Mode) : (unitScale (charge (prior G _) (array A.toInsertions C m))).part s= Ride.bump (M.S.a m) s A.d * M.omega N p (fun x=> ∏ i∈s.val,A.eval i x) := by
   rw [report C _ hm h.wilson]; unfold Ride.Product; simp_rw [A.physical]; rfl
end YM.Comparison.RG02.Sources
