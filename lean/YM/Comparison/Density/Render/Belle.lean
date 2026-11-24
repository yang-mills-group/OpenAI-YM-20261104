import YM.Comparison.Density.Render.Valence

/-!
Rank-two affine normalization of formal analytic extra packets. The
clover subtracted from EVERY placement, even winding paths, is the
syntactic affine response in the cover. We don't use a large-torus
replacement to assert that a tau criterion of perturbed atoms equals
that of actual atoms. The sum structure of formal packet determines
when the clover contacts total to zero. Exact residual-Hessian with
all LEFT derivatives; rank valuation from true group links.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Render
open Fusing Markers RG Lattice Function Finset MeasureTheory Filter Wilson
open Ovens Extra.Iteration
open Progress.DirectedRecipe AnalyticBridge.VerifiedReset AnalyticBridge.VerifiedReset.Collection
open WilsonStartup Averaging Geo Next.Scheduling Next.Scheduling.Wages Precision Work.F03 Work.G07 StressFlux
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff InnerProductSpace
open Transport AnalyticBridge.SectorAffine.Offset FreeResolvent.Affine FreeResolvent.TestD
variable {G : Gauge} {n : Side} {k t m : ℕ} {B : BudgetPoint}

variable (o : Site n)
def grow (M : ℕ) : ℝ:=4*(((G.colorScale)⁻¹*ticket G (meter G M) M)*5^M)
-- Through petals ordinary germs, independent of o/n. Use real projector.
lemma trail_pan (j : PlaqAxes) {V : Directions G n} (hv : ‖V‖≤1) :
    Through k (fun A : Directions G n=> petals (increment 1 A) o j) V (grow (G:=G) k) := by
  let H:= grow (G:=G) k
  have he (a b:Lattice.Step) : Through k (fun A : Directions G n=> plate (increment 1 A) o a b) V ((G.colorScale⁻¹*ticket G (meter G k) k)*5^k) := by
    let l:=oriented a b
    have hp:=ContinuousLinearMap.opNorm_le_bound (Wages.projector G) (inv_nonneg.mpr G.colorScale_pos.le) (Wages.norm_projector G)
    have hu:= worded (k:=k) o l hv; apply (abroad hu (Wages.projector G)).mono
    apply (mul_le_mul_of_nonneg_right hp hu.nonneg).trans
    rw [show l.length=4 from rfl]; norm_num; exact mul_assoc .. |>.symm.le
  have hz (a : Axis) (b : Axis) := (minus (minus (he (posDir a) (posDir b)) (he (posDir a) (negDir b))) (minus (he (negDir a) (posDir b)) (he (negDir a) (negDir b)))).scale ((4:ℝ)⁻¹)
  unfold petals clover stencil; apply (hz ..).mono; unfold grow; have ht:=tick_nn G k; have :=G.colorScale_pos
  have hu: 0≤(G.colorScale⁻¹*ticket G (meter G k) k)*5^k:=by positivity
  norm_num; linarith only [hu]

variable (a : Atom G 2)
def tag (u : Flux G) := a.poly fun i=>u (a.leg i).plaq
def pollen (U : Config G n) := tag a (petals U o)
def baseLine (U : Config G n) := a.unmasked U o
lemma bloom_price {U:Directions G n} (hU : ‖U‖≤1): Through k (fun A=> pollen o a (increment 1 A)) U (a.magnitude*(couple k*grow (G:=G) k)^2):=
    bundle a _ _ (fun i=> trail_pan o (a.leg i).plaq hU)

-- derivative bound in left norm at the anchor with fixed halo footprints.
def bloom (G : Gauge) (B : BudgetPoint):= 2^B.order*(colorBill G 4 B.power B.order)^2
lemma bud_bill (B : BudgetPoint): Bill B o (Healthy B.threshold {o}) (a.magnitude*bloom G B* B.threshold^2) (pollen o a):= by
  let C:=colorBill G 4 B.power B.order* B.threshold
  let f i (j:G.ColorIndex) (U:Config G n):= petals U o (a.leg i).plaq j
  have he i (j:G.ColorIndex):Bill B o (Healthy B.threshold {o}) C (f i j):= Wages.extracts (petals_bill B o _) j
  let v:=a.magnitude*bloom G B*B.threshold^2
  have hx i (j:G.ColorIndex) l q : Bill B o (Healthy B.threshold {o}) (bloom G B*B.threshold^2) (fun U=> f i j U * f l q U):= by
    have h:= (he i j).mul (he l q) (by norm_num)
    exact Bill.le h (by dsimp only [C]; unfold bloom; apply le_of_eq; ring)
  have hW j := Bill.mul_left (a.coeff j) (hx 0 (j 0) 1 (j 1))
  rw [show pollen o a=(fun U=> ∑ j, a.coeff j*(f 0 (j 0) U * f 1 (j 1) U)) from funext (fun x=>by simp only [pollen,tag,Atom.poly,Fin.prod_univ_succ, Fin.prod_univ_zero,mul_one]; rfl)]
  apply Bill.le (f:=fun U=> ∑ j, a.coeff j*(f 0 (j 0) U * f 1 (j 1) U)) (Bill.sum univ (fun j _=> hW j))
  unfold Atom.magnitude; rw [sum_mul,sum_mul]; exact le_of_eq (sum_congr rfl (fun j _=>by rw [mul_assoc]))
lemma fertile (U V : Config G n) (h : Agrees (halo 2 {o}) U V) : pollen o a U=pollen o a V:= by
  unfold pollen tag; congr! 2 with i; exact petals_reads o _ U V h

lemma stows {j : Fin 2} : walkCuts (a.leg j) o ⊆ a.footprint o:= by
  intro s hs; obtain ⟨x,hx,rfl⟩:= mem_image.mp hs; exact mem_image_of_mem _ (mem_insert_of_mem (mem_biUnion.mpr ⟨_,mem_univ _,hx⟩))

private lemma little_limit (g : Fin 2 → ℝ → G.Color) (w : Fin 2→ G.Color) (h : ∀ i, Tendsto (fun t:ℝ=> t⁻¹ • g i t) (𝓝[≠] 0) (𝓝 (w i))):
    Tendsto (fun t=> a.poly (fun i=> g i t)/t^2) (𝓝[≠] 0) (𝓝 (a.poly w)) := by
  let f z := a.poly z
  have ht : Continuous f:= by unfold f Atom.poly; fun_prop
  have hP:= (@ContinuousAt.tendsto _ _ _ _ f w ht.continuousAt).comp (show Tendsto (fun t:ℝ=> fun i=> t⁻¹ • g i t) (𝓝[≠] 0) (𝓝 w) from tendsto_pi_nhds.mpr h)
  refine hP.congr' ?_; apply Eventually.of_forall; intro x
  simp only [Function.comp_apply,f,Atom.poly, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  rw [Finset.sum_div]; apply sum_congr rfl; intro i _
  change a.coeff i*((x⁻¹*_) * (x⁻¹*_))=_; ring_nf; rfl

lemma base_zero : a.unmasked (1:Config G n) o=0:= by simp [Atom.unmasked, transported,roll,G.curvature_unit,unitTravel,Atom.poly]
lemma pollen_zero : pollen o a (1:Config G n)=0:= by simp [pollen,tag,Atom.poly]

lemma credit_pair {S : Support n} (hA : a.Invariant) (hX : halo 2 {o} ⊆ S) (hp : a.footprint o ⊆ S) :
    B.Regular S (baseLine o a-pollen o a) ∧ B.supBounds o S (baseLine o a-pollen o a)
      (Wages.price B a+a.magnitude*bloom G B*B.threshold^2) := by
  have hf : B.Regular S (baseLine o a):= reg_larger (Derivs.canonical_regular a o B hA) hp
  have he := bud_bill o a B
  have hy : B.Regular (halo 2 {o}) (pollen o a) := by
    refine reg_bill he ?_ (fertile o a) ?_
    · unfold pollen tag Atom.poly; fun_prop
    intro k U; unfold pollen tag; simp only [petals_gauge]; exact hA ..
  refine ⟨reg_sub hf (reg_larger hy hX),?_⟩
  exact sup_sub hf (reg_larger hy hX) (sup_larger (Wages.total B a o) hp) (Bill.sup he (fun _ hV=> healthy_mono (singleton_subset_iff.mpr (hX (halo_subset 2 {o} (mem_singleton_self _)))) hV))

set_option maxHeartbeats 400000 in
lemma rebases {S : Support n} (hG : G.Simple) (hA : a.Invariant) (p : BudgetPoint) (hX : halo 2 {o} ⊆ S) (hp : a.footprint o ⊆ S)
    (hS : Nonwrapping S o) (hn : 20<n.val) :∀ x y,IsAffineDirection o x → IsAffineDirection o y → logHessian (baseLine o a-pollen o a) x y = 0 := by
  have hx := (credit_pair o a (B:=p) hA hX hp).1
  apply affine_zero hx; intro v
  have he := (little_limit a (fun i t=> (a.leg i).atSite (line (v.field o) t) o) (fun i=> v.positive (a.leg i).plaq) (fun i=> slot_affine_limit (a.leg i) o v (hS _ (hp (stows o a (offset_inside _ o)))) (by omega)))
  have ht := (little_limit a (fun i t=>petals (line (v.field o) t) o (a.leg i).plaq) (fun i=> v.positive (a.leg i).plaq) (fun i=> petals_limit (a.leg i).plaq o hn v))
  have hh : Tendsto (fun t:ℝ=> ((baseLine o a-pollen o a) (line (v.field o) t))/t^2) (𝓝[≠] 0) (𝓝 0):= by
    have H:= he.sub ht; rw [sub_self] at H; simp_rw [Pi.sub_apply,sub_div]; exact H
  have he' := tendsto_nhds_unique (hessian_limit hG hx (show (baseLine o a-pollen o a) 1=0 by simp [baseLine,base_zero,pollen_zero]) _) hh
  linarith only [he']
end YM.Comparison.Density.Render
