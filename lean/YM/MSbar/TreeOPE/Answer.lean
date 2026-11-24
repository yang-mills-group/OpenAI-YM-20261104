import YM.MSbar.TreeOPE.Output
import YM.MSbar.Tree.Series

/-!
# tree MS OPE asymptotics theorem

arbitrary homogeneous physical marks at cluster, p fixed external (arbitrary
weights and fixed positions). The output order `m` is the total weight cutoff,
not a relative power or tuning parameter. Carry to arbitrary `m`; no
separation hypothesis within the collision except fixed shape really in conf.
We deal with shape rays here, using pointwise positions and give power error
in the relative distance parameter. Not integrated across rays or uniform
up to a shape boundary.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.OPE
open Function Set Filter Asymptotics Analysis
open Maxwell Maxwell.Free Maxwell.Wick
open Finsupp Next.Rank.Normal
open scoped ContDiff Topology BigOperators Classical
variable {G : Gauge} {H m n : ℕ} {x : Points n} (hx:x∈conf n) {p : Fin n→ WickPol G}

abbrev markW (i : Mark G n):= scaleW i.2

def inside (x : Points n) (r : ℝ) (z : E4):= points fun i:Fin n=> z+r • x i
include hx in
lemma safe (z : E4) {r : ℝ} (hr: 0<r): inside x r z ∈ conf n := by
  rintro i j he; apply (show Injective x.ofLp from hx); apply smul_right_injective _ hr.ne'; exact add_left_cancel he
lemma contracts (z : E4) (y : Points m) (h : foreign (spotX z) y): ∀ᶠ r:ℝ in 𝓝 0, foreign (inside x r z) y:= by
  refine eventually_all.mpr fun i=> eventually_all.mpr fun j=>?_
  have hu : Continuous (fun r : ℝ=> inside x r z i):= by change Continuous (fun r:ℝ=> z+r • x i); fun_prop
  apply hu.continuousAt.eventually (isOpen_ne.mem_nhds ?_)
  change z+ (0:ℝ) • _≠ _; rw [zero_smul,add_zero]; exact h 0 j
private lemma wallpapers {d : Fin n→ℕ} (h : ∀ i,pureW scaleW (d i) (p i)) (r : ℂ) :
    scale markW r (pot Finset.univ p)= r^(∑ i,d i) • pot Finset.univ p:= by
  have ht (i : Fin n) : scale markW r (post i (p i))= r^(d i) • post i (p i):= by
    rw [← map_smul (post i), ← scaled_pure scaleW r (d i) (p i) (h i)];
    apply DFunLike.congr_fun (f:=(scale markW r).comp (post i)) (g:=(post i).comp (scale scaleW r)) (x:=p i); ext1 j
    rw [AlgHom.comp_apply,AlgHom.comp_apply, post_X,scaled, scaled,map_smul,post_X]
  unfold pot; rw [map_prod]; simp_rw [ht]; rw [Finset.prod_smul,Finset.prod_pow_eq_pow_sum]
lemma mark_frame {r : ℝ} (u v : Mark G n) (hr: 0<r) (z : E4):
    (scope (readW markW (r:ℂ)) (frameX (safe hx z hr))).cov u v=(frameX hx).cov u v:= by
  change linearCombination ℂ (linearCombination ℂ _ (Finsupp.single u _)) (Finsupp.single v _)=_
  rw [linearCombination_single,linearCombination_single]; unfold frameX; simp only [Pi.smul_apply]; split_ifs
  · simp
  rw [smul_eq_mul, smul_eq_mul,← mul_assoc,mul_comm ((r:ℂ)^ markW v),← pow_add]; exact lengths _ _ _ _ _ r ((show Injective x.ofLp from hx).ne (by assumption)) hr

lemma priced {r : ℝ} {d : Fin n→ℕ} (h : ∀ i,pureW scaleW (d i) (p i)) (hr:0<r) (z : E4) {y : Points m} (hy:y∈conf m) (hp : foreign (inside x r z) y) (v : Fin m→ WickPol G):
    (r:ℂ)^(∑ i,d i)*Tree.finitePart 1 (combo (inside x r z) y) (Fin.append p v)=
      mixed 0 (frameX hy) (changed (edges (inside x r z) y) (readW markW (r:ℂ))) (tube hx p) (pot Finset.univ v):= by
  rw [Tree.four 1 (combination (safe hx z hr) hy hp),wick_mixed _ _ (safe hx _ hr) hy hp]
  rw [← smul_eq_mul,← mixed_smul,← wallpapers h]; unfold scale; rw [mixed_lift];
  rw [show scope (readW markW (r:ℂ)) (frameX (G:=G) (safe hx z hr))=frameX hx from Symmetric.ext (funext fun i=>funext fun j=>mark_frame hx i j hr z)]
  apply splitCluster

lemma close_part (p : Fin n→ WickPol G) (q:Fin m→ WickPol G) (z : E4) {y : Points m} (hy:y∈conf m) (h : foreign (spotX z) y):
    Accords (𝓝 0) (fun r:ℝ=>r^(H+1))
       (fun r:ℝ=> mixed 0 (frameX hy) (changed (edges (inside x r z) y) (readW markW (r:ℂ))) (tube hx p) (pot Finset.univ q))
       (fun r:ℝ=> mixed 0 (frameX hy) (changed (external y z) (delivery x (r:ℂ) H)) (tube hx p) (pot Finset.univ q)):= by
  apply mixed_perturb; intro i j
  simp_rw [changed, readW, linearCombination_single, Pi.smul_apply, smul_eq_mul];
  have he (r : ℂ) : (linearCombination ℂ (external y z) (delivery x r H i)) j=linearCombination ℂ (fun w=>entry w j.2 z (y j.1)) (delivery x r H i):= by simp only [linearCombination_apply, Finsupp.sum,Finset.sum_apply, Pi.smul_apply, external]
  simp_rw [he]; exact leg_close _ _ _ _ (show z ≠ y j.1 from h 0 _)

lemma linear_estimate (p : Fin n→ WickPol G) (L : WickPol G→ₗ[ℂ]ℂ) (m):
  (fun r:ℝ=> L (send x m (r:ℂ) (tube hx p)) - ∑ i∈Finset.range (m+1), (r:ℂ)^i * L (glued hx p i)) =O[𝓝 0] (fun r=>r^(m+1)):= by
  simp_rw [← gave _ p hx L m, ← lowered (Complex.ofReal _)]; simp only [approximant,map_sum,map_smul,smul_eq_mul]; exact slabAsymp scaleW (send x m 1 (tube hx p)) L m

/-- Normalized OPE budget. Includes the power multiplying the cluster,
so omitted powers are paid starting with `H+1` on the RHS.
-/
theorem remainder {d : Fin n→ℕ} (h : ∀ i,pureW scaleW (d i) (p i)) (z : E4) {y : Points m} (hy:y∈conf m) (ht : foreign (spotX z) y) (q : Fin m→ WickPol G) (H : ℕ):
    (fun r : ℝ=> (r:ℂ) ^(∑ i,d i)*Tree.finitePart 1 (combo (inside x r z) y) (Fin.append p q)-
        (∑ i∈Finset.range (H+1),(r:ℂ)^i*Tree.finitePart 1 (combo (spotX z) y) (Fin.append (solo (glued hx p i)) q))) =O[𝓝[>] 0] (fun r:ℝ=> r^(H+1)):= by
  let K:=external (G:=G) y z; let L:= depend 0 (frameX hy) K (pot Finset.univ q); let T(r:ℝ) := delivery (G:=G) x (r:ℂ) H
  have he(r:ℝ): mixed 0 (frameX hy) (changed (external y z) (T r)) (tube hx p) (pot Finset.univ q)= L (send x H (r:ℂ) (tube hx p)):= by unfold L; symm; exact (mixed_lift 0 (frameX hy) K (T r) (tube hx p) _).trans (by rw [scope_nil])
  simp_rw [Tree.four (G:=G) 1 (combination (sole z) hy ht), combined_single _ _ z hy ht]
  apply (((close_part (H:=H) hx p q z hy ht).differs.add (linear_estimate hx p L H)).mono nhdsWithin_le_nhds).congr' _ (EventuallyEq.refl _ _)
  filter_upwards [(contracts (x:=x) z y ht).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with r hr hv
  rw [priced hx h hv z hy hr, show _= L _ from he r]; unfold L K; ring
end YM.MSbar.OPE
