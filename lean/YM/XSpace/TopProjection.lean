import YM.XSpace.Stencils
import YM.XSpace.JetInterchange
import YM.Next.RANK.Inks
/-!
# Uncontracted readout for the *exact* top-stencil choices

To prove the equality on offshell Snap through all engineering weights (even
for the own-horizon convention this is needed before estimating errors), use
two-variable calculus. One variable for physical radial tests, one counts slots
by linearization before any filtration projection. Their Taylor jets commute.
`Projects` holds for all Snap, including after arbitrary pregauged scaling. No
assumption that a calibrated kernel can discard power-growing terms here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace
open Function Set Filter MeasureTheory Lattice Wilson Source Source.Drops
open Next.Foundations Next.Rank Gauss Formal Next.Rank.Normal LiftMark Beamer Spindle MvPolynomial
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators ContDiff Classical
variable {G : Gauge} {d : ℕ}

private lemma recurP {S : poly (Configuration.KeyIn G d)} (p : poly (Configuration.KeyIn G d)) (h : ∀ A:Snap G d, aeval (kp d A) p=aeval (kp d A) S) : p=S := by
  apply audible; intro x
  obtain ⟨A,H⟩:= kp_contains x; specialize h A; rw [H] at h; exact h

def off (G : Gauge) (d : ℕ) := Normal.exchange (ink d (id : AKey G→_))
def Pi0 (G : Gauge) (d : ℕ) : poly (AKey G) →ₗ[ℂ] poly (Configuration.KeyIn G d) :=
  (LiftMark.level (key G d) d).comp (off G d).toLinearMap

lemma off_X (k : AKey G) (A : Snap G d) : aeval (kp d A) (off G d (X k)) =
    ↑(oneGlow d A (k.1,k.2.1) k.2.2) := by
  unfold off; rw [Normal.exchange_x]; simp only [ink,Normal.glyph,map_sum,Finsupp.linearCombination_single,map_smul,aeval_X]
  rw [traffic,Complex.ofReal_sum]; apply Finset.sum_congr rfl; intro j _; rw [Complex.ofReal_mul,kp_real]; exact mul_comm ..

lemma Pi0_read (p : poly (AKey G)) (A : Snap G d) :
    aeval (kp d A) (Pi0 G d p)=Spindle.evaluate_ray (fun t => aeval (kp d (flash A t)) (off G d p)) d :=
  (ray_stamp ..).symm

namespace Words
variable {i : Index G d} (s : Words i)

abbrev sites := Fin s.n × G.ColorIndex

def keymark (j : s.sites) (A : Snap G d) := (↑(takes (hol G) d (s.slots j.1) A j.2):ℂ)
lemma paidSnap : Peg (hol G) d := Work.G02.answer Work.G01.answer ..
lemma keyDiff (j : s.sites) : ContDiffAt ℝ ⊤ (s.keymark j) 0 := Complex.ofRealCLM.contDiff.contDiffAt.comp (f:=fun A : Snap G d => takes _ _ _ A j.2) _
  ((EuclideanSpace.proj (𝕜:=ℝ) j.2).contDiff.contDiffAt.comp _ (((show Peg (hol G) d from paidSnap).shot _).contDiffAt))
private def b := Module.finBasis ℝ (Snap G d)
lemma key_zero (j : s.sites) : PowerSeries.coeff 0 (JetC (b (G:=G) (d:=d)) (s.keymark j))=0 := by rw [Formal.jet_zero (b (G:=G) (d:=d))]; simp [keymark,takes_zero]

lemma spine_born (j : s.sites) (A : Snap G d) : Formal.test (b (G:=G) (d:=d)) A (PowerSeries.coeff 1 (JetC (b (G:=G) (d:=d)) (s.keymark j))) = aeval (kp d A) (off G d (X (locus (s.slots j.1) j.2))) := by
  let S:=s.slots j.1
  rw [off_X, jet_ray (b (G:=G) (d:=d)) _ _ ((s.keyDiff j).of_le le_top)]
  simp only [Nat.factorial_one,Nat.cast_one, inv_one,one_mul, iteratedDeriv_one]
  have hx:Peg (hol G) d:=paidSnap
  have hd:= (Push.side (takes (hol G) d S) ((hx.shot S).differentiableAt) A)
  change HasDerivAt _ (Blurb (hol G) d S A) _ at hd
  rw [hx.initial] at hd
  have hm:= Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 ((EuclideanSpace.proj (𝕜:=ℝ) j.2).hasFDerivAt.comp_hasDerivAt 0 hd)
  exact hm.deriv

def model := combine s.keymark s.pose
lemma model_live : ContDiffAt ℝ ⊤ s.model 0 := lush s.keymark s.keyDiff s.pose

def essays (G : Gauge) (d : ℕ) := b (G:=G) (d:=d)
lemma brick : PowerSeries.coeff ((Frame G d).grades i).2 (JetC (b (G:=G) (d:=d)) s.model)=
   MvPolynomial.eval₂Hom MvPolynomial.C (fun j => PowerSeries.coeff 1 (JetC (b (G:=G) (d:=d)) (s.keymark j))) (homogeneousPart' s.pose ((Frame G d).grades i).2) := by
  unfold model
  rw [jet_combine (b (G:=G) (d:=d)) s.keymark s.keyDiff]
  exact pull_read' _ _ s.key_zero _ _ (show ∀ _, _ from s.starts)
lemma model_coeff (A : Snap G d) :
    let l:= ((Frame G d).grades i).2
    Formal.test (b (G:=G) (d:=d)) A (PowerSeries.coeff l (JetC (b (G:=G) (d:=d)) s.model))= aeval (kp d A) (off G d (ground s)) := by
  dsimp only []; rw [s.brick]; unfold ground
  let f (j : s.sites) := PowerSeries.coeff 1 (JetC (b (G:=G) (d:=d)) (s.keymark j))
  let g (j:s.sites):= locus (s.slots j.1) j.2
  let M := homogeneousPart' s.pose ((Frame G d).grades i).2
  have hh : (Formal.test (b (G:=G) (d:=d)) A).comp (aeval f)=(aeval (kp d A)).comp ((off G d).comp (rename g)):= by
    ext1 j; simp only [AlgHom.comp_apply, aeval_X, rename_X]; exact s.spine_born j A
  exact DFunLike.congr_fun hh M

lemma free_letter (u : ℝ) (A : Labels.Jet G) : Labels.read (u • A) ((Frame G d).basis i).val =
    u^((Frame G d).grades i).2 • Labels.read A ((Frame G d).basis i).val := by
  let P := ((Frame G d).basis i).val
  have he (k : Labels.Key G) : Labels.coord (u • A) k = (u:ℂ) * Labels.coord A k := by simp [Labels.coord]
  unfold Labels.read; rw [show ((Frame G d).basis i).val=_ from P.as_sum,map_sum,map_sum,Finset.smul_sum]; refine Finset.sum_congr rfl fun v hv=>?_
  have hh : Finsupp.weight Labels.bidegree v=(Frame G d).grades i := (Labels.pure_grade ..).1 ((Frame G d).pure _) (mem_support_iff.mp hv)
  rw [Labels.weight_slot] at hh
  rw [MvPolynomial.monomial_eq, map_mul (MvPolynomial.aeval _),map_mul (MvPolynomial.aeval _)]
  simp only [Finsupp.prod, Finsupp.sum] at *
  simp only [map_prod,map_pow,aeval_X,aeval_C,he,mul_pow, Finset.prod_mul_distrib, Complex.real_smul,smul_eq_mul,Complex.ofReal_pow]; rw [Finset.prod_pow_eq_pow_sum,show (((Frame G d).grades i).2)=_ from Eq.symm (congr_arg Prod.snd hh)]; ring

lemma dual_pass (A : Snap G d) (t : ℝ) :
    (authors G d).evaluate (Pi.single i 1) ((hol G).links d (expand d A) t)= s.model (flash A t) := by
  rw [s.past,Drops.scales (hol G)]; rfl

def both (A : Snap G d) (x : ℝ × ℝ) := s.model (x.1 • flash A x.2)
def ideal (i : Index G d) (A : Snap G d) (u : ℝ) := aeval (kp d (flash A u)) (Configuration.thawKey ((Frame G d).basis i))

lemma first_pass (A : Snap G d) (j : ℕ) (h : j≤d) (u : ℝ) :
    iteratedDeriv j (fun t : ℝ=> s.both A (u,t)) 0 = u^((Frame G d).grades i).2 • iteratedDeriv j (ideal i A) 0 := by
  let X : Snap G d:=u • A
  have hp : Projects (hol G) ((Frame G d).basis i) ((authors G d).evaluate (Pi.single i 1)) := by
    convert (Next.Foundations.sound G d).projects (Pi.single i 1)
    rw [← (Frame G d).coords_basis,(Frame G d).coords.symm_apply_apply]
  have he:= (hp (expand d X)).2.2 j h
  rw [show (fun t=>s.both A (u,t))=_ from (show (fun t=>s.both A (u,t))=(fun t=> (authors G d).evaluate (Pi.single i 1) ((hol G).links d (expand d X) t)) from _root_.funext fun t=> by rw [s.dual_pass,show flash X t=u • flash A t from flash_smul ..]; rfl),he]
  have hP (t : ℝ) : Labels.read (Source.scaleJet (expand d X) t) ((Frame G d).basis i).val = u^((Frame G d).grades i).2 • ideal i A t := by
    have ht : Source.scaleJet (expand d X) t=u • Source.scaleJet (expand d A) t := by
      unfold Source.scaleJet expand X; ext1 k; by_cases hh : k<d-1 <;> simp [hh, Pi.smul_apply]; exact smul_comm ..
    rw [ht,free_letter, Spindle.rewrites]; rfl
  rw [show (fun t=>Labels.read _ ((Frame G d).basis i).val) = (u^((Frame G d).grades i).2) • ideal i A from _root_.funext hP, iteratedDeriv_const_smul]; exact (okAt A (Configuration.thawKey ((Frame G d).basis i))).of_le (by exact_mod_cast h)

lemma wise (A : Snap G d) : ContDiffAt ℝ ω (s.both A) (0,0) := by
  unfold both
  apply (show ContDiffAt ℝ ω s.model ((0:ℝ) • flash A 0) from by simpa using s.model_live).comp (0,0)
  unfold flash Drops.trunk scaleJet; apply contDiffAt_pi.mpr; intro j; change ContDiffAt ℝ ω (fun x:ℝ×ℝ=> x.1 • (x.2^_ • (expand d A j.val))) _; let L:=ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (expand d A j.val)
  simp_rw [smul_smul]; have hh : ContDiff ℝ ω L := by apply ContinuousLinearMap.contDiff; exacts []
  exact hh.contDiffAt.comp _ (contDiffAt_fst.mul (contDiffAt_snd.pow _))

lemma output (A : Snap G d) (j : ℕ) (h : j≤d) :
    iteratedDeriv j (fun t : ℝ => aeval (kp d (flash A t)) (off G d (ground s))) 0=iteratedDeriv j (ideal i A) 0 := by
  let k:=((Frame G d).grades i).2; let w:= Spindle.okAt A (off G d (ground s)); let c : ℝ:=k.factorial
  have he (t : ℝ) := s.model_coeff (flash A t)
  have hv (t : ℝ) : c • (aeval (kp d (flash A t)) (off G d (ground s)))=iteratedDeriv k (fun u=> s.both A (u,t)) 0:= by
    rw [← he t]; change c • (Formal.test (b (G:=G) (d:=d)) _ (PowerSeries.coeff k (JetC (b (G:=G) (d:=d)) s.model)))=_; rw [jet_ray (b (G:=G) (d:=d)) s.model k (s.model_live.of_le le_top),Complex.real_smul]; change ((c:ℝ):ℂ) * (_ * _)= _; unfold c
    rw [Complex.ofReal_natCast,← mul_assoc,mul_inv_cancel₀,one_mul]; rfl; exact_mod_cast Nat.factorial_ne_zero k
  apply smul_right_injective _ (show c≠0 from Nat.cast_ne_zero.mpr k.factorial_ne_zero)
  change c • iteratedDeriv j _ (0:ℝ)= _
  rw [← iteratedDeriv_const_smul ((Spindle.okAt A (off G d (ground s))).of_le (show (↑j:WithTop ℕ∞) ≤ d from Nat.cast_le.mpr h)) c, show c • (fun t : ℝ => aeval (kp d (flash A t)) (off G d (ground s)))=_ from _root_.funext hv,← Formal.swap (s.wise A)] -- inspect
  rw [show (fun u : ℝ=>iteratedDeriv j (fun v=> s.both A (u,v)) 0)=_ from (_root_.funext (s.first_pass A j h)), iteratedDeriv_smul_const (show ContDiffAt ℝ _ (fun x : ℝ=>x^k) _ by fun_prop),iteratedDeriv_fun_pow_zero]; simp [c,k]

end Words

lemma pi_leading (i : Index G d) (s : Words i) : Pi0 G d (ground s)=Configuration.thawKey ((Frame G d).basis i) := by
  apply recurP; intro A
  rw [Pi0_read]; rw [← circle ((Frame G d).basis i),← ray_stamp]
  unfold evaluate_ray; refine Finset.sum_congr rfl fun j hj=> ?_
  rw [s.output A j (by simpa using hj)]; rfl
end YM.XSpace
