import YM.PertExtension.PositionBranch
import YM.PertExtension.Actual

/-!
# Slot recombination on a common physical field horizon

Here on the unselected hierarchy in asymptotically weak coordinates. Tested
scalar arrays, linear over the *same* fields. No precision improvement claimed
from the Maxwell limit.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 500000
namespace YM.PertExtension.Physical
open Set Filter Function Table Labels Extraction Climb Position Next.UVStress Ward
open MeasureTheory
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge}{C : Family G}{f : Order}{S : Table C.book}
variable {d : ℕ}{J : Type*}[Fintype J]

structure Profile where
  n : ℕ
  test : Test n

-- Continuous multilinear expansion before taking real entries.
lemma expansion {L : Register G}{T : Table L}{n : ℕ} (p:Fin n→J→ℂ)(b:J→T.Field d)(x : Points n) :
    T.classMoment T (fun _=>d) x (fun i=> ∑ j:J, p i j • b j) =
    ∑ j:Fin n→J,(T.classMoment T (fun _=>d) x (fun i=> b (j i)))*∏ i,p i (j i) := by
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro j hj; exact (MultilinearMap.map_smul_univ _ (fun i=>p i (j i)) (fun i=> b (j i))).trans (mul_comm ..)

def readingC {L : Register G} (T : Table L)(b : J→T.Field d) (r : ℝ) (q:Mark J Profile.n) :=
  q.1.test.applyTo (fun x=> T.useAt T (r • x) (fun i=>⟨d,b (q.2 i)⟩))
def reading {L : Register G} (T : Table L)(b : J→T.Field d) (r : ℝ) (q:Mark J Profile.n) :=
  (readingC T b r q).re

def columns {V : Type*} [AddCommMonoid V][Module ℂ V] (b : J→V) (k : FrameAt J ℝ) (i:J) : V :=
  ∑ j,(k i j:ℂ) • b j

lemma reading_columns {L : Register G} {T : Table L} (H : T.Smooth)(b:J→T.Field d) (r : ℝ) (hr:0<r) (k:FrameAt J ℝ) :
    reading T (columns b k) r=Position.insert J Profile.n (reading T b r) k := by
  funext q
  let B (j:Fin q.1.n→J) (x:Points q.1.n):= T.classMoment T (fun _=>d) (r • x) (fun i=>b (j i))
  have he (j : Fin q.1.n→J) : ContinuousOn (B j) (conf _) :=
    (smoothZoom H (fun i : Fin q.1.n=>⟨d,b (j i)⟩) hr).continuousOn
  have ht : (readingC T (columns b k) r q)=∑ w:Fin q.1.n→J, readingC T b r ⟨q.1,w⟩ * ∏ i,(k (q.snd i) (w i):ℂ):= by
    unfold readingC Test.applyTo
    let w (j : Fin q.1.n→J):= ∏ i,(k (q.2 i) (j i):ℂ)
    rw [show (fun x=> q.1.test x * T.useAt T (r • x) (fun i:Fin q.1.n=>⟨d,columns b k (q.snd i)⟩)) = fun x=>∑ j:Fin q.1.n→J, (q.1.test x*B j x) * w j from
      funext fun x=>by
        let p (i : Fin q.1.n)(k' : J) := (k (q.2 i) k':ℂ)
        rw [show T.useAt T _ (fun i:Fin q.1.n=>⟨d,columns b k (q.snd i)⟩) = ∑ j:Fin q.1.n→J, B j x * w j from
              expansion p b (r • x), Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; rw [←mul_assoc]]
    rw [integral_finsetSum _ (fun j _=>(q.1.test.smearing (he j)).mul_const (w j))]
    exact Finset.sum_congr rfl fun j _=>integral_mul_const (w j) _
  simp only [reading,ht,Position.insert, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _; rw [← Complex.ofReal_prod,Complex.mul_re];simp only [Complex.ofReal_re, Complex.ofReal_im,mul_zero,sub_zero]

variable {L : Register G}
/-- The free entries and symmetry source are independent of the actual kernels. -/
def free (b : J→(Bel L).Field d) := reading (Bel L) b 1
def onCurve (A : Actual C f S)(b:J→(Bel C.book).Field d)(k:ℕ):=
  reading S (fun i=>A.curve.U k d (b i)) (A.curve.r k)

lemma sampled (A : Actual C f S) (b : J→(Bel C.book).Field d)(q : Mark J Profile.n): Tendsto (fun k=>onCurve A b k q) atTop (𝓝 (free b q)) := by
  let z := fun i:Fin q.1.n=>(⟨d,b (q.2 i)⟩ : (Bel C.book).Tag)
  let g k := tested (A.curve.r k) (isoPanel A.curve k) z
  let t := q.fst.test
  have ht : ∀ k, onCurve A b k q=(t.applyTo (g k)).re:= fun _=>rfl
  have hc k : ContinuousOn (g k) (conf _) := (smoothZoom A.F.room.kernel.smooth _ (A.curve.positive k)).continuousOn
  have hd : ContinuousOn (disc z) (conf _) := (smoothDisc A.M.hT.smooth z).continuousOn
  have hv k : t.applyTo (g k)= t.applyTo ((g k)-(disc z))+t.applyTo (disc z) := by rw [test_sub _ _ (hc k) hd]; abel
  have hy : Tendsto (fun k=>t.applyTo ((g k)-(disc z))) atTop (𝓝 0) :=
       (A.approaches.values q.1.n z).at_test q.1.test
  have hx := hy.add_const (t.applyTo (disc z))
  simp_rw [ht,show free b q = (t.applyTo (disc z)).re by unfold free reading readingC; simp [t,z];rfl]
  exact Complex.continuous_re.continuousAt.tendsto.comp (by simpa only [hv,zero_add] using hx)

def check (A : Actual C f S)(b : J→(Bel C.book).Field d)
    (D : TestSystem J Profile Profile.n)(k:ℕ):=
  let p:D.Parameter:=onCurve A b k ∘ markIn D.tests
  columns (fun i=>A.curve.U k d (b i)) (D.baseline + (D.branch (free b) p).val)

variable (A : Actual C f S)(b : J→(Bel C.book).Field d)
    (D : TestSystem J Profile Profile.n)(h:D.Regular (free b))
private lemma sampled_system : Tendsto (fun k=>onCurve A b k ∘ markIn D.tests) atTop (𝓝 (free b ∘ markIn D.tests)) :=
  tendsto_pi_nhds.mpr fun q=>sampled A b (markIn D.tests q)
include h
private lemma sampled_pair : Tendsto (fun k=>
     (onCurve A b k ∘ markIn D.tests,D.branch (free b) (onCurve A b k ∘ markIn D.tests))) atTop
     (𝓝 (free b ∘ markIn D.tests,0)) := (D.tends (free b) h).comp (sampled_system A b D)

theorem sampled_normalization : ∀ᶠ k : ℕ in atTop,D.select (reading S (check A b D k) (A.curve.r k) ∘ markIn D.tests)=D.target := by
  filter_upwards [(sampled_system A b D).eventually (D.solves _ h)] with k hk
  unfold check;rw [reading_columns A.F.room.kernel.smooth _ _ (A.curve.positive k)]
  unfold TestSystem.lieResult onCurve at hk
  rw [D.result_eq] at hk; exact hk

theorem sampled_answer (q:Mark J Profile.n) :
    Tendsto (fun k:ℕ=> reading S (check A b D k) (A.curve.r k) q) atTop (𝓝 (Position.insert J Profile.n (free b) D.baseline q)) := by
  let k (i : ℕ) := (D.branch (free b) (onCurve A b i ∘ markIn D.tests)).val
  have hk : Tendsto k atTop (𝓝 (0:FrameAt J ℝ)) := D.Z.subtypeL.continuous.continuousAt.tendsto.comp (continuousAt_snd.tendsto.comp (sampled_pair A b D h))
  simp_rw [check,reading_columns A.F.room.kernel.smooth _ _ (A.curve.positive _)]
  have he : ∀ i j, Tendsto (fun m=> k m i j) atTop (𝓝 0) := fun i j=> tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hk i) j
  exact tendsto_finsetSum _ (fun (j:Fin q.1.n→J) _=>(sampled A b ⟨q.1,j⟩).mul
    (tendsto_finsetProd _ (fun i _=> by simpa [k] using ((he (q.2 i) (j i)).const_add _))))

end YM.PertExtension.Physical
