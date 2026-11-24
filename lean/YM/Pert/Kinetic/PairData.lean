import YM.Pert.Kinetic.SlowMode
noncomputable section
namespace YM.Pert.Kinetic
open Function Filter Set Lattice Wilson Exterior RG Precision
open Work.F03
open scoped Topology BigOperators Classical ContDiff InnerProductSpace
variable {n : Side} {G : Gauge} {σ C Λ : ℝ}

def atomMinor (k : ℕ) (W : ℕ → Atom G k) (x : Site n) (d : PlaqAxes) (a : fieldDir G n 1):= faceCurl (x,d) a -- wrapper

def slotAt (S : Slot) (a : fieldDir G n 1) (x : Site n) (z' : Bool) := faceCurl (if z' then slotFace S x else (x,S.plaq)) a

def pair (W : PathData G) (a : fieldDir G n 1) (x : Site n) (c : Bool) (i : ℕ) := (W.loop i).poly fun j => slotAt ((W.loop i).leg j) a x c
lemma slot_bound {m : ℝ} {a : fieldDir G n 1} (h : Slow a m) (S : Slot) (b : Bool) (z : G.ColorIndex) (x : Site n) : |slotAt S a x b z| ≤ m := calc
     _ = |inner ℝ (EuclideanSpace.basisFun G.ColorIndex ℝ z) (slotAt S a x b)| := by simp only [EuclideanSpace.basisFun_inner]
     _ ≤ _ := (abs_real_inner_le_norm _ _).trans (by simpa only [OrthonormalBasis.norm_eq_one,one_mul] using! (show ‖slotAt S a x b‖ ≤ m from h.curl _))
variable {p : Clip} (W : PathData G) (hb : W.Bounds p σ C Λ)
include hb
-- private lemma paying_loop (i : ℕ) : Summable (W.loop_coeff ((W.loop i).leg |> fun f=> fun j => (f j).plaq) (fun _=>Classical.arbitrary _)) := (hb.loopTerms ..).1 -- remove
lemma steady_null {m:ℝ} (a : fieldDir G n 1) (h : Slow a m) (x : Site n) : (∑' i,pair W a x false i) = 0 := by
    unfold pair Atom.poly slotAt; dsimp only
    let v := fun b : PlaqAxes => faceCurl (x,b) a
    have he (k) (u:Fin 2→G.ColorIndex):∏ i:Fin 2, v (W.loop k |>.leg i|>.plaq) (u i) = ∏ i,faceCurl (x,(W.loop k).leg i|>.plaq) a (u i) := by rfl
    simp only [ite_false,Bool.false_eq_true]
    simp_rw [←he]
    let facePath := fun k i=>((W.loop k).leg i).plaq
    let test := fun (b : Fin 2→G.ColorIndex) (d : Fin 2→PlaqAxes) => ∏ i,v (d i) (b i)
    have eqv (b : Fin 2→G.ColorIndex) k : (W.loop k).coeff b * ∏ i, v ((W.loop k).leg i |>.plaq) (b i) = ∑ d:Fin 2→PlaqAxes,W.loop_coeff d b k*test b d := by
       dsimp only [PathData.loop_coeff]
       rw [Finset.sum_eq_single_of_mem (facePath k) (Finset.mem_univ _)]
       · simp [test,facePath]
       intro j _ hj; simp [Ne.symm hj,facePath]
    have he1(b d): Summable fun k=> W.loop_coeff d b k * test b d := (hb.loopTerms d b).1.mul_right (test b d)
    simp_rw [eqv]; rw [Summable.tsum_finsetSum (fun i _=> summable_sum fun b _=> he1 i b)]
    have hx (i:Fin 2→G.ColorIndex): (∑' k, ∑ j:Fin 2→PlaqAxes,(W.loop_coeff j i k * test i j)) = _ := Summable.tsum_finsetSum (fun j _=>he1 i j)
    simp only [hx]
    apply Finset.sum_eq_zero; intro d _; apply Finset.sum_eq_zero;intro i _
    rw [tsum_mul_right, (hb.loop_normal ..).1,zero_mul]
end YM.Pert.Kinetic
