import YM.RG03.Transports

/-! Genuine LEFT link derivative costs through cube-Bianchi and path-alignment identities, using
  the `Next.Scheduling.Wages` ordered path budget; direction polynomials and expansion of true supports explicit. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG03
open Wilson RG Lattice Next.Scheduling.Wages Work.G07
open scoped ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : BudgetPoint) (o : Site n) (X : Support n)


def Pays (f: Config G n → E) (c:ℝ) := LeftBound P.order (BudgetPoint.dirBound (G:=G) P o) (Healthy P.threshold X) 1 c f

namespace Pays
variable {P o X} {f g : Config G n → E} {b c : ℝ}
lemma budget (h:Pays P o X f b) : P.supBounds o X f b := ⟨h.nonneg,fun v hv l hl ha=>by simpa using h.bound l hl ha v hv⟩
lemma add (h:Pays P o X f b) (h':Pays P o X g c) : Pays P o X (fun v=>f v+g v) (b+c) := LeftBound.add h h'
lemma more (h : Pays P o X f b) (he:b≤c) : Pays P o X f c := ⟨h.smooth,h.nonneg.trans he, by
  exact fun _ hl hw U hu=> by simpa using ((h.budget.2 U hu _ hl hw).trans he)
  ⟩
lemma neg (h:Pays P o X f b) : Pays P o X (fun v=> - f v) b := by
  have hh := LeftBound.postcomp h (-ContinuousLinearMap.id ℝ E)
  exact Pays.more (f:=fun v=> -f v) hh ((mul_le_mul_of_nonneg_right (by rw [norm_neg]; exact ContinuousLinearMap.norm_id_le) h.nonneg).trans_eq (one_mul _))
lemma sub (h:Pays P o X f b) (h':Pays P o X g c) : Pays P o X (fun v=>f v-g v) (b+c) := by
  simp_rw [sub_eq_add_neg]; exact h.add (Pays.neg h')
lemma mul {A:Type*}[NormedRing A][NormedAlgebra ℝ A]{f g:Config G n→A} (h:Pays P o X f b) (h':Pays P o X g c) : Pays P o X (fun v=>f v*g v) ((2:ℝ)^P.order*b*c) := LeftBound.mul h h' zero_le_one
end Pays

private lemma one_step (x:Site n) (a : Step) : separation x (x+a.vec) ≤ 1 := by
  rw [separation_comm,separation, add_comm, add_sub_cancel_right, Step.vec]; split
  · rw [pdist_neg]; exact pdist_step _
  exact pdist_step _

private lemma count_links (x:Site n) (w:Walk) : let l:=Path.tissue (G:=G) x w
    Path.price l=1 ∧ (Path.uses l).length=w.length ∧ ∀ i∈Path.uses l, separation x i.1 ≤ w.length := by
  dsimp only
  induction w generalizing x with
  | nil => simp [Path.tissue,Path.price,Path.uses]
  | cons a w ih =>
    obtain ⟨h,h',hh⟩:=ih (x+a.vec)
    have hx : (Path.single (G:=G) x a).size=1 ∧ (Path.single (G:=G) x a).links = [a.used x] := by
      unfold Path.single; split <;> constructor <;> rfl
    simp_rw [Path.tissue,Path.price,Path.uses,hx.1,hx.2,List.singleton_append,List.length_cons,h,h',one_mul]
    refine ⟨trivial,trivial,fun i hi=>?_⟩
    rcases List.mem_cons.mp hi with ha|hmem
    · rw [ha]; unfold Step.used; split
      · rename_i hneg
        apply le_trans (b:=1) _ (by omega); rw [sub_eq_add_neg]
        simpa [Step.vec,hneg] using one_step x a
      change separation x x ≤ _; simp
    refine (separation_triangle x (x+a.vec) i.1).trans ?_
    have := hh i hmem; have := one_step x a; omega

/-- Cost at a common anchor including the path length and the derivative power order. No support
weight charged yet (below `EBound` uses per-occurrence cover exponent). -/
def defectCost (G:Gauge) (P:BudgetPoint)(l:ℕ) :=
  ((1+G.colorScale)+‖(1:G.Mat)‖) * ((1+G.colorScale)*((1:ℝ)+l)^(P.power+1))^P.order
lemma defectCost_ge (G:Gauge) (P:BudgetPoint)(l:ℕ) : 1 ≤ defectCost G P l := by
  have hg:=G.colorScale_pos
  apply one_le_mul_of_one_le_of_one_le (by linarith [norm_nonneg (1:G.Mat)])
  exact one_le_pow₀ (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by simp)))

lemma nonempty_defect (w:Circuit) {l:ℕ} (hl:w.path.length ≤ l) (L:List (Directions G n))
    (hL:L.length ≤ P.order) (hN:L.length≠0) (ht:∀ i∈L, P.dirBound o i) (U:Config G n) :
    ‖leftDerivs (w.defect o) L U‖ ≤ defectCost G P l * P.threshold := by
  let p:=Path.tissue (G:=G) o w.path
  have he : w.defect o = fun v=> (Path.eval p v) + (-1:G.Mat) := by
    funext v; rw [Circuit.defect,Circuit.raw,Circuit.holonomy,Path.picture,sub_eq_add_neg]
  have hc := (LeftBound.const (r:=(1:ℝ)) (D:=fun _:Directions G n=>True) (Z:=fun _=>True) zero_le_one (-1:G.Mat)).smooth (k:=P.order)
  have hg : L ≠ [] := by rintro rfl; exact hN rfl
  simp_rw [he,left_add (Path.soft p P.order) hc hL,left_const,if_neg hg,add_zero]
  obtain ⟨h1, hlen, hx⟩ := count_links (G:=G) o w.path
  let T := G.colorScale*P.threshold*(1+l)^P.power
  let N := (1+G.colorScale)*(1+(l:ℝ))^(P.power+1)
  have hG:=G.colorScale_pos; have hP:=P.threshold_pos
  have hb := Path.bill p T (show 0≤T from by unfold T; positivity) U L fun i hi A ha=>?_ 
  rotate_left
  · have hx' := (hx i hi).trans hl
    rw [separation_comm o] at hx'
    rw [Gauge.colorMat_norm]; refine (mul_le_mul_of_nonneg_left (ht A ha i) hG.le).trans ?_
    unfold T; rw [mul_assoc]; gcongr
  apply hb.trans
  rw [show Path.price p=1 from h1,one_mul,show (Path.uses p).length=w.path.length from hlen]
  have ha : T*w.path.length ≤ N*P.threshold := by
    unfold T N; rw [pow_succ]; exact (show G.colorScale*P.threshold*(1+l)^P.power*(w.path.length:ℝ) ≤
      (1+G.colorScale)*P.threshold*(1+(l:ℝ))^P.power*(1+l) from by gcongr <;> (first | linarith | (apply le_trans (b:=(l:ℝ)) _ (by linarith); exact_mod_cast hl))) |>.trans_eq (by ring)
  have hcP : P.threshold^L.length ≤ P.threshold := by
    have hi : 1 ≤ L.length := Nat.one_le_iff_ne_zero.mpr hN
    simpa only [pow_one] using pow_le_pow_of_le_one hP.le P.threshold_le hi
  have hN' : 1 ≤ N := one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by simp))
  calc _ ≤ ‖(1:G.Mat)‖*(N*P.threshold)^L.length := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ha L.length) (norm_nonneg _)
       _ = ‖(1:G.Mat)‖*N^L.length*P.threshold^L.length := by rw [mul_pow,mul_assoc]
       _ ≤ ‖(1:G.Mat)‖*N^P.order*P.threshold^L.length := by gcongr
       _ ≤ defectCost G P l*P.threshold := by unfold defectCost; gcongr; linarith

lemma defect_pay (w:Circuit) {l:ℕ} (hl:w.path.length ≤ l) (hs:w.supply o X) :
    Pays P o X (w.defect (G:=G) o) (defectCost G P l * P.threshold) := by
  let y := defectCost G P l
  have hy : 1≤y := defectCost_ge ..
  have hP := P.threshold_pos
  have hdiff : LeftSmooth P.order (w.defect (G:=G) o) := by
    rw [show w.defect (G:=G) o = fun v=>Path.eval (Path.tissue o w.path) v+(-1:G.Mat) from funext fun v=>by rw [Circuit.defect,Circuit.raw,Circuit.holonomy,Path.picture,sub_eq_add_neg]]
    exact (Path.soft _ _).add ((LeftBound.const (r:=(1:ℝ)) (D:=fun _:Directions G n=>True) (Z:=fun _=>True) zero_le_one (-1:G.Mat)).smooth)
  refine ⟨hdiff,mul_nonneg (zero_le_one.trans hy) hP.le,?_⟩
  intro L hL hD U hu
  simp only [one_pow,mul_one]; change _ ≤ y*_
  obtain he|hne := eq_or_ne L []
  · subst L; apply (w.defect_small _ hP.le _ _ hs hu).trans
    rw [mul_comm]
    have hn : 1 ≤ (1+G.colorScale)*(1+(l:ℝ))^(P.power+1) :=
      one_le_mul_of_one_le_of_one_le (by linarith [G.colorScale_pos]) (one_le_pow₀ (by simp))
    have : G.colorScale*1 ≤ y := mul_le_mul (by linarith [norm_nonneg (1:G.Mat)]) (one_le_pow₀ hn) zero_le_one (by linarith [norm_nonneg (1:G.Mat),G.colorScale_pos])
    apply mul_le_mul_of_nonneg_right (by simpa using this) hP.le
  · exact nonempty_defect P o w hl L hL (by simpa) hD U
end YM.RG03
