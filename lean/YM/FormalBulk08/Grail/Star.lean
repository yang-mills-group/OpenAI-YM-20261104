import YM.FormalBulk08.Rial.Ivory

/-! Nonlinear graded Ward costs for source bearing vertices. Tap retains
ambient root, precision class remains weighted. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Grail
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge}{I V:Type*}{η σ A C : ℝ}{n r:ℕ}{W:Reach V}{x:V}

lemma penn_slice (p:V)(hA:η≤σ)(hp:0≤η) {T:Tile V (n+1)} (hv:Knoxville W σ x T A): Knoxville W η p (Lava.shed T p) (Real.exp (-(σ-η)*W.d p x)*A):= by
    refine ⟨mul_nonneg (Real.exp_pos _).le hv.1,?_⟩
    let f(v:chain V n):chain V (n+1):=Fin.cons p v
    have hh:Injective f := by intro i j he;simpa [f,Fin.cons_inj] using he
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]; refine le_trans ?_ (mul_le_mul_right ((ENNReal.tsum_comp_le_tsum_of_injective hh (penon W x σ T)).trans hv.2) _); rw [←ENNReal.tsum_mul_left]; apply ENNReal.tsum_le_tsum; intro v; unfold penon; rw [←mul_assoc]; refine mul_le_mul_left ?_ ‖Lava.shed T p v‖ₑ
    let H:=herb W x (f v)
    have he: herb W p v≤H:=known_wide W _ H fun i j=>reached W (Fin.cons x (f v):chain V (n+2)) i.succ j.succ
    have ht: W.d p x≤H:= reached W (Fin.cons x (f v)) (Fin.succ 0) 0
    unfold Gorge.shine; rw [←ENNReal.ofReal_mul (Real.exp_pos _).le, ←Real.exp_add]; refine ENNReal.ofReal_le_ofReal (Real.exp_monotone (?_ : η* _ ≤ -(σ-η)*_+σ*H));
    refine le_trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr he) hp) ?_
    nlinarith only [mul_le_mul_of_nonneg_left (show ((W.d p x:ℕ):ℝ)≤(H:ℝ) by exact_mod_cast ht) (sub_nonneg.mpr hA)]

lemma sew_wide (a:V)(v:chain V n): herb W x (Fin.cons a v) ≤ herb W a v + W.d a x:= by
    let Z:chain V (n+1):=Fin.cons a v
    apply known_wide; intro i j; cases i using Fin.cases with
    | zero=> cases j using Fin.cases with
             | zero=> rw [W.self]; omega
             | succ j=> simp only [Fin.cons_succ, Fin.cons_zero]; apply (W.tri x a (Z j)).trans; rw [W.turn x a]; have h:W.d a (Z j)≤herb W a v:= reached W Z 0 _; change W.d a x+ W.d a (Z j) ≤ _; omega
    | succ i=> cases j using Fin.cases with
               | zero=> simp only [Fin.cons_succ,Fin.cons_zero]; change W.d (Z i) x≤_; exact (W.tri _ a _).trans (Nat.add_le_add_right (reached W Z i 0) _)
               | succ j=> exact (reached W Z i j).trans (Nat.le_add_right ..)
lemma penn_pile (x:V)(hp:0≤η) (T:Tile V (n+1))(f: V→ℝ)(h:∀ a, Knoxville W η a (Lava.shed T a) (f a))(ht: (∑' a:V,Gorge.shine η (W.d a x) * ENNReal.ofReal (f a))≤ ENNReal.ofReal C)(hc:0≤C): Knoxville W η x T C:= by
    refine ⟨hc, le_trans ?_ ht⟩; rw [←Equiv.tsum_eq (Fin.consEquiv (fun _:Fin (n+1)=>V)), ENNReal.tsum_prod']; apply ENNReal.tsum_le_tsum;intro a
    refine le_trans ?_ (mul_le_mul_right (h a).2 _); rw [←ENNReal.tsum_mul_left]; refine ENNReal.tsum_le_tsum fun v=>?_; change Gorge.shine _ (herb W x (Fin.cons a v:chain V (n+1)))* _≤_;rw [←mul_assoc, mul_comm (Gorge.shine η (W.d a x))]; refine mul_le_mul_left ?_ ‖Lava.shed T a v‖ₑ
    rw [←shine_add]; exact shine_le η hp (sew_wide a v)
end YM.FormalBulk08.Grail
