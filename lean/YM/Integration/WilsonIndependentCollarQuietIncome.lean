import YM.Integration.WilsonIndependentCollarFirstStudent

/-! One positive-degree quiet vertex in either orientation of the actual
marked heat recursion, with its free and integrated legs paid on one torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarQuietIncome
open Finset Function Lattice Laurent Bloch Metric Precision RG Work.F08 Wilson FormalBulk08
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Winding
open WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open scoped Classical BigOperators
variable {n:Side} {α E : Type} [Fintype α] [NormedAddCommGroup E]

def salary (s:ℝ) (o:Site n) {r:ℕ} (F:Ten E (Co n α) r) :=
  ∑ x,Real.exp (s*tread (tor n) o x)*‖F x‖

theorem point (s:ℝ) (o:Site n) {r:ℕ} (F:Ten E (Co n α) r) :
    Cork (tor n) o s (salary s o F) F := by
  refine ⟨sum_nonneg fun x _=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _),fun x=>?_⟩
  have own : Real.exp (s*tread (tor n) o x)*‖F x‖ ≤ salary s o F :=
    single_le_sum (f:=fun y:dock (Site n) α r=>Real.exp (s*tread (tor n) o y)*‖F y‖)
      (fun y _=>mul_nonneg (Real.exp_pos _).le (norm_nonneg (F y))) (mem_univ x)
  rw [neg_mul,Real.exp_neg,←div_eq_mul_inv]
  exact (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using own)

theorem sum_root {s t A:ℝ} (o:Site n) {r:ℕ} {F:Ten E (Co n α) r}
    (held:Cork (tor n) o s A F) (gap:t<s) (nonnegative:0≤t) :
    salary t o F ≤ A*tiePay α r (s-t) := by
  cases r with
  | zero =>
    simpa [salary,tiePay,tread,league,stud,tor] using held.2 default
  | succ r =>
    let d:=tor n
    have one (x:dock (Site n) α (r+1)) :
        Real.exp (t*tread d o x)*‖F x‖ ≤ A*sail ((s-t)/(r+1:ℕ)) d o x := by
      let l:=tread d o x
      have attach (j:Fin (r+1)) : d.gap o (x j).1≤l := leg_le d (stud o x) 0 j.succ
      have cost := sail_cut (Nat.le_refl l) nonnegative gap (Nat.zero_lt_succ r) o x attach
      calc
        _ ≤ Real.exp (t*l)*(A*Real.exp (-s*l)) :=
          mul_le_mul_of_nonneg_left (held.2 x) (Real.exp_pos _).le
        _ ≤ Real.exp (t*l)*(A*(Real.exp (-t*l)*sail ((s-t)/(r+1:ℕ)) d o x)) := by
          gcongr
          exact held.1
        _ = _ := by rw [neg_mul,Real.exp_neg]; field_simp
    apply (sum_le_sum fun x _=>one x).trans
    rw [←mul_sum]
    exact mul_le_mul_of_nonneg_left (train_native (div_pos (sub_pos.mpr gap) (by positivity)) o (r+1)) held.1

variable [NormedSpace ℝ E]
theorem joined {s A B:ℝ} (pos:0<s) {C:ropes (Site n) α α} (wick:dragCup (tor n) s B C)
    (P:Gen ℝ (Co n α)) (F:Gen E (Co n α)) (o:Site n) (i j:ℕ)
    (quiet:Amber (tor n) s A (P (i+1))) :
    salary (s/2) o (wear (swivel (rill C P F (i+j) i j))) ≤
      ((sealM i j*B*A*salary s o (F (j+1))) * tiePay α 2 (s-3*s/4)) *
        tiePay α (i+j) (3*s/4-s/2) := by
  have h:=soloswivel_cup (solorill_bill wick quiet (point s o (F (j+1))) pos.le rfl)
  exact sum_root o (h.ledger (show 3*s/4<s by linarith) (by linarith)) (by linarith) (by linarith)

variable {G:Gauge} {ι:Type} [DecidableEq ι] {D k:ι→ℕ} {Z:Finset ι}
omit [Fintype α] [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem original (e hv qv i:ℕ) (paid:qv≤e) :
    ∃d:ℕ,∀I:Arch G,∃s A:ℝ,0<s ∧ s≤I.s ∧ 0≤A ∧ ∀p:PackOne Z D k e I,
    ∀(S:Finset ι) (ht qt j:ℕ) (o:Site p.V.n),
    let F:=p.surfU S ht qt
    let P:=p.V.vault hv qv
    let fare:=((sealM i j*I.mass*(A*p.V.coin^d)*salary s o (F (j+1))) *
      tiePay I.dial 2 (s-3*s/4))*tiePay I.dial (i+j) (3*s/4-s/2)
    salary (s/2) o (wear (swivel (rill p.N P F (i+j) i j))) ≤ fare ∧
      salary (s/2) o (wear (swivel (rill p.N.transpose P F (i+j) i j))) ≤ fare := by
  obtain ⟨d,H⟩:=Layered.snowLight G qv hv e (i+1) paid
  refine ⟨d,fun I=>?_⟩
  obtain ⟨t,A,pt,pa,old⟩:=H I
  let s:=min I.s t
  have sp:0<s:=lt_min I.h pt
  refine ⟨s,A,sp,min_le_left ..,pa,fun p S ht qt j o=>?_⟩
  have base:=((old p.V).mono (show s≤t from min_le_right ..)).aim
  have quiet:Amber (tor p.V.n) s (A*p.V.coin^d) (p.V.vault hv qv (i+1)) := by
    simpa only [pruce,Nat.succ_ne_zero,if_false] using base
  have cov:dragCup (tor p.V.n) s I.mass p.N := (p.V.rateRamp.mono (min_le_left ..)).bow
  refine ⟨joined sp cov _ _ o i j quiet,joined sp ?_ _ _ o i j quiet⟩
  refine ⟨cov.1,fun a b=>?_⟩
  rw [(tor p.V.n).swap a.1 b.1]
  exact cov.2 b a

end YM.Integration.WilsonIndependentCollarQuietIncome
