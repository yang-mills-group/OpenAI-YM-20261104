import YM.WilsonCoeffUV.Thermo.Transfer
/-! Matrix tickets for the page tariffs. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08
open scoped Topology BigOperators
variable {n:Side}{U α β V ι : Type*}{k r:ℕ} {A B σ η : ℝ}
variable {d:Distance U}
abbrev ropes (U α β: Type*) := Matrix (U×α) (U×β) ℝ

def dragCup (d:Distance U)(σ A:ℝ)(P:ropes U α β): Prop:=0≤A ∧∀ x y,|P x y| ≤A*Real.exp (-σ*d.gap x.1 y.1)
lemma dragCup.mono {P:ropes U α β}(h:dragCup d σ A P)(he:η≤σ): dragCup d η A P:= ⟨h.1,fun x y=>(h.2 x y).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg he) (by positivity))) h.1)⟩
lemma dragCup.le {P:ropes U α β}(h:dragCup d σ A P)(he:A≤B): dragCup d σ B P:= ⟨h.1.trans he,fun x y=>(h.2 x y).trans (mul_le_mul_of_nonneg_right he (by positivity))⟩
lemma dragCup.add {P F:ropes U α β}(h:dragCup d σ A P)(e:dragCup d σ B F): dragCup d σ (A+B) (P+F):= ⟨add_nonneg h.1 e.1,fun x y=>(abs_add_le ..).trans ((add_le_add (h.2 x y) (e.2 x y)).trans_eq (by rw [add_mul]))⟩
lemma dragCup.zero : dragCup d σ 0 (0:ropes U α β):=by simp [dragCup]
lemma dragCup.one [DecidableEq α][DecidableEq U]: dragCup d σ 1 (1:ropes U α α):= ⟨zero_le_one, fun x y=> by rw [Matrix.one_apply]; split <;> rename_i he; simp [he,d.self]; simp only [abs_zero]; positivity⟩

def hauling [AddGroup U](P:ropes U α β): Prop := ∀ b:U, ∀ x y, P (jog b x) (jog b y)=P x y
structure Pilots (P:(n:Side)→ ropes (Site n) α β)(F:ropes Cover α β): Prop where
  point : ∀ x y,Tendsto (fun n=>P n (foldUnder n x) (foldUnder n y)) atTop (𝓝 (F x y))
  move : ∀ᶠ n in atTop, hauling (P n)
  fees : ∃ σ A:ℝ,0<σ ∧ ∀ᶠ n in atTop, dragCup (tor n) σ A (P n)

lemma Pilots.unique {P:(n:Side)→ ropes (Site n) α β}{F D:ropes Cover α β}(h:Pilots P F)(e:Pilots P D): F=D:= Matrix.ext fun x y=>tendsto_nhds_unique (h.point x y) (e.point x y)
lemma Pilots.one [DecidableEq α] : Pilots (fun n=> (1:ropes (Site n) α α)) 1:=by
  refine ⟨fun i j=>tendsto_const_nhds.congr' ?_, Eventually.of_forall fun n b x y=> by simp [Matrix.one_apply],1,1,one_pos, Eventually.of_forall fun _=>dragCup.one⟩
  filter_upwards [fold_faith i j] with n hn; simp [Matrix.one_apply,hn]

-- Row conversions, including summability budgets for pace alone.
def shuttleM (R:Row α β): ropes Cover α β:=fun i j=> R i.2 j.2 (j.1-i.1)
lemma matrix_width {P:Row α β}(h:P.strip σ A)(hp:0≤A) : dragCup terrain σ A (shuttleM P):=by
  refine ⟨hp,fun i j=>?_⟩
  rw [neg_mul,Real.exp_neg,←div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
  exact cap_pt (h i.2 j.2) (j.1-i.1)
lemma matrix_visit [Fintype β]{P:Row α β}(h:P.strip σ A)(hp:0<σ)(ha:0≤A): Pilots P.acts (shuttleM P):=by
  refine ⟨fun i j=>?_, ?_,σ,Fintype.card β*A,hp,Eventually.of_forall fun n=> ⟨mul_nonneg (by positivity) ha,fun i j=>?_⟩⟩
  · have hs : Tendsto (fun R:ℕ=> (Fintype.card β:ℝ)*(Real.exp (-σ*R)*A)) atTop (𝓝 0):= by
      have ht : Tendsto (fun R : ℕ => Real.exp (-σ*R)) atTop (𝓝 0):= Real.tendsto_exp_atBot.comp (by exact tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_lt_zero.mpr hp))
      simpa using (ht.mul_const A).const_mul (Fintype.card β:ℝ)
    refine Metric.tendsto_nhds.mpr fun ε hε=>?_; obtain ⟨R,hR,he⟩ := ((hs.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop (size (j.1-i.1)))).exists
    filter_upwards [eventually_ge_atTop (⟨2*R+1,Nat.zero_lt_succ _⟩ : Side)] with n hn
    change |P.acts n (foldUnder n i) (foldUnder n j) - P i.2 j.2 (j.1-i.1)| < ε
    have hw:= lift_comparison h hp.le (wrap n i.1) (j.1-i.1) i.2 j.2 R he (by exact hn)
    rw [map_sub, add_sub_cancel] at hw; exact hw.trans_lt hR
  · refine Eventually.of_forall (fun n b x y=> tsum_congr fun z=>?_)
    congr 1
    ext; simp [jog,add_assoc]
  rw [mul_comm]; exact (physical_rows h hp.le n).point i j

lemma drag_two {d:Distance U} (x : Fin 2→U×α) : soar d x=d.gap (x 0).1 (x 1).1:=by
  refine le_antisymm (league_le _ _ fun i j=>?_) (leg_le d (Prod.fst ∘ x) 0 1)
  fin_cases i<;>fin_cases j<;> simp [d.self,d.swap (x 1).1 (x 0).1]
lemma drag_orb {P:ropes U α α}(h:dragCup d σ A P): Amber d σ A (orbQ P):=by
  refine ⟨h.1,fun x=>?_⟩; rw [drag_two,orbQ,Real.norm_eq_abs, abs_div]; exact (div_le_self (by positivity) (by norm_num)).trans (h.2 _ _)
lemma Pilots.orb {P:(n:Side)→ ropes (Site n) α α}{F:ropes Cover α α}(h:Pilots P F): Yields (fun n=>orbQ (P n)) (orbQ F):=by
  have he n: dilute (fun n=>orbQ (P n)) n=orbQ (P n):= if_neg (by norm_num)
  obtain ⟨s,a,hp,H⟩ :=h.fees; refine ⟨fun x=>?_, h.move.mono (fun n hn b x=> congr_arg (·/2) (hn b _ _)),s,a,hp,H.mono (fun n hn=> by rw [he]; exact drag_orb hn)⟩
  simp_rw [he]; exact (h.point _ _).div_const _
end YM.WilsonCoeffUV.Bank
