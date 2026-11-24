import YM.FormalBulk08.Mesa.Sash

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Mesa
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Series Jets PowerSeries
open scoped Topology ENNReal BigOperators Classical ContDiff
variable {r : ℕ} {I V : Type*} {C : Type*} [AddCommGroup C] [Fintype V]
lemma paste_grade (f : Rays V → ℝ) (r : ℕ) : (coeff r (paste f)).IsHomogeneous r := by
   rw [paste_coeff,laden]; let A:= iteratedFDeriv ℝ r f 0
   change MvPolynomial.IsHomogeneous ((r.factorial:ℝ)⁻¹ • facade r (fun v=>A (dotI ∘ v))) r
   rw [←map_smul]; apply facade_grade

lemma folds_byte [Fintype I] (p : V→I) (f : Rays V → ℝ) (h : ContDiffAt ℝ ∞ f 0) : paste (fun v:Rays I => f (v ∘ p))=PowerSeries.map (MvPolynomial.rename p).toRingHom (paste f) := by
   rw [←fit_translate,← paste_steps f (fun v:Rays I=>v ∘ p) h (contDiffAt_pi.mpr fun _=>contDiffAt_apply ..) rfl];rfl
omit [AddCommGroup C] in
lemma cores_here [Fintype C] [Fintype I] (x : V→C×I) (T : Tile V r) (b : chain (C×I) r) : cores x T b=∑ j,if x ∘ j=b then T j else 0 := by
   rw [core_sum,← tsum_fintype (L:=.unconditional _) (fun j=> if x ∘ j=b then T j else 0)] -- sense replace
   let U := {j:chain V r | x ∘ j=b};change (∑' j:U,T j.val) = _; rw [tsum_subtype]; exact tsum_congr fun j=>by simp [U,Set.indicator]
lemma deploy_fee [Fintype C] [Fintype I] (R : V→ C × I) (p : TypeR V) (i : Fin r) : marble r (∑ x:C, MvPolynomial.rename (tint x ∘ R) p)=deploy R (marble r p) := by
   rw [←canyon_eq,map_sum];simp_rw [canyon_eq,pebble]; funext v; simp_rw [deploy,Finset.sum_apply,cores_here];rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
   by_cases h : Pendant (R ∘ j) v
   · let b:= (v i).1-(R (j i)).1
     have he := (pendant_iff _ v i).mp h;rw [Finset.sum_eq_single b];
     · exact (if_pos he.symm).trans (if_pos h).symm
     · intro c _ hc; refine if_neg fun e=> hc ?_
       have ht:= congr_arg Prod.fst (congr_fun e i); simp only [Function.comp_apply,tint_fst] at ht;unfold b; rw [←ht]; simp
     simp
   rw [Finset.sum_eq_zero (fun a _=>if_neg (fun e=> h ⟨a,e.symm⟩))]; exact (if_neg h).symm

-- Template shape per degree
def schedules (p : Pap V) (R : V→ Biglot I) (n : Side): Pap (Tor n I):=
    ∑ x:Site n,PowerSeries.map (MvPolynomial.rename (tint x ∘ drip n ∘ R)).toRingHom p
lemma packet_schedules [Fintype I] (p : Pap V) (R : V→Biglot I) (n : Side) (i: Fin r) (e : ℕ) : rancho (schedules p R n) e r=cum i n (deploy R (rancho p e r)) := by
   unfold schedules rancho; rw [map_sum,deploy_fold]; simp_rw [coeff_map]; exact deploy_fee (drip n ∘ R) (coeff e p) i
end YM.FormalBulk08.Mesa
