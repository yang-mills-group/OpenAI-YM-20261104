import YM.MS.Rake.Post
/-!
# Raw entity budgets. Dimension direction and univ windows
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rake
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook Train Logarithm Emit Pearl Dock Shine Hem Mell
open scoped Topology ContDiff Interval
variable {I E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {G:Gauge}{S:Scale I}{F: Flats G}
  {x:I→ℝ}{R T p ε:ℝ}{v:ℤ}{n d:ℕ}{b:Bool}
lemma cult (_hx:R≥0) (a:ℤ): ∃ C:ℝ,0<C∧∀ t:ℝ,‖t‖≤R → exp t^a ≤ C := by
    refine ⟨exp (R*|(a:ℝ)|),Real.exp_pos _,fun t ht=>?_⟩; rw [a_e]; apply exp_monotone; apply le_trans (le_abs_self _); rw [abs_mul]; gcongr; exact ht
lemma nameD_warm (h: Host F n): Warm (nameR ( four n F ) x) b:= by
    constructor
    · intro i t ht E _ _ w hw hb; let K:= CK t; let S: Scale (camp t) :={length:= fun x=> Real.exp (tstart x), pos:= fun x=>exp_pos _,basic:=fun _=>1+‖x i‖+t,one_le:=fun _=>(by linarith [norm_nonneg (x i)])}; let T:= Job.single (camp t);
      have h':Bus T S id:= by refine ⟨⟨(1+‖x i‖+t),(by linarith [norm_nonneg (x i)]),0,fun i=>by simp; rfl⟩,Real.exp t,exp_pos t,fun i=>?_⟩; change Real.exp _≤_ * 1; rw [mul_one]; exact raise_here i -- `simp` too much
      have hD := nameD (S:=S) (a:= tstart) (η:=fun _=> x i) h (fun _=>rfl) (fun k:camp t=> (norm_add_le ..).trans ( by have hs:=htT k; change _≤ 1 + _ + _; linarith )) E w hw hb; let p:= pitch w-(n:ℤ); obtain ⟨C,hC,hpc⟩:= cult ht p;
      apply Job.ticket (P:=id) h' hD ?_ ( pos_nn _ ( fun i=>zero_le_one ) _ ); refine ⟨_,hC,0,fun i=>?_⟩; simp only [ id_eq, Function.comp_apply, pow_zero, cw,one_zpow,mul_one, ← zpow_add₀ (S.pos i).ne' ]; exact hpc _ (htT i)
    intro i l hl; obtain he : Continuous (fun t:ℝ=> fieldVal (hereZ n F t (x i) 0) (ray l) 1):= ((full_sm h (x i) (n:=0) (ray l)).comp ( f:=fun t:ℝ=> (t,(1:ℝ))) (by fun_prop)).continuous; simp_rw [fieldVal,ray_sail] at he; exact he
lemma collectFee {P: Pack G}(h:Fees b v P): collect (fun i t=> P (x i) (exp t)):= by obtain ⟨k,h⟩:= h.pay; exact ⟨k,fun i _=> h (x i) _⟩ -- collect includes global positive rank
lemma collectD (h:Host F n): collect (nameR (four n F) x):= by obtain ⟨k,hK⟩:= h.cap; refine ⟨ k.toNat,fun i t l hl=>?_⟩; let T:= hereZ n F t ( x i ); obtain hx: Issue k T:= valueC h.tall ( Moony.toast h.bill ) (Mell.grade k G) need_tail hK; exact hx 0 l (by omega)
end YM.MS.Rake
