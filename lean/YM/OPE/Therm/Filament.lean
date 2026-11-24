import YM.OPE.Therm.Rite
import YM.Push.LOCAL_SPLITTING.Orientation
import YM.Next.RANK.Evaluation
import YM.Next.RANK.Headwater
import YM.Corona.Fit
import YM.Push.ABSOLUTE_SUMS.Path
/-!
# Long string tails, per anchor

No analyticity appeals and no mask continuation. This file makes a collection of
uniform (GOOD and BAD) energy leaves for a pressure consumption. Evaluate
atoms with their own actual pull/flag sets. Native covers for E include cost
via the *anchored* budget, so merely cutting E masks here to finite range is
valid also for non-local choices of address tails in the supplied History.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Therm.Stove
open Function Filter RG Lattice Wilson MeasureTheory Next Next.Rank Next.Rank.Alarm PathData Cells Push.AbsoluteSums
open scoped BigOperators Classical Topology
variable {G : Gauge} {n : Side} {k:ℕ}
variable {c σ C Λ δ t w L:ℝ}
local notation "Ex" => Real.exp
local notation "𝒞" => Config G n

section widths
variable {ι F : Type*}[NormedAddCommGroup F] [CompleteSpace F]
def ends (len:ι→ℕ)(r:ℕ)(f:ι→F) (i:ι) := if len i≤r then f i else 0
def narrow (len:ι→ℕ)(r:ℕ)(f:ι→F) := ∑' i, ends len r f i

lemma threads (len:ι→ℕ)(r:ℕ)(f:ι→F)(A:ι→ℝ)(h:SumBudget (fun i=> A i* Ex (σ * len i)) C)
    (hv:0<σ)(hp:∀ i,‖f i‖ ≤ A i) :
    ‖∑' i, f i‖ ≤ C ∧ ‖narrow len r f‖≤ C ∧ ‖(∑' i,f i)-narrow len r f‖ ≤ Ex (-σ*r)*C := by
   let B i := A i* Ex (σ* len i); let z:= ends len r f; let a:=Ex (-σ*r)
   have hx (i):0≤ A i:= (norm_nonneg (f i)).trans (hp i); have hB (i): A i ≤B i:= le_mul_of_one_le_right (hx _) (Real.one_le_exp (by positivity)); have ha:0≤a:=(Real.exp_pos _).le
   have he (i): ‖z i‖ ≤B i:=by unfold z ends; split; exact (hp _).trans (hB _);rw [norm_zero]; exact h.1 _
   have hζ (f:ι→F) (a:ℝ)(h₁:0≤a)(h₂:∀ i,‖f i‖ ≤ a*B i) : ‖∑' i,f i‖ ≤ a*C:=by
      have hβ:=(h.2.1.mul_left a); have ht := hβ.of_nonneg_of_le (fun i=> norm_nonneg (f i)) h₂; apply (norm_tsum_le_tsum_norm ht).trans ((ht.tsum_le_tsum h₂ hβ).trans ?_); rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h.2.2 h₁
   have hF (i): ‖f i‖ ≤ B i:= (hp _).trans (hB _)
   refine ⟨(by simpa only [one_mul] using (hζ f 1 zero_le_one (by simpa only [one_mul]))), (by simpa only [one_mul] using! (hζ z 1 zero_le_one (by simpa only [one_mul]))), ?_⟩
   change ‖(∑' i,f i)-∑' i,z i‖ ≤ _;rw [← Summable.tsum_sub (h.2.1.of_norm_bounded hF) (h.2.1.of_norm_bounded he)]
   apply hζ _ a ha; intro i; unfold z ends; split
   · rw [sub_self,norm_zero]; exact mul_nonneg ha (h.1 _)
   rename_i hh
   rw [sub_zero]; apply (hp _).trans; unfold B; rw [mul_left_comm]; apply le_mul_of_one_le_right (hx i); unfold a;rw [← Real.exp_add]; refine Real.one_le_exp ?_; have ht := (Nat.le_of_not_ge hh); have hm := mul_le_mul_of_nonneg_left (show (r:ℝ)≤len i by exact_mod_cast ht) hv.le; linarith only [hm]
end widths
variable {R : Rep G n} (r:ℕ)

section ell
variable (F:PathData G){c : Clip}
lemma rip (h:F.Bounds c σ C Λ) (i:PlaqAxes)(U:𝒞) :
    ‖F.ell U (0,i)‖ ≤ 2*C ∧ ‖lakeHead F r i U‖ ≤2*C ∧ ‖F.ell U (0,i)-lakeHead F r i U‖ ≤ Ex (-σ*r)*(2*C) := by
   let c' i':= |(F.row i i').1|
   let A i':= 2*c' i'; let l k:= (F.row i k).2.length
   let h1:= h.rows i; refine threads l r (fun k=> F.ellTerms (0,i) k U) A ?_ h.width ?_
   · have hx (j): A j*Ex (σ*l j)= 2*(c' j*Ex (σ*l j)):=by unfold A; ring
     simp_rw [hx]; refine ⟨fun i'=>mul_nonneg (by norm_num) (h1.1 _),h1.2.1.mul_left _,?_⟩; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h1.2.2 (by norm_num)
   intro j; rw [ellTerms,norm_smul,Real.norm_eq_abs]; exact (mul_le_mul_of_nonneg_left (Slot.eval_norm ..) (abs_nonneg _)).trans_eq (mul_comm ..)
end ell
section atom
variable (F:ℕ→Atom G k)(p:BudgetPoint)
def chips (U:𝒞) := narrow (fun i=> (F i).length) r (fun i=>(F i).placed p U 0)
lemma tear (h:SumBudget (fun i=> (F i).budget σ) C) (hu:0<σ)(U:𝒞) :
    ‖atomSeries F p U 0‖ ≤ 2^k * C ∧ ‖chips r F p U‖ ≤ 2^k * C ∧ ‖atomSeries F p U 0 - chips r F p U‖ ≤ Ex (-σ*r)*(2^k*C):=by
   let A i:= 2^k*(F i).magnitude; let t i:=(F i).budget σ; refine threads (σ:=σ) (fun i=> (F i).length) r _ A ?_ hu (fun i=>((F i).placed_bound ..).trans_eq (mul_comm ..))
   have ht (i): A i*Ex (σ*(F i).length)= 2^k*t i:=by unfold A t Atom.budget; ring
   simp_rw [ht]; refine ⟨fun i=> mul_nonneg (by positivity) (h.1 _), h.2.1.mul_left _,?_⟩; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h.2.2 (by positivity)
lemma chips_meas : Measurable (chips (n:=n) r F p):= Measurable.tsum (fun i=> by unfold ends; split; exact masked_measurable _ _ _ ((F i).unmasked_cont (0 : Site n)|>.measurable); exact measurable_const)
lemma chips_local: LocalOn (halo (r+8) ({0}: Support n)) (chips (n:=n) r F p):= by
   intro U V h; refine tsum_congr fun i=>?_ ; unfold ends; split
   · rename_i hi
     refine sail p.threshold _ _ (unmasked_space (F i) 0) U V (agrees_mono h fun u hu=>?_)
     obtain ⟨v,hv,hz⟩:= halo_spec.mp hu; rw [Paths.atom_foot] at hv
     exact halo_spec.mpr ⟨0,Finset.mem_singleton_self _,(separation_triangle _ v _).trans (Nat.add_le_add ((Paths.where_slot _ _ _ hv).trans hi) hz)⟩
   rfl
end atom
section regular
variable {A:Activities G n}(p:BudgetPoint)
def leaf (A:Activities G n)(U:𝒞)(i:ℕ) := if (A.reg i).site=0 then A.regularOccurrence p i U else 0
def ease (A:Activities G n)(U:𝒞):= ∑' i, leaf p A U i
def toast (A:Activities G n)(U:𝒞):= narrow (fun i=>coverNumber p.B (A.reg i).support) r (leaf p A U)
def eroom (r:ℕ):= r*(4*p.B+2)+2*p.B+8
lemma gentle (h : A.Valid p δ w) (U:𝒞) : ‖ease p A U‖ ≤ δ ∧ ‖toast r p A U‖ ≤ δ ∧ ‖ease p A U-toast r p A U‖ ≤ Ex (-p.supportExponent*r)*δ:=by
   obtain ⟨b,hb,hS⟩:= h.boundE
   let v i:= (A.reg i).support; let l i:=coverNumber p.B (v i); let f i:=A.regularOccurrence p i U; let F i:= if (A.reg i).site=0 then b i else 0
   refine threads l r (leaf p A U) F ?_ p.exponent_pos ?_
   · convert hS 0 using 1; ext1 i; unfold F; split; exact mul_comm ..; rw [zero_mul]
   intro i; unfold F leaf; split
   · unfold Activities.regularOccurrence; by_cases hi: Healthy p.threshold (A.reg i).support U
     · rw [masked_eq _ _ _ _ hi]; exact (hb i).2 U hi [] (Nat.zero_le _) (by simp)
     rw [masked_ne _ _ _ _ hi,norm_zero]; exact (hb i).1
   exact (norm_zero).le
lemma toast_meas (h : A.RegularFamily p): Measurable (toast r p A):=by
   apply Measurable.tsum; intro i; unfold ends; split
   · unfold leaf; split; exact masked_measurable _ _ _ (h.smooth i).borel; exact measurable_const
   exact measurable_const
lemma toast_local (h:A.RegularFamily p): LocalOn (halo (eroom p r) ({0}:Support n)) (toast r p A):=by
   intro U V hp; refine tsum_congr fun i=>?_ ; unfold ends leaf; dsimp only; split; swap; · rfl
   rename_i hx; split; swap; · rfl
   rename_i he; refine (sail p.threshold _ _ (h.smooth i).sites) U V (agrees_mono hp fun x hz=>?_)
   obtain ⟨y,hy,hY⟩:=halo_spec.mp hz; have ht : (0:Site n)∈ (A.reg i).support:= he ▸ (A.reg i).anchor
   apply halo_spec.mpr; refine ⟨0,Finset.mem_singleton_self _,(separation_triangle _ y _).trans ?_⟩; exact Nat.add_le_add ((Corona.extent _ p.B ht hy).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hx) _)) hY
lemma repeated_leaf (h:A.Valid p δ w)(U:𝒞)(u:Signed)(x:Site n) :
    ease p A (pull u x U)= ∑' i,if (A.reg i).site=x then A.regularOccurrence p i U else 0 := by
   obtain ⟨M⟩:= h.moves u x; unfold ease; conv_rhs => rw [← M.ep.tsum_eq]
   apply tsum_congr; intro i; unfold leaf; rw [comp_turn A x u M,M.reg_site]; have he: affine u x (A.reg i).site=x ↔ (A.reg i).site=0:= by
      convert (show (Push.Local.turnSites u x) _ = Push.Local.turnSites u x (0:Site n) ↔ (A.reg i).site=0 from (Push.Local.turnSites u x).injective.eq_iff) using 1; simp [show ⇑(Push.Local.turnSites u x)= affine u x from rfl,affine]
   simp only [he]
lemma rested (h:A.Valid p δ w)(U:𝒞) : rag (ease p A) U=A.additive p U:=by
   let B (x:Site n) (i) := if (A.reg i).site=x then A.regularOccurrence p i U else 0
   have hf (i): (∑ x:Site n, B x i)= A.regularOccurrence p i U:= by simp [B]
   have hx (x) : Summable (B x):= by refine (((Activities.ESeries h).summable U).indicator (s:={i| (A.reg i).site=x})).congr fun i=>?_; by_cases hi:(A.reg i).site=x<;>simp [*, Set.indicator,B]
   have hE (u:Signed): (∑ x:Site n, ease p A (pull u x U))= A.additive p U:=by
       simp_rw [repeated_leaf p h U]; exact (Summable.tsum_finsetSum (f:=B) (fun x _=> hx x)).symm.trans (tsum_congr hf)
   unfold rag;simp_rw [hE]; rw [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,inv_mul_cancel_left₀]; exact_mod_cast Fintype.card_pos (α:=Signed)|>.ne'
end regular
end YM.OPE.Therm.Stove
