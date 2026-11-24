import YM.RG02.Laurent.L1
import YM.Progress.CLASSICAL_KIN_RECURSION.Dock
import YM.Laurent.Art

/-!
# Projectively local kernels through finite derivative slots

Metric stride (coarse cubes). Store color indices *inside* ℓ¹.
Real or complex actual stem families. Before period Wick only! Looped
answers may include windings; see Laurent. Keep external marking data
via index and slot flags. Small tori ADMITTED whenever stencil operations
actually have a physical analogue there. Here >=t only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Native
open Function Finset Lattice RG Precision Progress.ClassicalKin Progress.ClassicalKin.Tent
open scoped BigOperators Classical Topology

abbrev Leaf (α:Type)(n:Side) := Site n × α
abbrev Arm (α:Type) := Cover × α
abbrev CoverForm (α β A Z:Type) := β → (A→Arm α) → Z
abbrev OnTorus (α β A Z:Type)(n:Side) := Leaf β n → (A→Leaf α n) → Z
abbrev PeriodicTable (α β A Z:Type) := (n:Side)→OnTorus α β A Z n
variable {α β A Z: Type}
variable [NormedAddCommGroup Z] {n m:Side}

-- orientation: arm displacement = input minus output
def emit (o:Site n)(u: A→Arm α): A→Leaf α n:= fun a=>(o+wrap n (u a).1,(u a).2)
def stall (o:Site n)(j:A→Leaf α n): A→Arm α:= fun a=>(lift ((j a).1 - o),(j a).2)
lemma emit_stall (o:Site n)(j:A→Leaf α n):emit o (stall o j)=j:=by ext <;> simp [emit,stall]
lemma stall_one (o:Site n): Injective (stall (A:=A) (α:=α) o):= LeftInverse.injective (emit_stall o)

-- arbitrary common translation retained (proper covariance operator etc)
def collapse (h:divides n m)(o:Site n)(x: Leaf α m) : Leaf α n:= (lieBy h o x.1,x.2)
lemma collapse_emit (h:divides n m)(x:Site n)(r:Site m)(i:A→Arm α) : collapse h x ∘ emit r i =emit (lieBy h x r) i:=by
    funext j; refine Prod.ext ?_ rfl; change shrinkTo h (_+_)+x=_+_; rw [map_add,shrinkWrap]; unfold lieBy; abel
lemma collapse_self (n:Side)(i:Leaf α n) : collapse (dvd_refl n.val) 0 i=i:=by simp [collapse, lieBy, shrinks_self]

def imprint (F:CoverForm α β A Z)(n:Side) : OnTorus α β A Z n:=fun i j=> ∑' k:A→Arm α,if emit i.1 k=j then F i.2 k else 0

variable [Fintype A]
def length (v:A→Arm α) := ∑ i:A,Laurent.stride (v i).1
def spanAt (r:Site n)(v:A→Leaf α n) := ∑ i:A,separation (v i).1 r
lemma span_cost (r:Site n)(v:A→Arm α) : spanAt r (emit r v) ≤ length v:=by
    refine sum_le_sum (fun i _=>?_); change pdist (r+wrap n _-r) ≤ Laurent.stride _; rw [add_comm,add_sub_cancel_right]; apply Laurent.stride_wrap
lemma exact_stall (o:Site n)(j:A→Leaf α n) : length (stall o j)=spanAt o j:= rfl
lemma unchanged (o:Site n)(v:A→Arm α)(h:2*length v<n.val) : stall o (emit o v)=v:=by
    funext i; refine Prod.ext ?_ rfl; change lift (o + wrap n _-o)=_
    rw [add_comm,add_sub_cancel_right]
    exact Laurent.returns (lt_of_le_of_lt (Nat.mul_le_mul_left _ (single_le_sum (f:=fun i:A=>Laurent.stride (v i).1) (fun _ _=>Nat.zero_le _) (mem_univ i))) h)

-- Weights indexed by stencil tails within branch directions. For unused
-- markers still carry slot norm. Covers the operator where palette excludes
-- sites. Sectors needing additional stencil weight must budget it here.
def fee (a:ℝ)(F:CoverForm α β A Z)(i:β)(v:A→Arm α) := Real.exp (a* length v)*‖F i v‖
def cost (a:ℝ)(F:OnTorus α β A Z n)(i:Leaf β n)(j:A→Leaf α n) := Real.exp (a*spanAt i.1 j)*‖F i j‖

def narrow (a C:ℝ)(F:CoverForm α β A Z) := ∀ i:β, SumBudget (fee a F i) C

variable [Fintype α]

def ticket (F:OnTorus α β A Z n)(a:ℝ)(i:Leaf β n) := ∑ j:A→Leaf α n,cost a F i j
-- Use true sizes. Constants may depend palette and output ports.
def charged (t:ℕ)(a C:ℝ)(U:PeriodicTable α β A Z) := ∀ n:Side,t≤n.val→ ∀ i,ticket (U n) a i≤C

def coherent (t:ℕ)(U:PeriodicTable α β A Z) := ∀ (n m:Side) (h:divides n m)(o:Site n) (i:Leaf β m)(j:A→Leaf α n), t≤n.val→
    U n (collapse h o i) j = ∑ k:A→Leaf α m,if collapse h o ∘ k=j then U m i k else 0

omit [Fintype α] in
lemma narrow_mono {a C:ℝ}{F:CoverForm α β A Z}(he:narrow a C F){u D:ℝ}(hp:u≤a)(hc:C≤D) : narrow u D F:=by
   intro i
   have hh := he i
   have h j : fee u F i j≤fee a F i j:=by unfold fee; gcongr
   have hn j : 0 ≤ fee u F i j:=mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
   have hv := Summable.of_nonneg_of_le hn h hh.2.1
   exact ⟨hn,hv,(hv.tsum_le_tsum h hh.2.1).trans (hh.2.2.trans hc)⟩
lemma charged_mono {t a C}{U:PeriodicTable α β A Z}(he:charged t a C U){u D:ℝ}(hp:u≤a)(hc:C≤D) {T:ℕ}(hv:t≤T) : charged T u D U:=by
   intro n hn i
   have hh := he n (hv.trans hn) i
   have h j : cost u (U n) i j≤cost a (U n) i j:=by unfold cost; gcongr
   exact (sum_le_sum fun j _ => h j).trans (hh.trans hc)
lemma coherent_mono {t}{U:PeriodicTable α β A Z}(he:coherent t U){s:ℕ}(h:t≤s) : coherent s U:= fun n m hf o i j hp=> he n m hf o i j (h.trans hp)
lemma active_of {F:OnTorus α β A Z n}{i:Leaf β n}{j:A→ Leaf α n} {a:ℝ} : cost a F i j ≤ ticket F a i:=by
   exact single_le_sum (f:=cost a F i) (fun u _=> mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) (mem_univ _)

section proc
variable [CompleteSpace Z]

omit [Fintype α] in
lemma narrow.prepaid {F:CoverForm α β A Z}{a C:ℝ}(h:narrow a C F)(ha:0≤a)(i:Leaf β n)(j:A→Leaf α n): HasSum
    (fun k:A→Arm α=> if emit i.1 k=j then F i.2 k else 0) (imprint F n i j):=by
    let f (k:A→Arm α):Z:= if emit i.1 k=j then F i.2 k else 0
    have he : imprint F n i j=∑' k,f k:= by unfold imprint; apply tsum_congr; intro k; unfold f; split_ifs <;> rfl
    rw [he]; change HasSum f (∑' k,f k); apply Summable.hasSum
    refine Summable.of_norm_bounded ((narrow_mono h ha le_rfl) i.2).2.1 ?_
    intro k; unfold f; split
    · simp [fee]
    exact norm_zero.le.trans (((narrow_mono h ha le_rfl) i.2).1 _)

lemma narrow.covers {F:CoverForm α β A Z}{a C:ℝ}(h:narrow a C F)(ha:0≤a)(t:ℕ):coherent t (imprint F):=by
   intro n m hf o i j _
   let g(k:A→Leaf α m)(v:A→Arm α):Z:= if collapse hf o ∘ k=j then if emit i.1 v=k then F i.2 v else 0 else 0
   let u(k:A→Leaf α m):= if collapse hf o ∘ k=j then imprint F m i k else 0
   have he (k:A→Leaf α m) : HasSum (g k) (u k):=by
       by_cases hp:collapse hf o ∘ k=j
       · unfold g u; simp_rw [if_pos hp]; exact h.prepaid ha i k
       unfold g u; simp_rw [if_neg hp]; exact hasSum_zero
   unfold imprint; change _=∑ k:A→Leaf α m,u k
   rw [← (hasSum_sum (s:=univ) fun i _=>he i).tsum_eq]
   apply tsum_congr; intro v; symm
   rw [sum_eq_single (emit i.1 v)]
   · unfold g; rw [collapse_emit]; split
     next H=> simp only [collapse,H, ↓reduceIte]
     next H=> simp only [collapse,H, ↓reduceIte]
   · intro k _ hh; unfold g; split; exact if_neg hh.symm; rfl
   simp
lemma narrow.issues {F:CoverForm α β A Z}{a C:ℝ}(h:narrow a C F)(ha:0≤a)(t:ℕ): charged t a C (imprint F):=by
   intro n _ i
   let f:=fee a F i.2
   let g(j:A→Leaf α n)(v:A→Arm α):= if emit i.1 v=j then f v else 0
   have he (j:A→Leaf α n) : Summable (g j):=by
      apply Summable.of_nonneg_of_le _ _ (h i.2).2.1
      · intro v; unfold g; split; exact (h _).1 _; exact le_rfl
      intro v; unfold g; split; exact le_rfl; exact (h _).1 _
   calc
      _ ≤ ∑ j:A→Leaf α n,∑' v:A→Arm α, g j v := by
         apply sum_le_sum; intro j _
         let u (v:A→Arm α):Z:= if emit i.1 v=j then F i.2 v else 0
         let D:=Real.exp (a*spanAt i.1 j)
         have hx v: D* ‖u v‖ ≤ g j v:=by unfold g u D f fee; split; rename_i h; gcongr; exact_mod_cast h ▸ span_cost ..; simp
         have hr : 0<D:= Real.exp_pos _
         have hs : Summable (fun v=> D* ‖u v‖):= Summable.of_nonneg_of_le (fun v=>mul_nonneg hr.le (norm_nonneg _)) hx (he j)
         have hu : Summable fun v=> ‖u v‖:= (hs.mul_left D⁻¹).congr fun i=> inv_mul_cancel_left₀ hr.ne' _
         unfold cost; rw [← (h.prepaid ha i j).tsum_eq]; change D*‖∑' v:A→Arm α,u v‖≤_
         apply le_trans (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hu) hr.le)
         rw [← tsum_mul_left]; exact hs.tsum_le_tsum hx (he j)
      _ = ∑' v,f v:= by
         rw [← Summable.tsum_finsetSum (f:=g) fun j _=> he j]; apply tsum_congr; intro v
         rw [sum_eq_single (emit i.1 v)]; exact if_pos rfl; exact fun a _ ha=> if_neg ha.symm; simp
      _ ≤ _ :=(h _).2.2
end proc

end YM.RG02.Native
