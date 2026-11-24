import YM.Contacts.Pulse.Laminar
import YM.Next.STATIONARY.Shape.Vertex
/-!
# Our rooting budgets and established Fourier-normal leg calculus

Using unbiased displacement on INFINITE cover. Can consume before/post widths
in different gates. Towers stencils and arbitrary Face(color-active/algebraic).
-/
noncomputable section
namespace YM.Pulse.Spine
open Function Set Finset Filter Lattice RG Wilson Precision Stationary Exterior
open Bloch Laurent Push.AbsoluteSums Extra.Iteration
open scoped Classical Topology BigOperators NNReal
variable {α β X Y Z E : Type} {t n:ℕ} [NormedAddCommGroup E]
variable (σ η:ℝ≥0)
-- always with distinguished color and tag counts, no ℂ extension silently
abbrev Node (α : Type) := Cover×α
def terrain (σ:ℝ≥0)(α:Type) : Range (Node α) where
  fee p q:=⟨Real.exp (σ* (Laurent.size (q.1-p.1):ℝ)),(Real.exp_pos _).le⟩
  one _ _:= Real.one_le_exp (by positivity)
  flat _:= NNReal.eq (by simp [Laurent.size] ; rfl) -- maybe
  mirror x y:= NNReal.eq (by rw [← neg_sub (a:=y.1) (b:=x.1),size_neg])
  fold p q r:= by
    apply NNReal.coe_le_coe.mp; change Real.exp _ ≤ Real.exp _ * Real.exp _
    rw [← Real.exp_add,← mul_add]; apply Real.exp_monotone; gcongr
    norm_cast; rw [show r.1-p.1=(r.1-q.1)+(q.1-p.1) from by abel]; exact (size_add ..).trans_eq (add_comm ..)
@[simp] lemma terrain_step (u v:Node α): (terrain σ α).step u v=Real.exp (σ*(Laurent.size (v.1-u.1):ℝ)) := rfl
lemma terrain_le [Fintype X]{σ η:ℝ≥0}(he:η ≤ σ)(x:X→Node α): (terrain η α).bill x ≤ (terrain σ α).bill x:= (terrain _ _).wide _ ((terrain _ _).one_bill _) fun i j=> le_trans (b:=(terrain σ α).step (x i) (x j)) (by simp only [terrain_step]; gcongr) ((terrain _ _).width ..)

def degree (x:Breed t (Node α)) (i:Keys t) := (x i.1.succ).1 i.2 - (x 0).1 i.2
def alphabet (x:Breed t (Node α)):= Prod.snd ∘ x
def publish (z:Cover)(b:Breed t α) (v:Tailor t)(i:Fin (t+1)):Node α:= (z+legLane v i,b i)
def extract (F:Breed t (Node α)→E) (b:Breed t α) := F ∘ publish 0 b
def flag (b:Breed t α) (f: Tailor t→E) (x:Breed t (Node α)) := if alphabet x=b then f (degree x) else 0
def author (f: Breed t α→Tailor t→E)(x:Breed t (Node α)) := f (alphabet x) (degree x)
@[simp] lemma alpha_issue (z:Cover)(b:Breed t α)(v:Tailor t): alphabet (publish z b v)=b:= rfl
@[simp] lemma deg_issue (z:Cover)(b:Breed t α)(v:Tailor t): degree (publish z b v)=v:= by ext a; simp [degree,publish,legLane]
@[simp] lemma retrieve (x:Breed t (Node α)): publish (x 0).1 (alphabet x) (degree x)=x:= by
  funext i; cases i using Fin.cases with | zero => simp [alphabet,publish,legLane] | succ i=> refine Prod.ext ?_ rfl; ext a; simp [publish,legLane,degree]
omit [NormedAddCommGroup E] in
lemma relocate (F:Breed t (Node α)→E)(h:∀ x (z:Cover), F (fun i=> (z+(x i).1,(x i).2))=F x) : author (extract F)=F := by
  funext x; change F _=F x
  rw [← h _ (x 0).1]; refine congr_arg F (Eq.trans ?_ (retrieve x)); funext; simp [publish]
lemma authors [Fintype α](f:Breed t α→Tailor t→E) (x:Breed t (Node α)): author f x=∑ b:Breed t α,flag b (f b) x:= by simp [author,flag]
omit [NormedAddCommGroup E] in
lemma author_extract (f:Breed t α→Tailor t→E)(b:Breed t α): extract (author f) b=f b:= by funext; simp [author,extract]
lemma degree_code (x:Breed t (Node α)): size (degree x)=∑ j : Fin t,Laurent.size ((x j.succ).1-(x 0).1) := by unfold degree size; rw [Fintype.sum_prod_type]; rfl
lemma expense (x:Breed t (Node α)) (i:Fin (t+1)): Laurent.size ((x i).1-(x 0).1) ≤ size (degree x):= Fin.cases (by simp [Laurent.size]) (fun j => by rw [degree_code]; exact single_le_sum (f:=fun i : Fin t=>Laurent.size ((x i.succ).1-(x 0).1)) (fun _ _=> Nat.zero_le _) (mem_univ j)) i
lemma between (x:Breed t (Node α)) (i j:Fin (t+1)): Laurent.size ((x i).1 - (x j).1)≤ 2*size (degree x):= by
  calc
    _ = size (((x i).1-(x 0).1)+(-((x j).1-(x 0).1))) := by rw [show (x i).1 - (x 0).1 + -((x j).1 - (x 0).1)=(x i).1-(x j).1 from by abel]
    _ ≤ _:= (size_add ..).trans (by rw [size_neg,two_mul]; exact add_le_add (expense x i) (expense x j))
lemma landscape (x:Breed t (Node α)) : (terrain σ α).bill x ≤ Real.exp ((2*σ:ℝ)*size (degree x)) := by
  refine (terrain σ α).wide x (Real.one_le_exp (by positivity)) (fun i j=> ?_); simp only [terrain_step]; rw [mul_comm 2,mul_assoc]; apply Real.exp_monotone; gcongr; exact_mod_cast between x j i
lemma avenue {σ η:ℝ≥0} (x:Breed t (Node α))(h:(t:ℝ)*η ≤ σ): Real.exp (η*(size (degree x):ℝ)) ≤ (terrain σ α).bill x := by
  have hx : 0 < (terrain σ α).bill x := zero_lt_one.trans_le ((terrain σ α).one_bill _)
  by_cases he:t=0; · subst t; rw [degree_code]; simp [(terrain σ α).one_bill x]
  have hu (i:Fin t): t*(η*(Laurent.size ((x i.succ).1-(x 0).1):ℝ)) ≤ Real.log ((terrain σ α).bill x) := by
    apply le_trans (b:=σ*(Laurent.size ((x i.succ).1-(x 0).1):ℝ)); · rw [← mul_assoc]; gcongr
    exact (Real.le_log_iff_exp_le hx).2 ((terrain σ α).width x 0 i.succ)
  apply (Real.le_log_iff_exp_le hx).1
  refine le_of_mul_le_mul_left (a:=(t:ℝ)) ?_ (by exact_mod_cast Nat.pos_of_ne_zero he)
  convert sum_le_sum fun j (_:j∈Finset.univ) => hu j using 1 <;> simp [degree_code,mul_sum]
lemma lock_shift {x y:Breed t (Node α)}(ha:alphabet x=alphabet y)(hb:degree x=degree y)(i:Fin (t+1))(he:x i=y i): x=y := by
  have hx j : (x j).1 = (x 0).1 + legLane (degree y) j := hb ▸ Eq.symm (congr_arg (fun (v:Breed t (Node α))=>(v j).1) (retrieve x))
  have hr : (x 0).1=(y 0).1 := add_right_cancel (b:=legLane (degree y) i) (hx i |>.symm.trans ((congr_arg Prod.fst he).trans (congr_arg (fun (v:Breed t (Node α))=>(v i).1) (retrieve y)).symm))
  exact (retrieve x).symm.trans (by rw [hr,ha,hb,retrieve])
lemma flag_price {f: Tailor t→E}{σ η:ℝ≥0}{b:Breed t α}{C:ℝ} (h: Width η C f)(he:(2*σ:ℝ)≤η): Rooted (terrain σ α) (flag b f) C:= by
  refine ⟨Cost.nonneg h, fun i a=> ?_⟩
  let Z:= Locked (Node α) i a; let W:= {p: Z// alphabet p.val=b}; let g (p:W):=degree p.val.val
  have hg : Injective g:= fun p q h=> Subtype.ext (Subtype.ext (lock_shift (p.property.trans q.property.symm) h i (p.1.property.trans q.1.property.symm)))
  let r (z:Z):= ‖flag b f z.val‖*(terrain σ α).bill z.val; change SumBudget r _; have hr z:0≤ r z:= by unfold r; positivity
  have hh : SumBudget (fun z:W=>r z.val) C:= by
    refine budget_mono (budget_pull g hg h) (fun _=> hr _) fun z=>?_ ; dsimp only [r,g]; rw [flag, if_pos z.property,mul_comm]; gcongr; exact (landscape σ _).trans (by gcongr)
  have hu : ∀ z ∉ Set.range (Subtype.val : W→Z), r z=0 := by
    rintro i h; dsimp [r]; rw [flag, if_neg (show ¬ _ from fun he=> h ⟨⟨_,he⟩,rfl⟩),norm_zero,zero_mul]
  have hm := (Subtype.coe_injective.hasSum_iff hu).1 hh.2.1.hasSum
  exact ⟨hr, hm.summable, hm.tsum_eq.trans_le hh.2.2⟩
lemma export_price {F:Breed t (Node α)→E}{σ η:ℝ≥0}{C:ℝ} (h:Rooted (terrain σ α) F C) (b: Breed t α)(he:(t:ℝ)*η≤σ): Width η C (extract F b) := by
  let g (p:Tailor t): Locked (Node α) (0:Fin (t+1)) (0,b 0):= ⟨publish 0 b p,by simp [publish,legLane]⟩
  have hg : Injective g:= fun x y h=> (deg_issue 0 b x).symm.trans ((congr_arg (fun z=> degree (z : Locked (Node α) (0:Fin (t+1)) (0,b 0)).val) h).trans (deg_issue 0 b y))
  refine budget_mono (budget_pull g hg (h.row (0:Fin (t+1)) _)) (fun p=> by positivity) fun p=> ?_
  dsimp only [g,extract,Function.comp_apply]; rw [mul_comm]; gcongr; simpa only [deg_issue] using avenue (publish 0 b p) he
end YM.Pulse.Spine
