import YM.OPE.PolyDisk

/-! A one-sided tensor stencil in directions not necessarily aligned with
  the axes. All coordinates are processed once; estimates only on successive
  single-parameter moves from nearby configurations are needed. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stencils
open PolyDisk
open scoped BigOperators Classical Topology
open Function Filter Set

variable {V : Type*} {ι : Type*} [DecidableEq ι]

/-- First root strictly above `p`, plus successors. -/
def steps (a : ℝ) (p:ℝ)(j:ℕ) : ℝ := a*((⌈p/a⌉:ℤ)+1+j)
def angle (a p : ℝ) := p/a-(⌈p/a⌉:ℤ)-1

section Algebra
variable (A:ℕ)(a:ℝ)
lemma angle_law {p : ℝ} : |angle a p| ≤ 3:=by unfold angle; have h₁:=Int.le_ceil (p/a); have h₂:=Int.ceil_lt_add_one (p/a); apply abs_le.mpr; constructor <;> linarith only [h₁,h₂]
lemma step_affine {p:ℝ}(ha:0<a)(j:Fin A) : steps a p j = p + displacement a (angle a p) j:= by unfold steps angle displacement;field_simp;ring
lemma step_near {p:ℝ}(ha:0<a)(j:Fin A): 0<steps a p j-p∧steps a p j-p≤a*(A+3):=by
    rw [step_affine A a ha j]; unfold displacement
    have h : angle a p<0 := sub_neg.mpr ((sub_nonpos.mpr (Int.le_ceil _)).trans_lt (by norm_num))
    have ht := abs_le.mp (angle_law a (p:=p))
    rw [add_comm p,add_sub_cancel_right]; constructor
    · exact (mul_pos ha (sub_pos.mpr (h.trans_le (Nat.cast_nonneg _))))
    have hh: (j.val:ℝ)≤A:=Nat.cast_le.mpr j.is_lt.le
    nlinarith only [ha,hh,ht.1]

variable [NormedAddCommGroup V] [NormedSpace ℂ V]
def tensor (p:ι→ℝ) (f : (ι→ℝ)→V) (run:List ι): V := match run with
   | [] => f p
   | k::l => ∑ i:Fin A, lagWeight (angle a (p k)) i • tensor (update p k (steps a (p k) i)) f l

def valid (run:List ι)(p x:ι→ℝ) : Prop:= ∀ k,(k∈run→∃ i:Fin A, x k=steps a (p k) i)∧(k∉run→x k=p k)

/-- Express as one finite sum for relating different readings against the
same auxiliary vector. -/
lemma budget : ∃ R:ℝ,1 ≤ R ∧∀ p:ℝ,(∑ j:Fin A, ‖lagWeight (angle a p) j‖)≤R:= (lag_budget A).imp fun R ⟨h,ht⟩=>⟨h,fun _=> ht _ (angle_law a)⟩

lemma valid_grow {k:ι} {p x:ι→ℝ}{i:Fin A}{run:List ι} (h' : (k::run).Nodup) (h:valid A a run (update p k (steps a (p k) i)) x) : valid A a (k::run) p x:=by
   intro l; by_cases hl : l=k
   · subst l; exact ⟨fun _=>⟨i,h k |>.2 (List.nodup_cons.mp h').1 |>.trans (update_self ..)⟩, fun he=>False.elim (he List.mem_cons_self)⟩
   simp only [List.mem_cons,hl,false_or,valid]
   exact ⟨fun ht=> (h l).1 ht|>.imp (fun _ heq=>heq.trans (by rw [update_of_ne hl])),fun ht=> (h _).2 ht |>.trans (update_of_ne hl _ _)⟩

lemma tensor_bound {R B:ℝ} (hR:∀ p:ℝ,(∑ j:Fin A, ‖lagWeight (angle a p) j‖)≤R)(hB:0≤B)
     (run:List ι) (h':run.Nodup)(p:ι→ℝ)(f:(ι→ℝ)→V) (h:∀ x,valid A a run p x→‖f x‖≤B): ‖tensor A a p f run‖ ≤ B*R^run.length:=by
   have hp : 0 ≤ R:=le_trans (Finset.sum_nonneg fun z _=>norm_nonneg _) (hR 0)
   induction run generalizing p with
   | nil=>exact (h p fun k=>⟨fun he=>False.elim (by simpa using he),fun _=>rfl⟩).trans_eq ((by simp):B=B*R^ ([]:List ι).length)
   | cons k l ih=>
     have ih'(i:Fin A):= ih (List.nodup_cons.mp h').2 (update p k (steps a (p k) i)) (fun x hx=>h x (valid_grow A a h' hx))
     rw [tensor]; apply (norm_sum_le ..).trans
     calc
       _ ≤ (∑ i:Fin A, ‖lagWeight (angle a (p k)) i‖*(B*R^l.length)):= Finset.sum_le_sum (fun i _=> by rw [norm_smul]; gcongr; exact ih' i)
       _ ≤ _ := by rw [← Finset.sum_mul, List.length_cons, pow_succ (n:=l.length),show B * (R ^ l.length * R)= (B*R^l.length)*R by ring, mul_comm (B*_ ) R]; gcongr; exact hR _

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
@[simp] lemma tensor_map (h : V→ₗ[ℂ] W)(p:ι→ℝ)(f : (ι→ℝ)→V)(run:List ι) : h (tensor A a p f run) = tensor A a p (h ∘ f) run:=by
    induction run generalizing p with
    | nil=>rfl
    | cons i l ih=> simp [tensor,map_sum,ih, comp_def]

@[simp] lemma tensor_sub (p:ι→ℝ)(f g:(ι→ℝ)→V)(run:List ι) : tensor A a p (f-g) run=tensor A a p f run-tensor A a p g run:=by
    induction run generalizing p with
    | nil=>rfl
    | cons i l ih=> simp [tensor,ih,smul_sub,Finset.sum_sub_distrib]

@[simp] lemma tensor_smul (c:ℂ) (p:ι→ℝ)(f:(ι→ℝ)→V)(run:List ι) : tensor A a p (c • f) run=c • tensor A a p f run:=by
    induction run generalizing p with
    | nil=>rfl
    | cons i l ih=>
      simp_rw [tensor]
      simp_rw [Finset.smul_sum,ih]
      apply Finset.sum_congr rfl fun j _=> by rw [smul_smul,smul_smul]; exact congr_arg (fun z : ℂ=> z • _) (mul_comm _ _)

/-- A partially advanced tensor coordinate. -/
def Partway (run:List ι)(p y:ι→ℝ) : Prop:= ∀ i,(i ∈ run→y i=p i)∧(∀ k∉run, 0 ≤ y k-p k ∧ y k-p k ≤ a*(A+3)) -- repeated ∀k.

/-- Telescoping. -/
lemma tensorCost {R b:ℝ}(hR:∀ p:ℝ,(∑ j:Fin A, ‖lagWeight (angle a p) j‖)≤R)(hb:0≤b) {p:ι→ℝ}(ha:0<a)
     {f:(ι→ℝ)→V} {ιs:Finset ι} (h:∀ x i, Partway A a [i] p x→ i∈ιs → ‖f x-tensor A a x f [i]‖≤ b) (y:ι→ℝ)(run:List ι)(h':run.Nodup)(hκ:Partway A a run p y)(hw:∀ i∈run,i∈ιs): ‖f y-tensor A a y f run‖ ≤ b*(1+R)^run.length:=by
   have h₀:0 ≤ R:=le_trans (Finset.sum_nonneg fun z _=>norm_nonneg _) (hR 0)
   induction run generalizing y with
   | nil=> simp only [tensor,sub_self,norm_zero,List.length_nil,pow_zero,mul_one]; exact hb
   | cons k l ih=>
     let u:= fun i:Fin A=> update y k (steps a (y k) i)
     let C₀:=b*(1+R)^l.length
     have hp(k:ℕ) : 0≤b*(1+R)^k:=mul_nonneg hb (by positivity)
     have hq k : b≤b*(1+R)^k:=le_mul_of_one_le_right hb (one_le_pow₀ (by linarith only [h₀]))
     have ih'(i:Fin A): ‖f (u i) - tensor A a (u i) f l‖ ≤ C₀:= ih (u i) (List.nodup_cons.mp h').2 (fun v=>by
          have hkn := (List.nodup_cons.mp h').1
          refine ⟨fun hv=>by dsimp only [u]; rw [update_of_ne (show v≠k by rintro rfl; exact hkn hv)]; exact (hκ _).1 (List.mem_cons_of_mem _ hv), fun v hv=>?_⟩
          by_cases hk : v=k
          · subst v; dsimp only [u]; rw [update_self, (hκ _).1 List.mem_cons_self]; exact ⟨(step_near A a ha i).1.le,(step_near A a ha i).2⟩
          rw [show u i=update _ _ _ from rfl,update_of_ne hk];exact (hκ k).2 _ fun ht=> by simpa [hk,hv] using ht) (fun _ he=> hw _ (List.mem_cons_of_mem _ he))
     have hh: ‖f y-tensor A a y f [k]‖≤ b:= h y _ (by
       intro i; refine ⟨fun he=>?_,fun v hv=>?_⟩
       · obtain rfl := List.mem_singleton.mp he; exact (hκ _).1 List.mem_cons_self
       by_cases he:v∈k::l
       · simp [(hκ _).1 he, mul_nonneg ha.le (show 0≤(A:ℝ)+3 by positivity)]
       exact (hκ i).2 _ he) (hw _ List.mem_cons_self)
     have he': f y-tensor A a y f (k::l) = f y- tensor A a y f [k] + (∑ i:Fin A, lagWeight (angle a (y k)) i • (f (u i)-tensor A a (u i) f l)):= by  simp only [tensor,smul_sub,u,Finset.sum_sub_distrib]; abel
     rw [he']; calc
       _ ≤ _ := norm_add_le _ _
       _ ≤ b + ∑ i:Fin A, ‖lagWeight (angle a (y k)) i‖*C₀ := add_le_add hh ((norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=> (norm_smul ..).le.trans (by gcongr;exact ih' i))))
       _ ≤ b+R*C₀:=by rw [← Finset.sum_mul]; gcongr; exact hR _
       _ ≤ _ :=by rw [List.length_cons,pow_succ]; unfold C₀; linarith only [hq l.length]
end Algebra
end YM.OPE.Stencils
