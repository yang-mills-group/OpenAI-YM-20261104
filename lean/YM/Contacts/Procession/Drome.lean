import YM.Contacts.Procession.Rondel
/-! # Budget for all wavelength registers exhausted.We use the **same** Walk circuit on the cover.
Exp.Mark.Tops. Then take the indicated functionals. -/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts.Procession.Xenon
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Sun
open scoped Classical Topology BigOperators NNReal ENNReal Matrix ContDiff
variable {α β ι:Type}{G:Gauge}{σ:ℝ≥0}{b c:ℝ}{m:Side}{u h i k:ℕ}
-- rectangular extensions; sign free on field rows.
def candy (R:Row α β) : Row (Option α) (Option β) := fun i j=> i.elim 0 fun a=> j.elim 0 fun b=> R a b
def piece (R:Row α β) : Row (Option α) (Option β) := fun i j=> i.elim (j.elim (unitRow Unit () ()) (fun _ =>0)) fun a=> j.elim 0 fun b=> R a b
def tint (α:Type) : Row α (Option α) := fun i j=> j.elim 0 fun a=> unitRow α i a
variable {R: Row α β}
lemma unit_zero (x y:Cover) : unitRow Unit () () (y-x)= if x=y then 1 else 0:= by simp [unitRow, eq_comm,sub_eq_zero]
lemma tinrice : (tint α).strip σ 1:= by
    intro i j; cases j; · simpa [Width,tint] using (budget_loosen (budget_zero (α:=Cover)) (show (0:ℝ)≤1 by norm_num)) -- simp tint
    exact strip_unit _ _
lemma candy_leaf (h:R.strip σ b)(hp:0≤b) : (candy R).strip σ b:= by intro i j; cases i <;> cases j <;> first| apply h | simpa [Width,candy] using budget_loosen (budget_zero (α:=Cover)) hp
lemma piece_leaf (h:R.strip σ b)(hp:1≤b): (piece R).strip σ b:= by
    intro i j; have hx:0≤b:= zero_le_one.trans hp; have hu:Width σ b (fun _:Cover=>(0:ℝ)):= by simpa [Width] using (budget_loosen (budget_zero (α:=Cover)) hx)
    cases i <;> cases j <;> first | exact hu| apply h | exact Width.mono (by apply strip_unit () ()) (rfl.le) hp
lemma footplane {R:Row α α}: plane (candy R)=quiet (plane R):= by funext ⟨i,a⟩ ⟨j,b⟩; cases a <;> cases b <;> rfl
lemma shadeplane (R:Row α β): plane (piece R)=veil (Matrix.of (plane R)):= by funext ⟨i,a⟩ ⟨j,b⟩; cases a <;> cases b <;> first| rfl| (simp [plane,piece,veil]; try simp [unitRow, sub_eq_zero]); -- write explicit
lemma ribbons (α:Type): plane (tint α)=coreM Cover α:= by funext ⟨i,a⟩ ⟨j,b⟩; cases b <;> simp [plane,coreM,tint,unitRow] <;> grind
lemma period_Quiet (m:Side){R:Row α α}: (candy R).acts m=Matrix.of (quiet (R.acts m)):= by
   ext ⟨i,a⟩ ⟨j,b⟩; cases a <;> cases b <;> first | rfl| simp [Row.acts,candy,quiet]
lemma period_shade (R:Row α β)(m:Side): (piece R).acts m=veil (R.acts m):= by
   ext ⟨i,a⟩ ⟨j,b⟩; cases a <;> cases b <;> first| rfl| simp [Row.acts,piece,veil] -- likely none none using acts_unit
   change (unitRow Unit).acts m (i,()) (j,()) = _; rw [acts_unit]; simp [Matrix.one_apply, eq_comm]
lemma period_ribbons (α:Type)(m:Side): (tint α).acts m=coreM (Site m) α:= by
    ext ⟨i,a⟩ ⟨j,b⟩; cases b; · simp [Row.acts,tint,coreM]
    rename_i b; change (unitRow α).acts m (i,a) (j,b) = _; rw [acts_unit,Matrix.one_apply]; unfold coreM; simp
variable [Fintype α][Fintype β]
def pads (α β:Type)[Fintype α][Fintype β](k:ℕ)(b a:ℝ):ℝ:= ((Fintype.card α:ℝ)*b)*a*((Fintype.card β:ℝ)*b)^(k-1)
lemma reaches {A: House (Node α)}{V:House (Co m α)}(h:Two (voyageW m σ α) (A i k) (V i k) b 0): Two (voyageW m σ _) (cloak A i k) (cloak V i k) (pads α (Option α) k 1 b) 0:= by have ht:=hoist_comp (tint α) m (tinrice (α:=α) (σ:=σ)) zero_le_one h; dsimp only at ht; rw [mul_zero,zero_mul] at ht; erw [ribbons, period_ribbons] at ht; exact ht
lemma pulsive {x:α}{F:Field (Fin i) (Node α)} (h:Rest (terrain σ α) (0,x) F b) (m:Side): Two (voyageW m σ _) (stem F) (stem (packing (lower m) F)) b 0 := (together_due (heritage (fun x z=>scar_shift F x z) m) (scar_paid x h) (beyond m F)).print
-- cap witness length homogeneous call, **uniform in choice of t=T call time for birth**
def stainCharge (α:Type)[Fintype α](g:TableFee)(x:ℝ): TableFee:= fun i j=> pads α (Option α) j 1 (g i j)+x
lemma ring_energy (A:House (Node α))(F:Field (Fin i) (Node α)){x:α}(V:House (Co m α))(g:TableFee)(h:∀ i j, Two (voyageW m σ α) (A i j) (V i j) (g i j) 0)(hf:Rest (terrain σ α) (0,x) F b)(j k t:ℕ):
   Two (voyageW m σ _) (ringS t F A j k) (ringS t (packing (lower m) F) V j k) (stainCharge α g b j k) 0:= by
    unfold ringS; let U:=Option α; simp_rw [Pi.add_apply]; let W:= voyageW m σ U; let X:= reaches (h j k)
    by_cases hm: j=t; swap; · simp_rw [Pi.single_eq_of_ne hm]; simp only [Pi.zero_apply, add_zero]; exact X.shift (le_add_of_nonneg_right hf.cash) le_rfl
    subst t; simp_rw [Pi.single_eq_same]; by_cases hu:k=i+1; swap; · simp_rw [Pi.single_eq_of_ne hu,add_zero]; exact X.shift (le_add_of_nonneg_right hf.cash) le_rfl
    subst k; rw [Pi.single_eq_same,Pi.single_eq_same]; have hv:= X.add (pulsive hf m); rw [zero_add] at hv; exact hv
end YM.Contacts.Procession.Xenon
