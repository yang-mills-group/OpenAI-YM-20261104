import YM.FormalOPE.RG10.Boardwalk.Arrival
/-!
 # Perturbative electricity in positive-order orientation/calibration
Arithmetic. As always not on every time in history. Uniform through finite size only.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Boardwalk
open Function Finset Real Asymptotics Filter Clearing Ledger Rates
open scoped Topology BigOperators Classical
variable {I E F G : Type*}{l:Filter I}
variable (P:Path l)
variable [NormedAddCommGroup E][NormedAddCommGroup F][NormedAddCommGroup G]
def Sized (x:I→E) := Crop P (fun i=> ‖x i‖)
def Prize (x:I→E) := Cut P (fun i=>‖x i‖)
abbrev Compared (x y : I→ E) := Prize P fun i=> x i-y i
-- sqft independent branch growth and their comparative budget
structure Fair (x y:I→E) : Prop where
 size : Sized P x
 shift : Compared P x y

variable {P} {x y z:I→E}{x' y' z':I→ F}
namespace Sized
lemma mono (hx:Sized P x)(hy:∀ᶠ i in l, ‖x' i‖≤‖x i‖): Sized P x' := Crop.mono hx hy
lemma fit (hx:Sized P x)(h:x=ᶠ[l] y): Sized P y := hx.mono (h.mono fun i hi => by rw [hi]) -- linter unused hi
lemma fixed (x:E):Sized P (fun _=>x) := Crop.fixed _
lemma join (hx:Sized P x)(hy:Sized P y): Sized P (fun i=>x i+y i) := (Crop.join hx hy).mono (Eventually.of_forall (fun _=> norm_add_le ..))
lemma neg (hx:Sized P x) : Sized P (fun i=>-x i):= hx.mono (Eventually.of_forall fun i=> (norm_neg (x i)).le)
lemma minus (hx:Sized P x)(hy:Sized P y): Sized P (fun i=>x i-y i) := by simp_rw [sub_eq_add_neg]; exact hx.join hy.neg
lemma income (a:E)(ha:Tendsto x l (𝓝 a)): Sized P x:= (Crop.fixed (‖a‖+1)).mono (ha.norm.eventually (ge_mem_nhds (by linarith)))
lemma done (hx:Sized P x) (r:ℝ) (hr:0 ≤ r)(hz:∀ᶠ i in l, ‖x' i‖≤ r*‖x i‖): Sized P x' := (Crop.smul hx hr).mono hz
lemma map [NormedSpace ℝ E][NormedSpace ℝ F](hx:Sized P x) (L:E →L[ℝ] F): Sized P (fun i=>L (x i)):= hx.done ‖L‖ (norm_nonneg _) (Eventually.of_forall fun _=> L.le_opNorm _)
lemma bilinear [NormedSpace ℝ E][NormedSpace ℝ F][NormedSpace ℝ G](hx:Sized P x)(hy:Sized P x')(L:E→L[ℝ] F→L[ℝ] G): Sized P (fun i=> L (x i) (x' i)):= ((Crop.multiply hx hy (Eventually.of_forall fun _=> norm_nonneg _)).smul (norm_nonneg L)).mono (Eventually.of_forall (fun _=> (L.le_opNorm₂ ..).trans_eq (mul_assoc ..)))
end Sized
namespace Prize
lemma mono (hx:Prize P x)(hy:∀ᶠ i in l, ‖x' i‖≤‖x i‖): Prize P x' := Cut.mono hx hy
lemma arrival (hx:Prize P x): Tendsto x l (𝓝 0):= tendsto_zero_iff_norm_tendsto_zero.mpr (Cut.arrival hx (Eventually.of_forall (fun _=> norm_nonneg _)))
lemma size (hx:Prize P x):Sized P x:= Cut.crop hx
lemma empty : Prize P (fun _=> (0:E)):= Cut.nil (P:=P) |>.mono (Eventually.of_forall (fun _=> (norm_zero).le)) -- infer ?
lemma fit (hx:Prize P x)(h:x=ᶠ[l] y): Prize P y := hx.mono (h.mono fun i hi=> by rw [hi])
lemma join (hx:Prize P x)(hy:Prize P y): Prize P (fun i=>x i+y i) := (Cut.join hx hy).mono (Eventually.of_forall (fun _=> norm_add_le ..))
lemma neg (hx:Prize P x) : Prize P (fun i=>-x i):= hx.mono (Eventually.of_forall fun _=> (norm_neg _).le)
lemma minus (hx:Prize P x)(hy:Prize P y): Prize P (fun i=>x i-y i) := by simp_rw [sub_eq_add_neg]; exact hx.join hy.neg
lemma done (hx:Prize P x) (r:ℝ) (hr:0 ≤ r)(hz:∀ᶠ i in l, ‖x' i‖≤ r*‖x i‖): Prize P x' := (Cut.smul hx hr).mono hz
lemma map [NormedSpace ℝ E][NormedSpace ℝ F](hx:Prize P x) (L:E →L[ℝ] F): Prize P (fun i=>L (x i)):= hx.done ‖L‖ (norm_nonneg _) (Eventually.of_forall fun _=> L.le_opNorm _)
lemma bilinear [NormedSpace ℝ E][NormedSpace ℝ F][NormedSpace ℝ G](hx:Prize P x)(hy:Sized P x')(L:E→L[ℝ] F→L[ℝ] G): Prize P (fun i=> L (x i) (x' i)):= ((Cut.multiply hx hy (Eventually.of_forall fun _=> norm_nonneg _)).smul (norm_nonneg L)).mono (Eventually.of_forall (fun _=> (L.le_opNorm₂ ..).trans_eq (mul_assoc ..)))
end Prize
namespace Fair
lemma rights (h:Fair P x y):Sized P y:= by have he := h.size.minus h.shift.size; simpa only [sub_sub_cancel] using he
lemma fit (h:Fair P x y){u v:I→E}(hx:x=ᶠ[l] u)(hy:y=ᶠ[l] v): Fair P u v:= ⟨h.size.fit hx,h.shift.fit (hx.sub hy)⟩
lemma same (h:Sized P x): Fair P x x:= ⟨h, Prize.empty.fit (Eventually.of_forall (fun _=> (sub_self _).symm))⟩
lemma fixed (x:E): Fair P (fun _=>x) (fun _=>x):= same (Sized.fixed _)
lemma flip (h:Fair P x y): Fair P y x:= ⟨h.rights,h.shift.neg.fit (Eventually.of_forall (fun _=> neg_sub ..))⟩
lemma transit (h:Fair P x y)(k:Fair P y z) : Fair P x z:= ⟨h.size,(h.shift.join k.shift).fit (Eventually.of_forall (fun _=>by abel))⟩ -- check
lemma join (h: Fair P x y) {v w:I→E}(u:Fair P v w): Fair P (fun i=>x i+v i) (fun i=>y i+w i):= ⟨h.size.join u.size, (h.shift.join u.shift).fit (Eventually.of_forall fun _=> by simp [sub_eq_add_neg]; try abel)⟩
lemma neg (h:Fair P x y) : Fair P (fun i=>-x i) (fun i=>-y i):= ⟨h.size.neg,h.shift.neg.fit (Eventually.of_forall fun _=> by simp [sub_eq_add_neg]; try abel)⟩
lemma minus (h: Fair P x y) {v w:I→E}(u:Fair P v w): Fair P (fun i=>x i-v i) (fun i=>y i-w i):= by simp_rw [sub_eq_add_neg]; exact h.join u.neg
lemma sum {J:Type*}(S:Finset J){x y:J→ I → E} (h:∀ i∈S,Fair P (x i) (y i)): Fair P (fun i=>∑ j∈S,x j i) (fun i=>∑ j∈S,y j i):= by
 induction S using Finset.induction_on with
 | empty=>simp only [sum_empty]; exact fixed _
 | insert i S hi ih=> simp_rw [sum_insert hi]; exact join (h _ (mem_insert_self ..)) (ih (fun j hj=> h j (mem_insert_of_mem hj)))
lemma both (h:Fair P x y) (a:E)(hz:Tendsto x l (𝓝 a)): Tendsto y l (𝓝 a):= by simpa only [sub_zero, Pi.sub_apply, sub_sub_cancel] using Tendsto.sub hz h.shift.arrival
section linear
variable [NormedSpace ℝ E][NormedSpace ℝ F][NormedSpace ℝ G](h:Fair P x y)
include h
lemma map (L:E→L[ℝ] F): Fair P (fun i=>L (x i)) (fun i=>L (y i)):= ⟨h.size.map _, (h.shift.map L).fit (Eventually.of_forall fun _=> map_sub ..)⟩ -- include h
lemma bilinear (h':Fair P x' y') (L:E→L[ℝ] F→L[ℝ] G): Fair P (fun i=>L (x i) (x' i)) (fun i=> L (y i) (y' i)):= by
 refine ⟨h.size.bilinear h'.size L, ?_⟩; apply ((h.shift.bilinear h'.rights L).join (h'.shift.bilinear h.size L.flip)).fit; filter_upwards with i; rw [L.flip_apply, map_sub, map_sub,_root_.sub_apply]; abel
end linear
end Fair
end YM.FormalOPE.RG10.Boardwalk
