import YM.AllOrder.Fire.Health
/-!
# Tapes form a commutative single-coupling algebra
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Fire
open Function Finset Laplace.SigmaP PositionX.Jet PertExtension PertExtension.Series PositionX.Gauss Radial MeasureTheory Response Module
open scoped Topology ContDiff BigOperators Classical
variable {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X] (x:X)
variable {u v w:Book X}
local infix:65 "+#" => alters
private def leaf (x:X) (u:Book X):PowerSeries ℝ := PowerSeries.mk (swap u x)
omit [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X] in
lemma write_co (x:X)(u v:Book X) : leaf x (u +# v)=leaf x u*leaf x v:= by unfold leaf; ext n; rw [PowerSeries.coeff_mk]; rfl
omit [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X] in
lemma unique {u v:Book X}(h:∀ x,leaf x u=leaf x v):u=v:= by
 funext i x; have he:=congr_arg (PowerSeries.coeff i) (h x); unfold leaf at he; simp only [PowerSeries.coeff_mk,swap] at he; exact he
omit [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X] in
lemma associate (u v w:Book X):(u+#v) +# w=u +# (v+#w):= unique (fun x=>by simp_rw [write_co,mul_assoc])
omit [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X] in
lemma commute (u v:Book X):u+#v=v+#u:=unique (fun x=>by simp_rw [write_co,mul_comm (leaf x u)])
local notation "D"=>wirings (X:=X) (fun _=> 1)
omit [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X] in
lemma oneC (u:Book X):D+#u=u := funext fun i=> funext fun x=> (congr_fun (exact_scale 1 (swap u x)) i).trans (one_smul ℝ (u i x))
omit [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X] in
lemma leafN (x:X)(u:Book X)(h:u 0 x≠0):leaf x u ≠0:= fun hh=> h (by convert (congr_arg (PowerSeries.coeff 0) hh) using 1; unfold leaf;simp; rw [map_zero])
omit [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X] in
lemma colI {u v w: Book X} (h:∀ x,u 0 x ≠ 0)(hh:u+#v=u+#w):v=w:=by apply unique; intro x; exact mul_left_cancel₀ (leafN x u (h x)) (by rw [← write_co,hh,write_co])
omit [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X] in
lemma aligned (u v:Book X)(n:ℕ): (u+#v) n=∑ i∈ range (n+1), u i * v (n-i):= funext fun x=> (plus_real u v x n).trans ((Finset.sum_apply x (range (n+1)) (fun i=>u i * v (n-i))).symm)
omit [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X] in
lemma alt_add (u v w:Book X): u+#(v+w)= (u+#v)+(u+#w):= by funext i; simp only [aligned,Pi.add_apply,mul_add,Finset.sum_add_distrib]
omit [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X] in
lemma alt_smul (u v:Book X)(x:ℝ): (u+#(x•v))=x•(u+#v):= by funext i; simp only [aligned, Pi.smul_apply, mul_smul_comm, Finset.smul_sum]
omit [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X] in
lemma alt_sum {ι:Type*}(u:ι→Book X)(s:Finset ι)(v:Book X):v+# (∑ i∈s,u i) =∑ i∈s,(v+# u i):=by induction s using Finset.induction_on with
   | empty=> simp only [Finset.sum_empty]; funext n; simp only [aligned,Pi.zero_apply, mul_zero, Finset.sum_const_zero]
   | insert a s hi ih=> rw [sum_insert hi,sum_insert hi,alt_add,ih]
section diff
def Clear (u:Book X): Prop:= ∀ i,Plausible (u i)
omit [FiniteDimensional ℝ X] in
lemma Clear.add [FiniteDimensional ℝ X]  (h:Clear u)(hh:Clear v):Clear (u+v):=fun i=> (h i).add (hh i)
omit [FiniteDimensional ℝ X] in
lemma Clear.charge [FiniteDimensional ℝ X]  (h:Clear u)(t:ℝ):Clear (t•u):=fun i=> (h i).scale t
omit [FiniteDimensional ℝ X] in
lemma Clear.prod [FiniteDimensional ℝ X]  (h:Clear u)(H:Clear v):Clear (u+#v):= fun i=> (aligned u v i).symm ▸ (Plausible.sum (fun j _=>(h j).mul (H _)))
omit [FiniteDimensional ℝ X] in
lemma Clear.sum [FiniteDimensional ℝ X]  {ι:Type*}(s:Finset ι){u:ι→Book X}(h:∀ i∈s,Clear (u i)):Clear (∑ i∈s,u i):=by intro i;rw [Finset.sum_apply];exact Plausible.sum fun j hj=> h _ hj i
def slope (x:X)(u:Book X)(i:ℕ): X→ℝ:= diff' x (u i)
lemma Clear.step (h:Clear u) : Clear (slope x u):= fun i=> (h i).ds x
lemma combine (h:Clear u)(hh:Clear v) : slope x (u+#v)=(slope x u+# v)+(u+# slope x v) := by
 funext i; unfold slope; simp_rw [Pi.add_apply,aligned]; rw [tout (Finset.range (i+1)) (fun j _=>(h j).mul (hh (i-j))) x, ← sum_add_distrib]; refine Finset.sum_congr rfl fun i _=> ?_; exact mults (h _) (hh _) x -- order
lemma collect (t:ℝ)(h:Clear u): slope x (t • u)= t • slope x u:= by funext i; rw [slope, Pi.smul_apply]; exact scalars (h i) t x
lemma totals {ι:Type*}(s:Finset ι){u:ι→Book X}(h:∀ i∈s,Clear (u i)): slope x (∑ i∈s,u i)=∑ i∈s,slope x (u i):= by funext i; rw [slope,Finset.sum_apply,Finset.sum_apply]; exact tout _ (fun j hj=> h j hj _) _
lemma slope_rate (h:Clear u) (n:ℕ): slope x (energy u (n+1))= ((n+1:ℕ):ℝ) • ((slope x u) +# energy u n):= by
  induction n with
  | zero=> rw [powered, level,oneC, Nat.zero_add,Nat.cast_one,one_smul,commute, oneC]
  | succ n ih=>
    rw [powered u (n+1), combine x (square_p h _) h, ih, commute (_•_), alt_smul, commute u (slope x u +# energy u n), associate, ← powered, commute (energy u (n+1))]; simp [add_smul]
end diff
end YM.AllOrder.Fire
