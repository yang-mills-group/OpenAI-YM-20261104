import YM.MS.Garment.Lemming
/-!
# Shape/price of Wick ingredients

No relation between regulators in appearance. Short horizon positivity and
 projections along Shot φ. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Garment.Wick
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps
open Momentum Metric City Color
open scoped Topology ContDiff
open Complex (I)
variable (G:Gauge) (s:ℝ){m n:ℕ}{A C: Type}[Fintype A][DecidableEq A]
lemma rainbow (K:YMflow A): ∀ k:G.El, Transport (dye k) (Landau.choir K id) (Landau.choir K id):= by
    intro k t a b; let X:=(dye (P:=Momentum A) (D:=A) k); let T:= Landau.choir (C:=G.ColorIndex) K id;
    change (if a.2=b.2 then K a.1 b.1 t else (0:ℂ))= ∑ u:Leg A G.ColorIndex,∑ v,T u v t* X.fieldC u a * X.fieldC v b; rw [Fintype.sum_prod_type] -- outer once
    have h (q:Atom A)(p:G.ColorIndex) : ∑ i:Leg A G.ColorIndex,T (q,p) i t*X.fieldC (q,p) a * X.fieldC i b=K q b.1 t* X.fieldC (q,p) a*wc k p b.2 := by rw [Fintype.sum_prod_type]; simp only [T,X,dye,Landau.choir,mul_ite,ite_mul,mul_zero,zero_mul, id_eq]; simp
    simp_rw [h]; rw [Finset.sum_eq_single a.1]; unfold X dye; simp only [if_true,mul_assoc, ← Finset.mul_sum,Native.Paint.forward]; split <;> simp [*]; · intro i _ hi; simp [X,dye,hi]
    simp
-- price using ready Meter at native1
lemma heatK : rPrice (A0 G 0):= by
    intro m i j; obtain he:= line_meter (S:= Arc.path (0:UScale Unit)) (a:=phaseDiff _) (fun _ => le_rfl) (fun _=>le_rfl) i j; convert he.std using 1; · ext; simp [A0]
    ext; simp [Arc.path]
lemma heatB : rPrice (B0 G 0):=by
    intro m i j; obtain he:= lap_meter (S:= Arc.path (0:UScale Unit)) (a:=phaseDiff _) (fun _=>le_rfl) (fun _=>le_rfl) i j; convert he.std using 1; · ext; simp [B0]
    ext; simp [Arc.path]
lemma fectL : rPrice (L0' G s):= by
    -- derive point d by B scaling, then use loadC and uniform.
    intro m i j; obtain ht:= heatB G m i j; let F:= B0 G 0 m i j; let u:= (3-(wfield i:ℂ)-wfield j); let W:= Bench.Forest.patch F u
    have he x p: W p x=B0 G p m i j x:= congr_fun (congr_fun (congr_fun (congr_fun (pB G p) m) i) j) x
    let V:=Bench.Forest.loadC F u; have hL : L0' G s m i j=Bench.Forest.patch V u s:= funext (fun x=> by obtain h:=Bench.Forest.patch_d ((railto ht).smooth ()) u x s; rw [funext (he x)] at h; exact (trigger G s m i j x).unique h)
    dsimp only; rw [hL]; exact fastline (Bench.Forest.unrent (Bench.Forest.rails_f' ht u) u s) (⟨s,mem_closedBall_self zero_le_one⟩:Trail0 s)
lemma A_caps : Knot true (A0 G s):= ⟨pA G s ▸ priced1 (heatK G) 4 s, mat1 ..⟩
lemma B_caps: Knot true (B0 G s):= ⟨pB G s ▸ priced1 (heatB G) 3 s, genB ..⟩
lemma C_caps: Knot true (L0' G s):= ⟨fectL G s, genL ..⟩
lemma count_caps: Priced (Q G) where
   solid n i j:= by
       obtain he:= send_cost (S:=Arc.path (0:UScale Unit)) (a:=phaseDiff _) (fun _=> le_rfl) (fun _=>le_rfl) i j
       convert he.std using 1; rfl; ext; simp
lemma vex_caps : BeamR (B0 G) (L0' G s) s:= by obtain hx:= trigger G s; rw [show B0 G=(fun t=>pulse 3 t (B0 G 0)) from funext fun t=> (pB G t).symm]; apply horizonR 3 (heatB G) (by simpa only [pB] using hx)
end YM.MS.Garment.Wick
