import YM.OPE.Compatible.Bowman.Aten
/-! # Functional rada constant across histories. quantitative factor.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Votive
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Flume Flume.Script Frequency
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Y Z:Type}{G:Gauge}{n c:Side}{S:StepData c c}{p q:Clip}{R T:PathData G} {P:Patch}{K:KernelChoices}{V:ChartRatio G} {i j t r m:ℕ} {s s' u α T₁ T₂ b b' d U ℓ:ℝ}{B:Sponsor G} {H:Seasons B}
namespace Alps
open Page Planned.PrimaryIntegral295.Carrier
-- well engineering two
abbrev lemmaCov : Bin 1≃ Cover where
    toFun p:= stepOut p 0
    invFun i:=lace 1 (fun _=>i)
    left_inv p:=by unfold stepOut; ext ⟨j,i⟩; fin_cases j; rfl
    right_inv i:=rfl
variable (w:G.ColorIndex)
def costWorld (a b:Axis)(q:Script (Shade G) 2):ℝ:= Flume.well (Script.crop q (fun _=>(b,w))) (tasting [(0,a),(0,a)])
lemma coinWhat (a b:Axis)(hv:a < b)(A:Alps B H i ℓ)(h:4 ≤ i) : costWorld w a b (inkV A.live A.clip 2)= -2:=by
    let P:= inkV A.live A.clip 2; let L:List (Flume.Keys 1):= [(0,a),(0,a)]; let F:=Script.crop P fun _=> (b,w); let T(p:Bin 1):= F p * tasting L (translit p)
    change ∑' p,T p=_; rw [← lemmaCov.symm.tsum_eq T, ← fundamental a b hv B.K A.gear h]; refine tsum_congr (fun x=>?_); let j: Bin 1 := lemmaCov.symm x; let p:= wreath 1 (0,j); let Q:Page (Shade G) 2:= syn p (fun _=> (b,w))
    have he: Q.primary=0:=header ..; have hz:(Q 1).1=x:=by change stepOut (wreath 1 (0,j)) (Fin.succ 0)=x; erw [flowPart 0 j (0: Fin 1), zero_add]; rfl
    have hp: F j=A.root (coord b) (coord b) x:=by change inkV A.live A.clip 2 Q=_; rw [A.textReal h Q he,if_pos (show (Q 0).2.2=(Q 1).2.2 from rfl),hz];rfl
    change F j*_= _; rw [hp]; apply congr_arg; change ((x a:ℝ)*((x a:ℝ)*1):ℝ)=(x a:ℝ)^2; ring
lemma world_low (a b:Axis)(q:Script (Shade G) 2)(hp:q.Poll 3): costWorld w a b q=0:=hp _ _ (by simp)
lemma world_budget (a b:Axis)(h:2≤m)(p:Script (Shade G) 2)(hp:soot m p d): ‖costWorld w a b p‖ ≤ d:=by
    let A:= Script.crop p (fun _=> (b,w)); have he:=crops hp fun _=> (b,w); let L:List (Flume.Keys 1):= [(0,a),(0,a)]; let F(v:Bin 1):= A v*tasting L (translit v); have hz :Summable F:= gardens (flavor_part L m (show L.length≤m from h)) he
    have hm(v:Bin 1): ‖F v‖ ≤ poise m v*‖A v‖:=by unfold F; rw [norm_mul,mul_comm ‖A v‖]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply (tasting_bill L v).trans; change (size v:ℝ)^L.length ≤ (notch v:ℝ)^m; exact le_trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (Nat.le_add_left (size v) 1)) L.length) (pow_le_pow_right₀ (show 1≤ (notch v:ℝ) by exact_mod_cast notch_one v) h)
    exact (norm_tsum_le_tsum_norm hz.norm).trans ((hz.norm.tsum_le_tsum hm he.2.1).trans he.2.2)
lemma wscale (a b:Axis)(p:Script (Shade G) 2)(u:ℝ): costWorld w a b (u • p)=u*costWorld w a b p:=wellScale (Script.crop p (fun _=> (b,w))) u _
lemma wcount (a b:Axis){p q:Script (Shade G) 2}(hp:folk p)(hQ:folk q): costWorld w a b (p+q)=costWorld w a b p+costWorld w a b q:=by
   have he(z:Script (Shade G) 2)(h:folk z):Summable (fun i=> Script.crop z (fun _=> (b,w)) i*tasting [(0,a),(0,a)] (translit i)):= gardens (flavor_part _ 2 (by simp)) (crops (h 2).choose_spec _)
   unfold costWorld Flume.well; rw [← Summable.tsum_add (he p hp) (he q hQ)]; apply tsum_congr; intro i; rw [show Script.crop (p+q) _ i=Script.crop p (fun _=> (b,w)) i+Script.crop q (fun _=> (b,w)) i from rfl, add_mul]
lemma wdep (a b:Axis) {p q:Script (Shade G) 2}(hp:folk p)(he:folk q): costWorld w a b (p-q)=costWorld w a b p-costWorld w a b q:=by rw [sub_eq_add_neg,show -q=(-1:ℝ)• q by simp,wcount w a b hp (folkS he (-1:ℝ)), wscale]; ring
end Alps
end YM.OPE.Votive
