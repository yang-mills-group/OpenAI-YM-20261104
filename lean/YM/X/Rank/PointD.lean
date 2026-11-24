import YM.X.Rank.Lens
/-!
Polynomial partial integration for the **free** bilocal test. Color-separated notation.
Arbitrary site arguments of additional single curvature probes kept real.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PositionX.Rank
open Function Set Filter Maxwell Wick Maxwell.Free Next.Rank.Normal MvPolynomial Finsupp Rad
open scoped Topology BigOperators Classical
variable {G : Gauge}(c k i: G.ColorIndex) {j l : ℕ}

abbrev Scout := E4 × Flavor 0
def torch (x : Scout)(k:G.ColorIndex): Canvas G := pluck x.1 (pen k x.2)
def pay (w : Scout) (z : Stroke) := if z.1=w.1 then (0:ℝ) else fare c (ax z.2.1 z.2.2) w.2 (z.1-w.1)
def hot (a b : Scout) := if a.1=b.1 then 0 else (fare c a.2 b.2 (a.1-b.1):ℂ)
def dip (f : Stroke→ℂ) (k:G.ColorIndex) (x:Fiber G): ℂ:= if x.2=k then f x.1 else 0
def cost (a : Scout): Fiber G → ℂ := dip (fun z=> ↑(pay c a z)) k
def bill (x:E4)(w : Flavor 0)(f : Stroke→ℂ) : ℂ := ∑ y, ↑((ax 0).coord y w)* f (x,⟨0,y⟩)

lemma torch_formula (w : Scout) : torch w k=∑ y, C (↑((ax 0).coord y w.2) : ℂ)*X ((w.1,⟨0,y⟩),k) := by
  rcases w with ⟨x,w⟩; unfold torch; dsimp only; unfold pluck pen; simp only [LinearMap.coe_mk,AddHom.coe_mk,map_sum, map_mul, rename_X,rename_C]
lemma torch_linear (x : E4): ∃ L: Flavor 0 →ₗ[ℝ] Canvas G, ∀ w, torch (x,w) k=L w:=⟨((pluck x).toLinearMap.restrictScalars ℝ).comp (pen k),fun _=>rfl⟩
lemma cost_ax (x:E4) (w: Ax 0): cost c k (x,ax 0 w)=(weft c).cov ((x,⟨0,w⟩),k) := by
  funext v; rw [Next.Rank.Normal.Symmetric.symm]; rfl
lemma cost_sum (u:Scout) : cost c k u= ∑ y, (↑((ax 0).coord y u.2):ℂ) • (weft c).cov ((u.1,⟨0,y⟩),k) := by
  funext v
  simp only [Finset.sum_apply,Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ (w : Ax 0), (weft c).cov ((u.1,⟨0,w⟩),k) v = _ from fun w=>(weft c).symm ((u.1,⟨0,w⟩),k) v]
  unfold cost pay dip
  by_cases h : v.2=k
  · rw [if_pos h]; simp only [weft,h,↓reduceIte]; unfold scov; dsimp only
    split_ifs with he
    · simp
    conv_lhs => arg 1; rw [← fare_pair c _ _ (sub_ne_zero.mpr he)]; rhs; rw [← (ax 0).sum_repr u.2]
    simp only [_root_.map_sum,map_smul,smul_eq_mul,Complex.ofReal_sum,Complex.ofReal_mul]; rfl
  rw [if_neg h]; simp [weft,h]

lemma slit_scales {V:Type*}(p : poly V)(z:ℂ)(u:V→ℂ) : slit (z • u) p=C z* slit u p:=by rw [slit_smul,C_mul']
lemma slit_total {V ι:Type*}(p:poly V)(s:Finset ι)(u:ι→V→ℂ): slit (∑ i∈s,u i) p=∑ i∈s, slit (u i) p:= by
  induction s using Finset.induction_on with
  | empty => simp [slit_zero]
  | @insert i s hi ih => simp only [Finset.sum_insert hi,slit_linear,ih]
lemma bill_pay (a b:Scout) : bill b.1 b.2 (fun z=> (pay c a z:ℂ))=hot c b a := by
  unfold bill pay hot; dsimp only; by_cases hx:b.1=a.1
  · simp [hx]
  simp_rw [if_neg hx, ← fare_pair c _ _ (sub_ne_zero.mpr hx)]; conv_rhs => arg 1; lhs; rhs; rw [←(ax 0).sum_repr b.2]
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,Complex.ofReal_sum,Complex.ofReal_mul]; rfl
lemma hot_symm (a b:Scout):hot c a b=hot c b a := by
  unfold hot; by_cases h:a.1=b.1
  · simp [h]
  rw [if_neg h,if_neg (Ne.symm h)]; exact congr_arg (fun x:ℝ=>(x:ℂ)) (K_symmetric (flavor (G:=G) 0 c a.2) (flavor (G:=G) 0 c b.2) h)
lemma slit_torch (f:Stroke→ℂ) (a:Scout): slit (dip f k) (torch a i)= C (if i=k then bill a.1 a.2 f else 0) := by
  rw [torch_formula]; by_cases h:i=k
  · simp only [C_mul',_root_.map_sum, Derivation.map_smul, slit_X, dip,h,↓reduceIte,bill, _root_.map_mul]
  simp [C_mul',_root_.map_sum,slit_X,dip,h]
lemma slit_cost (a b:Scout): slit (cost c k a) (torch b i)=C (if i=k then hot c b a else 0) := by rw [cost, slit_torch, bill_pay]
lemma leg_reads (x: Scout)(p:Canvas G): E c (torch x k * p)= E c (slit (cost c k x) p) := by
  rw [torch_formula, cost_sum, slit_total, Finset.sum_mul]; simp_rw [_root_.map_sum]; apply Finset.sum_congr rfl
  intro i _; rw [slit_smul,mul_assoc,C_mul',map_smul,map_smul]; apply congr_arg; rw [E,Next.Rank.Normal.blended,Pi.zero_apply,zero_mul,zero_add]
def patch (a b:Scout):Canvas G := ∑ i:G.ColorIndex,torch a i * torch b i
lemma patch_comm (a b:Scout): patch (G:=G) a b=patch b a:= Finset.sum_congr rfl fun i _=> mul_comm (torch a i) _
lemma patch_eq (a:Scout)(w:Flavor 0) : patch (G:=G) a (a.1,w)=prim a.1 (team G a.2 w) := by rw [patch,team, _root_.map_sum]; refine Finset.sum_congr rfl ?_; intro i _; rw [_root_.map_mul, prim,AlgHom.comp_apply,AlgHom.comp_apply,paint_bit,paint_bit];rfl
lemma second_reads (a:Scout)(p:Canvas G): E c (patch a a * p) = ∑ i:G.ColorIndex,E c (slit (cost c i a) (slit (cost c i a) p)) := by
  rw [patch, Finset.sum_mul,_root_.map_sum]; refine Finset.sum_congr rfl ?_; intro i _; rw [mul_assoc,leg_reads, Derivation.leibniz, slit_cost]
  simp only [hot,↓reduceIte, smul_eq_mul,C_0,mul_zero,add_zero]; rw [leg_reads]
end YM.PositionX.Rank
