import YM.XSpace.Wicker

/-!
# Actual order-one permitting the bulk Feynman gauge (no ghosts at this order)

Expose the literal table entries for estimates against independent columns.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Feynman
open Function Set Topology Filter Module Chart2 Lattice
open scoped Topology BigOperators InnerProductSpace
variable {G:Gauge} {R:Period}
lemma lumens (A B:Fields R.side G) (c: G.ColorIndex): innerF (light c A) B= innerF A (light c B):=by unfold innerF innerT; simp_rw [slate, light_at,mag_sym]
lemma refer_light (c:G.ColorIndex)(v:RealDual (R:=R) (G:=G)): refer R (v ∘ₗ light c)=light c (refer R v):= unique (fun x=> by rw [← refer_ok,LinearMap.comp_apply,lumens (R:=R),refer_ok _ _])

def factor (R:Period) : RealDual (R:=R) (G:=G)→ₗ[ℝ] Fields R.side G:= (LinearMap.id+R.mirrorLink) ∘ₗ beamField R.side ∘ₗ refer R
lemma factor_at (v:RealDual (R:=R) (G:=G)): factor R v=beamField R.side (refer R v)+ R.mirrorLink (beamField R.side (refer R v)):= rfl
lemma legit (v:RealDual (R:=R) (G:=G)): Legit R (factor R v):=by unfold Legit; rw [factor_at,map_add, R.mirror_link_twice, add_comm (R.mirrorLink _)]
lemma factor_sym (p q:RealDual (R:=R) (G:=G)): p (factor R q)= q (factor R p):=by
  have h (v x y: Fields R.side G): innerF v (x+y)=innerF v x+innerF v y :=by simp [innerF_b, mul_add,Finset.sum_add_distrib]
  rw [refer_ok _ (factor R q), refer_ok _ (factor R p),factor_at,factor_at,h,h,← mirror_sym,reflected,← beam_sym (R.mirrorLink _)]; congr 1; rw [← beam_sym]; exact innerF_comm _ _; exact innerF_comm _ _
lemma factor_color (c: G.ColorIndex) (v: RealDual (R:=R) (G:=G)): factor R (v ∘ₗ light c)=light c (factor R v):=by rw [factor_at,factor_at,refer_light,beam_color,hues,map_add]
lemma refer_bill (A:Fields R.side G): refer R (pressure R G A) = (1/2:ℝ) • cost A :=by
  apply unique; intro x; rw [← refer_ok, press,← whole_cost]; unfold innerF innerT; simp only [slate, Pi.smul_apply,real_inner_smul_left,← Finset.mul_sum]; ring
lemma reflected_curl (A:Fields R.side G) (h: Legit R A): R.curl A = R.curl A ∘ R.reflectedFace:= by
  conv_lhs=>rw [← h]
  exact funext (R.curl_mirror A)
lemma say_ok (A:Fields R.side G) (h:Legit R A): R.curl (factor R (pressure R G A))= R.curl A:=by
  rw [factor_at,refer_bill]; simp_rw [map_add,map_smul,beam_inverse]; funext p; simp only [Pi.add_apply,Pi.smul_apply]; rw [R.curl_mirror, beam_inverse]; have he:= congr_fun (reflected_curl A h) p; simp only [Function.comp_apply] at he; rw [← he]; module

def meet (G:Gauge) (R:Period) : Meet G R := ⟨factor R,factor_color,factor_sym,legit,say_ok⟩
lemma refer_bond (p: Roller R G): refer R (reading p)= cellVec p.1 p.2 := by apply unique; intro A; rw [← refer_ok,reading_at,innerF_comm,knot]
lemma beam_single {n:Side} (x y:Site n)(i j:Axis)(c:G.ColorIndex): beamField n (cellVec (x,i) c) (y,j)= if i=j then Potential.G n (y-x) • basisC G c else 0:=by rw [beam_val]; by_cases h:i=j; subst i; simp [cellVec, Pi.single_apply, apply_ite, eq_comm]; simp [cellVec, Ne.symm h,h]

def mixed {n:Side} (x y:Edge (Site n)) (i j:G.ColorIndex):= if i=j ∧ x.2=y.2 then Potential.G n (x.1-y.1) else 0
lemma beam_read (x y:R.Bonds)(i j:G.ColorIndex): beamField R.side (cellVec y j) x i=mixed x y i j:=by
  obtain ⟨a,b⟩:=x; obtain ⟨c,d⟩:=y; unfold mixed; rw [beam_single]; simp only [basisC,EuclideanSpace.basisFun_apply]; split_ifs with H Q H <;> simp_all
lemma green_entries (i j: Roller R G): (wide (meet G R)).cov i j=
    ↑(mixed i.1 j.1 i.2 j.2-mixed (R.reflect i.1) j.1 i.2 j.2):=by
  change ((reading i (factor R (reading j)):ℝ):ℂ)=_
  rw [factor_at,reading_at,refer_bond j]; simp only [Pi.add_apply,PiLp.sub_apply, R.mirror_apply,beam_read (R:=R), ← sub_eq_add_neg]
end YM.XSpace.Feynman
