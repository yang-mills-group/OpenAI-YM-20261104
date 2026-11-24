import YM.GradedFar.Fork
import YM.OPE.Mountains.Payout
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Fork
open Function Finset Filter Set OPE OPE.Arboreal Table OPE.Log Node
open scoped Topology BigOperators Classical
variable {I J:Type} [Fintype I] [Fintype J]
variable {G:Gauge}{L:Register G}
def load (p:Node I J→L.Token):ℕ := ∑i,(p (leaf i)).1
def premium (p:Node I J→L.Token):ℕ := ∑ j,(p (far j)).1
def mass (p:Node I J→L.Token)(r t:ℝ):ℝ := r^(load p)*t^(premium p)

theorem innerdeg (p:Node I J→L.Token):sigma (Arboreal.crop p (near I J))=load p:=by
  rw [sigma_set];simp [near,load]
theorem outerdeg (p:Node I J→L.Token)(a:L.Token):sigma (Arboreal.crop (update p child a) (outer I J))=a.1+premium p:=by
  rw [sigma_set];simp [outer,broad,premium]
theorem fee (p:Node I J→L.Token)(r t:ℝ)(n:ℕ):
    (tree I J).fee p (radius r t) (tree I J).leaves (tree I J).root n=mass p r t/t^n:=by
  rw [Arboreal.fee,Arboreal.rent,leaves,Finset.prod_union]
  · simp [mass,load,premium,near,broad,tree,radius,Finset.prod_pow_eq_pow_sum]
  rw [Finset.disjoint_left]; intro u; cases u <;> simp [near,broad]
omit [Fintype I] [Fintype J] in
theorem prestige (r t:ℝ): Arboreal.prestige (tree I J) (radius r t)=badge t*badge r:=by
  simp [Arboreal.prestige,tree,radius,badge]
omit [Fintype I] [Fintype J] in
theorem ratio (r t:ℝ):(tree I J).ratioAt (radius r t) child=r/t:=rfl
end YM.Integration.GradedFar.Fork
