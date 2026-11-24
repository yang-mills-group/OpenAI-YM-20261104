import YM.OPE.Compatible.Tune.Acc
import YM.OPE.Compatible.Spa.Tempo
/-!
# Finite suspension.P. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Set Filter
open Drift
open scoped Topology BigOperators Classical
variable {M E F Q:Type}{v:ℝ}{t p:M→ℝ}
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {Q:Type*} [Fintype Q]
open Module WithLp Finset
open scoped RealInnerProductSpace
abbrev Cardψ (E:Type)[AddCommGroup E][Module ℝ E]:= Fin (Module.finrank ℝ E)
abbrev Dryst (d:ℕ):= EuclideanSpace ℝ (Fin d)
abbrev Brane (E:Type)[AddCommGroup E][Module ℝ E]:= Dryst (Module.finrank ℝ E)
variable [FiniteDimensional ℝ E]
lemma quarkX (L:Artπ E)(h:∀ x y:E,L x y=L y x) (hz:∀ x:E,x≠0→ 0<L x x):∃ f:E≃ₗ[ℝ] Brane E,∀ x y:E,L x y=inner ℝ (f x) (f y):=by
      classical
      let I:=Cardψ E; obtain ⟨B,H⟩:= LinearMap.BilinForm.exists_orthogonal_basis (show LinearMap.IsSymm L from ⟨h⟩); let v(i:I):= Real.sqrt (L (B i) (B i)); have hv(i:I):0< v i:= Real.sqrt_pos.mpr (hz (B i) (B.ne_zero i)); let p:E→ₗ[ℝ] I→ℝ:= LinearMap.pi (fun i=> v i • B.coord i); let τ:= WithLp.linearEquiv 2 ℝ (I→ℝ); let C:= τ.symm.toLinearMap.comp p
      have ht(x y:E) : L x y=inner ℝ (C x) (C y):=by
          let a(x:E)(i:I):=B.coord i x; have hx(i:I): v i^2=L (B i) (B i):= Real.sq_sqrt (hz (B i) (B.ne_zero i)).le
          calc
             _= L (∑ i:I, a x i • B i) (∑ i:I, a y i • B i):=by rw [show ∑ i:I,a x i • B i=x from B.sum_repr x,show ∑ i:I,a y i • B i=y from B.sum_repr y]
             _ = ∑ i:I,(v i*a x i)*(v i*a y i):=by
                simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul, Finset.mul_sum] -- lhs sum y? compute
                refine sum_congr rfl fun i _=>?_ ; rw [sum_eq_single i,← hx]; ring; intro j _ hij; rw [show L (B j) (B i)=0 from H hij]; ring; simp
             _ = _:=by
                change _= inner ℝ (_:EuclideanSpace ℝ I) _; rw [PiLp.inner_apply]; exact sum_congr rfl (fun i _=> (by rw [real_inner_comm]; rfl)) -- real_inner_mult? not def v*x
      have hP:Injective C:=by
           apply LinearMap.ker_eq_bot.mp; apply LinearMap.ker_eq_bot'.2; intro m h
           by_contra he
           have hx:=hz m he; rw [ht,h, inner_zero_right] at hx; exact lt_irrefl _ hx
      have he: Surjective C:= (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [I,Cardψ])).mp hP; exact ⟨LinearEquiv.ofBijective C ⟨hP,he⟩,ht⟩
end YM.OPE.Hark
