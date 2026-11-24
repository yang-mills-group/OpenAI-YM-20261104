import YM.XSpace.Laurel
/-! # Simultaneous proper rotations averaged smooth support (using no choice of frame from calibration)

Construct by Gram variables. Actually all improper ones too.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Rose
open Function Set Filter MeasureTheory Trace Graph3 Angle Season
open scoped Topology ContDiff BigOperators InnerProductSpace RealInnerProductSpace
variable {X: Points 3} (c:Shade.Cut)
abbrev Sim (V:E4 ≃ₗᵢ[ℝ] E4) (p:Points 3) := points (V ∘ p.ofLp)
def Turns {T:Type}(t:Points 3→T) := ∀ (V:E4 ≃ₗᵢ[ℝ] E4) (p:Points 3), t (Sim V p) = t p
variable (T:ℝ)
local notation "C"=> T*θs⁻¹
local notation "P3"=> Points 3
local notation "A"=> θs
def Gram (x:P3): ℝ:= ‖x 0-C • x 2‖^2+‖x 1‖^2+(‖x 2‖^2- A^2)^2
lemma evokes : Turns (Gram T):=fun V p=> by unfold Gram Sim; simp only [points_apply,comp_apply,← map_smul,← map_sub, V.norm_map]
lemma gin : ContDiff ℝ ∞ (Gram T):=by
  have he(i: Fin 3): ContDiff ℝ ∞ (fun x:Points 3=> x i):= (PiLp.proj (𝕜:=ℝ) 2 (fun _:Fin 3=>E4) i).contDiff
  exact ((((he 0).sub ((he 2).const_smul (T*θs⁻¹))).norm_sq ℝ).add ((he 1).norm_sq ℝ)).add ((((he 2).norm_sq ℝ).sub contDiff_const).pow 2)
def Booth (R:ℝ): Set P3:={x|Gram T x≤R}
lemma leis (R:ℝ): IsClosed (Booth T R):= isClosed_le (gin _).continuous continuous_const
-- proper (small level suffices)
lemma cage : IsCompact (Booth T 1):=by
  let c:=‖C‖; let d:=(1+c*6)+1+6; have hc: 0≤c:=norm_nonneg _; have hd:0<d:=by unfold d; positivity
  refine (isCompact_closedBall (0:P3) d).of_isClosed_subset (leis ..) (fun i hi=>?_); rw [Metric.mem_closedBall, dist_zero_right]; change Gram T i≤1 at hi; let x:=i 0; let y:=i 1; let z:=i 2; let w:=‖x-C • z‖; change w^2+‖y‖^2+(‖z‖^2-(5:ℝ)^2)^2≤1 at hi
  have hh:z=z:= rfl; have h1:‖z‖≤6:=by
    have hl: ‖z‖^2-(5:ℝ)^2≤1:= by nlinarith [sq_nonneg w, sq_nonneg ‖y‖]
    nlinarith
  have h2:‖y‖≤1:= by nlinarith [sq_nonneg w,sq_nonneg (‖z‖^2-(5:ℝ)^2)]
  have h3:‖x‖≤1+c*6:= calc
    _ ≤ w+c*‖z‖:=by unfold w c; rw [← norm_smul]; exact norm_le_norm_sub_add ..
    _ ≤ _:= add_le_add (by nlinarith [sq_nonneg ‖y‖,sq_nonneg (‖z‖^2-(5:ℝ)^2)]) (mul_le_mul_of_nonneg_left h1 hc)
  apply le_of_sq_le_sq ?_ hd.le; rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]; change ‖x‖^2 + ‖y‖^2 + ‖z‖^2 ≤ _; unfold d; nlinarith [norm_nonneg x,norm_nonneg y,norm_nonneg z]

def here (u:E4) : P3:= points (Graph3.trip (T • u) 0 (A • u))
lemma entry (u:E4)(h:‖u‖=1): Gram T (here T u)=0:=by
  unfold Gram here; simp only [points_apply, peg₀,peg₁,peg₂,smul_smul]; rw [show T*A⁻¹*A=T from by simp [θs],sphere_len h (show 0≤A by norm_num [θs])]; simp
lemma mirror (x:P3): Gram T x=0↔∃ u:E4,‖u‖=1∧ here T u=x:=by
  refine ⟨fun h=>?_, fun ⟨u,hu,e⟩=> e ▸ entry T u hu⟩; let u:= x 2; let v:= x 0-C • u; let z:=A⁻¹ • u; change ‖v‖^2+‖x 1‖^2+(‖u‖^2-A^2)^2=0 at h; have hh:= (add_eq_zero_iff_of_nonneg (show 0≤ ‖v‖^2+_ from by positivity) (show 0≤ (‖u‖^2-A^2)^2 by positivity)).mp h; have hp:0<A:=by norm_num [θs]
  have hu: ‖u‖=A:= (sq_eq_sq₀ (norm_nonneg _) hp.le).1 (sub_eq_zero.mp (sq_eq_zero_iff.mp hh.2))
  have he:v=0:= norm_eq_zero.mp (by nlinarith [hh.1,sq_nonneg ‖x 1‖]); have hy : x 1=0:= norm_eq_zero.mp (by nlinarith [hh.1,sq_nonneg ‖v‖]); refine ⟨z,?_,?_⟩
  · unfold z; rw [norm_smul,Real.norm_of_nonneg (by positivity:0≤A⁻¹),hu,inv_mul_cancel₀ hp.ne']
  apply PiLp.ext; intro i; fin_cases i; · rw [here,points_apply]; exact (mul_smul ..).symm.trans (sub_eq_zero.mp he).symm
  · rw [here,points_apply]; exact hy.symm
  rw [here,points_apply]; exact smul_inv_smul₀ hp.ne' u
lemma small_ball {K:Set P3}(hK:IsOpen K)(h:∀ u:E4,‖u‖=1→ here T u ∈ K):∃ a:ℝ,0<a ∧ a≤1 ∧ Booth T a ⊆ K:=by
  let G:=Booth T 1∩ Kᶜ; by_cases p: G.Nonempty
  · obtain ⟨x,hx,H⟩:= ((cage T).inter_right hK.isClosed_compl).exists_isMinOn (f:=Gram T) p (gin T).continuous.continuousOn; have hz:= (show x∈Booth T 1∩ Kᶜ from hx); have he: 0< Gram T x:= by
      apply lt_of_le_of_ne (by unfold Gram; positivity); intro e; obtain ⟨u,hu,X⟩:= (mirror T x).1 e.symm; exact hz.2 (show x∈K from X ▸ h u hu)
    refine ⟨Gram T x/2, half_pos he, le_trans (half_le_self he.le) hz.1, fun i hi=>?_⟩; by_contra! hp; change Gram T i≤Gram T x/2 at hi; have hh : Gram T x≤1:=hz.1; have ht: Gram T x≤ Gram T i:= H (show i∈G from ⟨le_trans hi (by change _≤1; linarith),hp⟩); linarith
  exact ⟨1,one_pos,le_refl _,sdiff_eq_empty.mp (show Booth T 1\K=∅ from Set.not_nonempty_iff_eq_empty.mp p)⟩ -- lemma
lemma imaging {K:Set P3}(h: IsOpen K)(hx:∀ u:E4,‖u‖=1→ here T u∈ K): ∃ φ:P3→ℝ,(∀ t,0≤φ t)∧φ (here T (basis 0))=1 ∧ ContDiff ℝ ∞ φ∧HasCompactSupport φ ∧ Turns φ ∧ tsupport φ ⊆ K:=by
  obtain ⟨a,ha,hA,h⟩:= small_ball T h hx; let f:ContDiffBump (0:ℝ):=⟨a/2,a, half_pos ha, half_lt_self ha⟩; let φ:= f ∘ Gram T; have ht: tsupport φ⊆Booth T a:= by apply closure_minimal _ (leis ..); intro x hx; have hx': Gram T x∈ Metric.ball (0:ℝ) a:= f.support_eq ▸ hx; change Gram T x≤a; exact (le_abs_self _).trans (mem_ball_zero_iff.mp hx').le
  refine ⟨φ,fun i=> f.nonneg,show _=_ from ?_,f.contDiff.comp (gin T), (cage T).of_isClosed_subset (isClosed_tsupport _) (ht.trans (show Booth T a⊆ _ from fun x hx=>(show Gram T x≤ a from hx).trans hA)),fun X i=> congr_arg f (evokes T X i), ht.trans h⟩; unfold φ comp; rw [entry T _ (basis_norm _)]; exact f.one_of_mem_closedBall (Metric.mem_closedBall.mpr (by rw [dist_self]; exact f.rIn_pos.le))
end YM.XSpace.Rose
