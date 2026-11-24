import YM.XSpace.CoverProjector
import YM.XSpace.Compat.Episode
/-! # Top self covariance (in finite and infinite volume) -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace
open Function Set Filter Lattice Wilson MeasureTheory Laurent Bloch Exterior Matrix
open Next.Free Precision PhysicalNext.RankCovariance Further.FreeCovariance.KP
open Further.CorrectedLift
open YM.XSpace.Compat.KP
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators ContDiff

lemma sides_up : Tendsto (fun n : Side => n.val) atTop atTop := by
  refine tendsto_atTop.2 fun m => (eventually_ge_atTop (⟨m+1,m.succ_pos⟩:Side)).mono fun n hn=>?_ ; change m+1 ≤ n.val at hn; exact (Nat.le_succ m).trans hn
lemma sides_up' : Tendsto (fun n : Side => (n.val:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp sides_up

lemma wraps_grow (x : Cover) : ∀ᶠ n : Side in atTop, lift (wrap n x)=x := by
  suffices h : ∀ i, ∀ᶠ n : Side in atTop, -(n.val : ℤ)<2*x i ∧ 2*x i ≤ n.val by
    exact (eventually_all.mpr h).mono fun n hn=> lift_eq_iff.mpr ⟨rfl,hn⟩
  intro i
  filter_upwards [sides_up.eventually_gt_atTop (2*(x i).natAbs)] with n hn
  omega

abbrev orb0 n := Episode.found 1 (Train.top 4) n

lemma point_rate (a b : X2) : ∃ J : Cover → ℂ, ∃ C : ℝ, 0≤C ∧ ∀ n : Side, ∀ x : Cover, ‖orb0 n a b x - J x‖ ≤ C*(1+‖rcast x‖)/(n.val:ℝ) := by
  obtain ⟨α,Ω,η,hα,hη,H⟩ := Episode.paid 1 one_pos le_rfl
  obtain ⟨f,hf⟩ := H (Train.top _)
  obtain ⟨C,hC,H'⟩:= lift_mesh [] [] (Ω:=Ω) hα hη a b
  refine ⟨fun x=>retract (fun p=> rebus [] [] f p a b) (rcast x),C,hC,fun n x=>?_⟩
  unfold orb0; rw [← Episode.bridge _ one_pos le_rfl hα hη _ _ hf]; exact H' ..

def Orb0 (a b:X2) := Classical.choose (point_rate a b)

lemma orb0_to (a b : X2) (x : Cover) : Tendsto (fun n=> orb0 n a b x) atTop (𝓝 (Orb0 a b x)) := by
  obtain ⟨C,hC,H⟩ := Classical.choose_spec (point_rate a b)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _=>norm_nonneg _) (fun n=> H n x) (tendsto_const_nhds.div_atTop sides_up')

variable {G : Gauge}
lemma kernel_trans {n : Side} (x y : Site n) (a b : PA) (i j : G.ColorIndex) (o : Site n) : kernel G n ((x+o,a),i) ((y+o,b),j)= kernel G n ((x,a),i) ((y,b),j) := by
  apply Complex.ofReal_inj.mp
  rw [kernel_formula, kernel_formula]; by_cases h : i=j
  · simp only [if_pos h]
    apply Episode.wraps; simp
  simp only [if_neg h]

lemma kernel_cover {n : Side} (x y : Cover) (a b : PA) (i j : G.ColorIndex) : (↑(kernel G n ((wrap n x,a),i) ((wrap n y,b),j)):ℂ)= if i=j then
    orb0 n (plaquette a) (plaquette b) (x-y) else 0 := by
  rw [kernel_formula]; by_cases h:i=j
  · simp only [if_pos h]
    apply Episode.wraps; simp
  simp only [if_neg h]

lemma differentiated (A B:List Axis) (a b:PA) (x:Cover) : Tendsto (fun n=>slot checkout B (slot checkin A (orb0 n (plaquette a) (plaquette b))) x) atTop (𝓝 (slot checkout B (slot checkin A (Orb0 (plaquette a) (plaquette b))) x)) := by
  let V n := orb0 n (plaquette a) (plaquette b); let W:= Orb0 (plaquette a) (plaquette b)
  have hC (S:Axis→(Cover→ℂ)→ Cover→ℂ) (A : List Axis)
      (h : ∀ U : Side → Cover → ℂ,∀ L : Cover → ℂ, (∀ x,Tendsto (fun n=> U n x) atTop (𝓝 (L x)))→ ∀ i x, Tendsto (fun n=> S i (U n) x) atTop (𝓝 (S i L x)))
      (U : Side → Cover → ℂ) (L : Cover → ℂ) (hu : ∀ x,Tendsto (fun n=> U n x) atTop (𝓝 (L x))) (x:Cover) : Tendsto (fun n=> slot S A (U n) x) atTop (𝓝 (slot S A L x)) := by
    induction A generalizing U L with
    | nil=>exact hu _
    | cons i A ih=> exact ih (fun n=> S i (U n)) (S i L) (h _ _ hu i)
  have hu (x) : Tendsto (fun n=>slot checkin A (V n) x) atTop (𝓝 (slot checkin A W x)):= hC checkin A (fun U L h i x=> (h (x+step i)).sub (h x)) V W (fun _=>orb0_to ..) x
  exact hC checkout B (fun U L h i x=> (h (x-step i)).sub (h x)) _ _ hu _

theorem infinite_cost (A B:List Axis) (a b:PA) : ∃ C:ℝ, 0<C ∧ ∀ x:Cover,1 ≤ ‖rcast x‖→
    ‖slot checkout B (slot checkin A (Orb0 (plaquette a) (plaquette b))) x-↑(decree A B a b (rcast x))‖ ≤ C*(‖rcast x‖^(5+A.length+B.length))⁻¹ := by
  obtain ⟨C,hC,H⟩ := Episode.per_cost 1 one_pos 4 le_rfl A B a b
  refine ⟨C,hC,fun x hx=>?_⟩; let v:= (‖rcast x‖^(5+A.length+B.length))⁻¹
  have hw : Tendsto (fun n:Side => C*(v+(1+‖rcast x‖)/n.val)) atTop (𝓝 (C*v)) := by
    nth_rw 2 [← add_zero v]; exact (tendsto_const_nhds.mul (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop sides_up')))
  exact le_of_tendsto_of_tendsto ((differentiated A B a b x).sub tendsto_const_nhds).norm hw (Eventually.of_forall fun n=> H (Train.top _) n x hx)
end YM.XSpace
