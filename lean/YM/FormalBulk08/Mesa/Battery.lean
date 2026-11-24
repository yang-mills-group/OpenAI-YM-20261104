import YM.FormalBulk08.Mesa.Why
import YM.FormalBulk08.Reef.Seed

/-! Cover seed exactly Wilson fundamental through all orders. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Mesa
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {r : ℕ} (G : Gauge)

abbrev edgeL (G : Gauge) := Biglot (Loc G 1)
abbrev So (G : Gauge):= Fin 4 × G.ColorIndex
def rowRay (u : PlaqAxes) : Fin 4 → Cover× Exterior.TypeFace 1 :=
   let x:= u.val.1; let y:=u.val.2
   ![(0,Exterior.coord x),(step x,Exterior.coord y),(step y,Exterior.coord x),(0,Exterior.coord y)]
def ashPort (u : PlaqAxes) (t : So G) : edgeL G :=((rowRay u t.1).1,(rowRay u t.1).2,t.2)
def circle (p : Jets.Rays (So G)) (i : Fin 4) := G.lieExp (WithLp.toLp 2 fun j=>p (i,j))
def tinge (p : Jets.Rays (So G)) : ℝ := G.price (circle G p 0*(circle G p 1*((circle G p 2)⁻¹*(circle G p 3)⁻¹)))
lemma tinge_diff : ContDiffAt ℝ ω (tinge G) 0 := by
   have hm (i:Fin 4) : ContDiffAt ℝ ω (fun z=> G.mat (circle G z i)) 0 := by
      let b : Jets.Rays (So G)→L[ℝ] G.Color := LinearMap.toContinuousLinearMap {toFun:=fun z=>WithLp.toLp 2 fun j=> z (i,j),map_smul':=fun _ _=> rfl,map_add':=fun _ _=> rfl}
      exact G.exp_jet.contDiffAt.comp 0 b.contDiff.contDiffAt
   refine Work.F03.price_smooth (A:=fun p:Jets.Rays (So G)=> circle G p 0*(circle G p 1*((circle G p 2)⁻¹*(circle G p 3)⁻¹))) ?_
   have hi (i:Fin 4) := ((show G.Mat≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt (x:=G.mat (circle G 0 i))).comp (0:Jets.Rays (So G)) (hm i)
   simp_rw [G.mat_mul,G.mat_inv]; exact (hm 0).mul ((hm 1).mul ((hi 2).mul (hi 3)))
lemma scuff (n : Side) (x : Site n) (u : PlaqAxes) (z : Jets.Rays (wire G n)) : G.price (faceValue (input G n z) (x,u))=tinge G (z ∘ Lotus.tint x ∘ drip n ∘ ashPort G u) := by
   unfold tinge; apply congr_arg G.price
   simp only [faceValue,square,travel, Step.pos_read,Step.neg_read,Step.vec_pos,Step.vec_neg,mul_one];
   let X:= (step u.val.1: Site n); let Y:=(step u.val.2:Site n);
   rw [show x+X+Y-X=x+Y by abel, show x+X+Y+-X-Y=x by abel]
   have he (i:Fin 4): circle G (z ∘ Lotus.tint x ∘ drip n ∘ ashPort G u) i= input G n z (wrap n (rowRay u i).1 + x,Exterior.axisEquiv.symm (rowRay u i).2) := by
       rw [input,Work.F03.represent_link]; unfold circle; rw [show Exterior.coord _= _ from Exterior.axisEquiv.apply_symm_apply _]; congr
   simp_rw [he]; simp [rowRay,add_comm,Y, show ∀ i, Exterior.axisEquiv.symm (Exterior.coord i) =i from Exterior.axisEquiv.symm_apply_apply]
lemma fundamental_funding (n : Side) : paste (fundamental G n)= ∑ i:PlaqAxes, schedules (paste (tinge G)) (ashPort G i) n := by
   let f (p:Face (Per n)) (z:Jets.Rays (wire G n)) := tinge G (z ∘ tint p.1 ∘ drip n ∘ ashPort G p.2); have hf (p:Face (Per n)) : ContDiffAt ℝ ∞ (f p) 0 := (show ContDiffAt ℝ ∞ _ _ from (tinge_diff G).of_le le_top).comp (f:=fun z: Jets.Rays (wire G n)=> z ∘ tint p.1 ∘ drip n ∘ ashPort G p.2) 0 (contDiffAt_pi.mpr fun _=>contDiffAt_apply ..)
   rw [show fundamental G n=∑ p,f p by funext z; unfold f; simp only [fundamental,Function.comp_apply,energy,Finset.sum_apply]; exact Finset.sum_congr rfl fun p _=> scuff ..,garter _ _ (fun i _=>hf i)];
   simp_rw [f,folds_byte _ (tinge G) ((tinge_diff G).of_le le_top)]; change ∑ p: Site n × PlaqAxes,_=_; rw [Fintype.sum_prod_type,Finset.sum_comm]; rfl

def Canon (G : Gauge) : Pap (So G) := - afterX (paste (tinge G)) 2
lemma emberseed (n : Side) : seed G n=∑ p: PlaqAxes,schedules (Canon G) (ashPort G p) n := by ext1 e; simp_rw [seed,Canon,schedules,map_sum,map_neg, after_one, fundamental_funding]; simp only [map_sum,schedules, coeff_map, after_one,Finset.sum_neg_distrib]
end YM.FormalBulk08.Mesa
