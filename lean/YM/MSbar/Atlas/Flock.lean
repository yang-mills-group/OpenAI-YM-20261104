import YM.MSbar.Atlas.Epoch
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath.Stock
open Lattice Wilson RG Function Filter MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{c f n':Side}{n:ℕ}{S:StepData c f}
open Precision Tree Pressure Push Push.AbsoluteSums ConnectedActivityE6 Push.Uniform
open Heath Bulk Finset
variable (P:Patch)(K:KernelChoices)(J:Voice G) (A B:Stage)(s:Palisade) (G0:Gauge)
set_option quotPrecheck false
local notation "L"=> P.L
local notation "Ξ"=> tip G L
-- bound output ankel term: x * lowNeed with v allowed x^-1/2 log. near variance. λ etc.

def ySp (b:Stage)(x:ℝ) (v t : ℝ) := ((t)*lowNeed b.clip (radiusB x) b.paths b.width v +
   (t*(b.paths*(temp x)^3+b.paths*(temp x)^4)+(lbt x)*(temp x)^2)*(2*Real.exp (b.width*8)*(81*meter b.width))) + ability x*(2*Real.exp (b.supportExponent*10))*((2*((4:ℝ)*radiusB x+2)+1)^4*meter b.supportExponent)+(9:ℝ)^4
def yCover (P:Patch)(J:Voice G)(A:Stage)(x:ℝ) := ySp A x (base J (tip G P.L x)) (8*tip G P.L x)
lemma firing (x : ℝ){R:Rep G n'} (h:FaceValue A x R) (v:ℝ): ankle R.p R.clip A.width A.paths (ability x) (lbt x) v 1 R.beta=ySp A x v R.beta:=by
    unfold ankle ash RG.PathData.loopsPrice life ySp; rw [h.size,h.support,h.clip,h.threshold]; ring
lemma heating (x:ℝ)(h:1<x)(v Y W:ℝ)(he:Y≤W): ySp A x v Y ≤ ySp A x v W:=by
    have hp :0 ≤ temp x:=mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.exp_pos _).le
    unfold ySp; have hM:=meter_pos A.width_pos; have hh:=A.paths_pos; have hz:0≤lowNeed A.clip (radiusB x) A.paths A.width v:=by unfold lowNeed; have h1:= A.clip.quadratic_pos; have h2:=meter_pos (half_pos A.width_pos); positivity
    gcongr
-- Beam estimate. Push `x` above by 8*Ξ.Rate.Any.
lemma deco : Beam G L (yCover P J A):=by
    let z:=Ξ; let b:= fun x=>8*z x
    let v x:=base J (z x); let c:=A.paths
    let r:=A.width;have hr:=A.width_pos
    let y (x:ℝ):=(radiusB x:ℝ); have hY:Beam G L y:=Beam.rare ..; have hN:=Beam.logfine G L
    let T x:= (2*y x+1)^4; let E:=A.clip.direct/2+c^2/2
    have ht:Beam G L T:= (((Beam.coin 2).mul hY).add (Beam.coin 1)).power 4
    have he:Beam G L (fun x=> b x*v x^2):=by
       let u:=8*J.C*shade G; let k:=8*u^2; let f x:= k*(Real.log (z x))^4; have hf: Beam G L f:= (Beam.coin k).mul (hN.power _); apply hf.lower; filter_upwards [Delay.shift_pos G L] with x hx
       apply le_of_eq; apply congr_arg; have h:((z x)^(-(1/2:ℝ)))^ (2:ℕ) * z x=1:=by rw [Real.rpow_neg (show 0≤ z x from hx.le), ←Real.sqrt_eq_rpow, inv_pow, Real.sq_sqrt hx.le, inv_mul_cancel₀ hx.ne']
       unfold b v base skies distance f k u
       linear_combination (norm:=ring) (8*(8*J.C*shade G)^2*Real.log (z x)^4)*h
    let H x:= b x* T x*(A.clip.direct*v x^2/2+(A.paths*v x)^2/2)
    have hF:Beam G L H:= ((ht.mul he).mul (Beam.coin E)).lower (Eventually.of_forall fun x=> by apply le_of_eq; apply congr_arg; unfold H E c; ring)
    have hC:Rate G L 1 b:= Rate.hat.mul_left _
    have hx : Pole G L fun x=> Real.exp (-r/2*(radiusB x:ℝ)):=by
        intro i; refine loose G ((Pole.first G (r/2) (half_pos hr) i).congr (?_)) L; exact Eventually.of_forall fun x=>congr_arg Real.exp (by rw [neg_div])
    have hP : Beam G L fun x=> Real.exp (-r/2*(radiusB x:ℝ))*b x := Beam.lax (hx.mul hC (-1)) neg_one_lt_zero
    have hp : Beam G L fun x=> b x * lowNeed A.clip (radiusB x) c A.width (v x):= (((hF.add (hP.mul (Beam.coin ((c*4)*(c*2)*(81*meter (r/2)))))).mul (Beam.coin (Fintype.card PlaqAxes:ℝ)))).lower (Eventually.of_forall fun x=> by apply le_of_eq; apply congr_arg; unfold H T y lowNeed r c; ring)
    let u x:= temp x
    have hy := macroG G L;have hI:Rate G L 0 (lbt):=(microG G L).mul_left _
    have hv:= hC.mul ((hy.pow 3).mul_left c); have ha:= hC.mul ((hy.pow 4).mul_left c); have hb : Beam G L fun x=> b x*(A.paths*u x^3+A.paths*u x^4) := ((Beam.lax hv (by norm_num)).add (Beam.lax ha (by norm_num))).lower (Eventually.of_forall fun x=>by unfold c u; rw [mul_add])
    have hf := (Beam.lax (hI.mul (hy.pow 2)) (by norm_num))
    have hQ :Beam G L ability:= Beam.lax (loose G (a:=-(11/10)) ((ability_rate G ⟨1,one_pos⟩).congr (Eventually.of_forall fun x=>by simp [tip,betaF])) L) (by norm_num)
    let K x:=(2*(4*y x+2)+1)^ (4:ℕ); have hs: Beam G L K:= (((Beam.coin 2).mul (((Beam.coin 4).mul hY).add (Beam.coin 2))).add (Beam.coin 1)).power 4
    exact ((hp.add ((hb.add hf).mul (Beam.coin _))).add ((hQ.mul (Beam.coin _)).mul (hs.mul (Beam.coin _)))).add (Beam.coin _)
end YM.MSbar.Heath.Stock
