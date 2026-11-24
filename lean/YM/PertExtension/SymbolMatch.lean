import YM.PertExtension.SymbolWindow

/-! Whole-space Maxwell band comparison for frequency samples on the Wilson top torus. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace YM.PertExtension.LatticePT.Band
open MeasureTheory Measure Filter Maxwell Next Next.Rank Next.Rank.Radian Topology Analysis Asymptotics Set Real Metric Lattice Beamer Atlas Normal Perch Wall CellsInt Prayer RG
open Function Finset
open scoped ContDiff Topology BigOperators Classical NNReal FourierTransform RealInnerProductSpace
local notation "𝑒" => Real.exp
local notation "ℑ" => Complex.I
open Angular
variable {G : Gauge}(a b:Degree G)

def torch (v : ℝ×E4) := (tensor a b (0,v.2) * (Maxwell.normal:ℝ)) * ((𝑒 (-‖v.1•v.2‖^2):ℝ):ℂ) / ((‖v.2‖^2:ℝ):ℂ)
lemma torch_smooth : Smooth (torch a b):=by
   intro q h; have ht:=h.2
   let f (v:ℝ×E4):= tensor a b (0,v.2)
   have h:= ContDiff.prodMk (contDiff_const (c:= (0:ℝ))) (contDiff_snd : ContDiff ℝ ∞ (Prod.snd (α:=ℝ) (β:=E4)))
   have he : ContDiff ℝ ∞ f:= (tensor_smooth a b).comp h
   have hb : ContDiffAt ℝ ∞ (fun q:ℝ×E4=> (‖q.2‖^2)⁻¹ *𝑒 (-‖q.1•q.2‖^2)) q:=by
      have hh : ‖q.2‖^2≠(0:ℝ):= pow_ne_zero 2 (norm_ne_zero_iff.mpr ht)
      exact (((contDiff_norm_sq ℝ).comp contDiff_snd).contDiffAt.inv hh).mul ((((contDiff_norm_sq ℝ).comp polar_nice).neg.exp).contDiffAt)
   simp_rw [show torch a b=(fun q:ℝ×E4=> ((((‖q.2‖^2)⁻¹ *𝑒 (-‖q.1•q.2‖^2):ℝ)):ℂ) * (f q * (Maxwell.normal:ℝ))) from by funext v; unfold torch;change (f v*_) * _ / _= _;push_cast; ring_nf]
   exact (Complex.ofRealCLM.contDiff.contDiffAt.comp q hb).mul (he.mul contDiff_const).contDiffAt

def litHeat := HeatP 1 (origin a) (origin b)
lemma candle (r : ℝ) (hr:0<r)(x:E4)(hx:x≠0)(i j):
  press [i,j] (liturgy 1) (r • x)= pipeM i j (0,x) * ((Maxwell.normal:ℝ)*𝑒 (-‖r • x‖^2) / (‖x‖^2:ℝ)) :=by
  have h(z : Axis): chirp z (r • x)=(r:ℂ)*chirp z x:=by unfold chirp;change _ * (((r*x z):ℝ):ℂ)= _;push_cast;ring
  have ht: ‖r • x‖^2=r^2*‖x‖^2:= by rw [norm_smul,Real.norm_of_nonneg hr.le,mul_pow]
  rw [show press _ _ _=chirp i (r • x)*(chirp j (r • x)*liturgy 1 (r • x)) from rfl, pipe_origin,h,h,liturgy,ht]
  unfold major; rw [ht]; push_cast
  have hr':(r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne';have hx':(‖x‖:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx); field_simp [hr',hx']

lemma ceremony (r : ℝ)(hr:0<r)(x)(hx:x∈opened):litHeat a b (r • x)=torch a b (r,x):=by
  unfold litHeat HeatP torch tensor raypath paints feather origin
  split_ifs <;> simp [candle r hr x hx,RCLike.real_smul_eq_coe_smul (K:=ℂ)] <;> ring
lemma torch_eq (x) : sight a b (0,x)= torch a b (0,x):= by
  unfold sight torch;rw [show polarPoint (0,x)=0 from zero_smul ℝ _,hood_zero,origin_mass];simp_rw [zero_smul,one_mul,norm_zero, zero_pow (by omega : 2≠0),neg_zero, Real.exp_zero]
  unfold Maxwell.normal
  have hp :(Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  push_cast; field_simp; ring

def heatModel : Model (litHeat a b) 0 where
    drawing := torch a b
    nice:=torch_smooth a b
    sees r x hr h := (by simpa using ceremony a b r hr x h)

def difModel : Model (shell a b-litHeat a b) 0 where
    drawing := sight a b - torch a b
    nice z hz:=(sight_nice a b z hz).sub (torch_smooth a b z hz)
    sees r x hr h:= by rw [Pi.sub_apply,(shellModel a b).sees r x hr h,(heatModel a b).sees r x hr h]; simp only [pow_zero,one_smul];rfl

set_option linter.unusedVariables false in
theorem profile (n : ℕ) : ∃ c,Window (shell a b) 2 c n 1 a b:=by
    obtain ⟨c,hc⟩:= (shellModel a b).cast n 2
    obtain ⟨p,hp⟩:= (difModel a b).cast_vanishing (fun x hx=> by change sight a b (0,x)-torch a b (0,x)=0;rw [torch_eq];exact sub_self _) n 1
    -- meas directly as quotient of continuous cutoff before using class
    refine ⟨c+p, by linarith only [hc.positive,hp.positive],fun z hz=>by rw [shell,hood_away (by exact_mod_cast hz),zero_mul,zero_div],?_,?_,hc.coin (le_add_of_nonneg_right hp.positive), hp.coin (le_add_of_nonneg_left hc.positive)⟩
    · unfold shell; rw [show location 0=0 from Finset.sum_eq_zero fun i _=> by rw [show ‖increment i 0‖^2=0 from by rw [increment,teleports];simp]]; simp; linarith only [hc.positive,hp.positive]
    have h i : Continuous (increment i):= (tune _).continuous
    refine (Measurable.div ?_ (Complex.ofRealCLM.continuous.measurable.comp ((show Continuous location from continuous_finsetSum Finset.univ (fun i hi=>(h i).norm.pow _)).measurable)))
    apply Measurable.mul hood_smooth.continuous.measurable (Continuous.measurable ?_)
    unfold raw origin paints feather; split_ifs <;> first | exact continuous_const | change Continuous _
    all_goals dsimp only; have he(i j) := (show Continuous (pipe i j) from (h i).neg.mul ((h j).comp continuous_neg)); repeat first | exact he _ _ | exact continuous_const | apply Continuous.sub | apply Continuous.add | apply Continuous.neg | apply Continuous.mul | apply Continuous.smul | apply he | exact continuous_const

end YM.PertExtension.LatticePT.Band
