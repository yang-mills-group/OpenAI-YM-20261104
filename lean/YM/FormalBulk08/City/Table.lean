import YM.FormalBulk08.City.Door

/-! Ward shaft when no unit-cell wrap (internal proof only eventually atTop). -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.City
open Reef Lattice Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries
open Stationary hiding Rays
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

variable (i : G.ColorIndex) (x : Site n)

-- step orientation toll
def rowD {m : Type} (x : m×TypeFace 1×hue G) (b : hue G) : m×TypeFace 1×hue G:=(x.1,x.2.1,b)
def localCoord (v : wire G n) := Sum.map (rowD v) (id:Unit→Unit)
def deltaS (z : Rays (dah (wire G n))) (v : wire G n):=
   if v.1=x then curtain i true (z ∘ localCoord v) v.2.2
   else if v.1+step (axisEquiv.symm v.2.1)=x then curtain i false (z ∘ localCoord v) v.2.2
   else z (.inl v)
def glow (z : Rays (dah (wire G n))) (p : Site n):=if p=x then lantern i (z (.inr ())) else 1

lemma delta_home : deltaS i x 0=0:= by funext j; unfold deltaS; split_ifs <;> first|exact congr_fun (curtain_home ..) _|rfl
lemma localCoord_cap (v : wire G n) (s: WithTop ℕ∞) : ContDiffAt ℝ s (fun z:Rays (dah (wire G n))=> z ∘ localCoord v) 0:= contDiffAt_pi.mpr fun _=>contDiffAt_apply ..
lemma delta_cap : ContDiffAt ℝ ω (deltaS i x) 0 := by
    refine contDiffAt_pi.mpr fun v=>?_ ; unfold deltaS;
    by_cases he:v.1=x
    · simp_rw [if_pos he]; exact (contDiffAt_pi.mp (curtain_diff i true) v.2.2).comp (f:=fun z:Rays (dah (wire G n))=> z ∘ localCoord v) 0 (localCoord_cap v _)
    by_cases hp:v.1+step (axisEquiv.symm v.2.1)=x
    · simp_rw [if_neg he,if_pos hp]; exact (contDiffAt_pi.mp (curtain_diff i false) v.2.2).comp (f:=fun z:Rays (dah (wire G n))=> z ∘ localCoord v) 0 (localCoord_cap v _)
    simp_rw [if_neg he,if_neg hp]; exact contDiffAt_apply ..
lemma glow_cap : Army (glow i x) 0 := by
   intro v;unfold glow;by_cases he:v=x
   · simp_rw [if_pos he]; exact (G.exp_jet.comp (f:=fun z:Rays (dah (wire G n))=> z (.inr ()) • moon G (dotI i)) (by fun_prop)).contDiffAt
   simp_rw [if_neg he]; exact contDiffAt_const
lemma post_delta (v : Axis) (t : Site n) (i' : hue G) (h : step v≠(0:Site n)) :
   ∀ᶠ z in 𝓝 0,input G n (deltaS i x z) (t,v) = Lattice.gauge (glow i x z) (input G n (cheekL (wire G n) z)) (t,v) := by
   let a:wire G n:= (t,coord v,i'); have H (z:Rays (dah (wire G n))) : input G n (cheekL _ z) (t,v)=G.lieExp (moon G (cheekL (hue G) (z ∘ localCoord a))) := by rw [input,represent_link]; rfl
   have hh : Tendsto (fun z:Rays (dah (wire G n))=> z ∘ localCoord a) (𝓝 0) (𝓝 0):=(localCoord_cap a ω
        ).continuousAt
   by_cases he:t=x
   · have h':¬ t+step v=x:= fun e=> h (add_left_cancel ((e.trans he.symm).trans (add_zero t).symm))
     filter_upwards [hh.eventually (go_yellow i true)] with z hz
     rw [Lattice.gauge,input,represent_link]; rw [show _= _ from H z]; simp only [glow,if_pos he,if_neg h',inv_one,mul_one]
     change G.lieExp _=yellow i true (z ∘ localCoord a); rw [←hz]
     congr 1;ext b; exact (if_pos he)
   by_cases hp:t+step v=x
   · filter_upwards [hh.eventually (go_yellow i false)] with z hz
     rw [Lattice.gauge,input,represent_link]; rw [show _= _ from H z]; simp only [glow,if_neg he,if_pos hp,one_mul]
     change G.lieExp _=yellow i false (z ∘ localCoord a); rw [←hz]
     congr 1;ext b; change deltaS _ _ _ (t,coord v,b)= _;rw [deltaS, if_neg he];change (if t+step (axisEquiv.symm _)=_ then _ else _)= _;rw [show axisEquiv.symm (coord v)=v from axisEquiv.symm_apply_apply _,if_pos hp];rfl
   refine .of_forall fun z=>?_ ; rw [Lattice.gauge,input,represent_link]; rw [show _=_ from H z]; simp only [glow,if_neg he,if_neg hp,inv_one,one_mul,mul_one];congr 1; ext b; change deltaS _ _ _ (t,coord v,b)= _; rw [deltaS,if_neg he];change (if t+step (axisEquiv.symm _)=_ then _ else _)= _;rw [show axisEquiv.symm (coord v)=v from axisEquiv.symm_apply_apply _,if_neg hp]; rfl
lemma frontTable (p : Pap (wire G n)) (h : Rite p p 1 0) (hp : ∀ v,step v≠(0:Site n)) : roam ℝ (motor (deltaS i x)) p=PowerSeries.map (MvPolynomial.rename (Sum.inl : wire G n→ dah (wire G n))).toRingHom p := by
   rw [←fit_translate]; symm
   exact h (dah (wire G n)) (cheekL (wire G n)) (deltaS i x) (glow i x) (map_zero _) (delta_home ..) ((cheekL (wire G n)).contDiff.contDiffAt) (delta_cap ..) (glow_cap i x) ⟨1,by ext b;simp [glow]⟩ (by filter_upwards [eventually_all.mpr fun v:Site n × Axis=>post_delta i x v.2 v.1 i (hp _)] with z hz; rw [pull_id]; exact funext hz)

end YM.FormalBulk08.City
