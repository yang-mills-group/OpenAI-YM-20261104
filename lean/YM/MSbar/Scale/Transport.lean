import YM.MSbar.Symbol.Azimuth
/-! ODE on the ray. Use divided difference operators for arbitrary degree. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Scale.Flight
open Function Filter Metric Set Complex Symbol
open scoped Topology ContDiff BigOperators Classical
abbrev Vec:= ℝ → ℂ
abbrev Great (x:Vec):Prop:= x.HasTemperateGrowth
variable {f g : Vec} {a:ℂ} {i n:ℕ} {s:ℝ} (hf:Great f)(hg:Great g)

-- sign convention scale k (not length)
def flight (a:ℂ)(f:Vec)(t:ℝ):= a*f t - (t:ℂ)*deriv f t
def higher (f:Vec)(t:ℝ):=(t:ℂ)*f t
@[simp] lemma at_zero (a:ℂ)(f:Vec): flight a f 0=a*f 0:=by simp [flight]
include hf
omit hf in
lemma great_cast : Great (fun x:ℝ=>(x:ℂ)):= Complex.ofRealCLM.hasTemperateGrowth
lemma go : Great (flight a f):= ((HasTemperateGrowth.const a).mul hf).sub (great_cast.mul (deriv_tame_ray hf))
lemma taller : Great (higher f):= great_cast.mul hf
include hg
lemma add : flight a (f+g)= flight a f+flight a g:=funext fun t=> by simp [flight,deriv_add (hf.1.differentiable (by simp) _) (hg.1.differentiable (by simp) _)]; ring
lemma sub : flight a (f-g)= flight a f-flight a g:=funext fun t=> by simp [flight,deriv_sub (hf.1.differentiable (by simp) _) (hg.1.differentiable (by simp) _)]; ring
omit hg
lemma scale (b:ℂ): flight a (b • f)= b • flight a f:=by
    funext x; change a*(b*_)-_*deriv (fun t:ℝ=> b*f t) x=_
    rw [deriv_const_mul _ (hf.1.differentiable (by simp) _)];simp [flight]; ring
omit hf in
@[simp] lemma higher_lower (s:ℝ)(x:Vec): strip x s * (s:ℂ)= x s-x 0 := by rw [mul_comm]; exact roll x -- WARNING omit
@[simp] lemma up : flight a (higher f)= higher (flight (a-1) f):=by
    funext t; unfold flight higher; rw [deriv_fun_mul (great_cast.1.differentiable (by simp) _) (hf.1.differentiable (by simp) _),show deriv (fun x:ℝ=>(x:ℂ)) t=1 from Complex.ofRealCLM.hasDerivAt.deriv]; ring
omit hf in
private lemma strip_id (x:Vec): x=higher (strip x)+(fun _=>x 0):=funext fun s=> by simp only [higher,Pi.add_apply,mul_comm (↑s:ℂ), show strip x s * (s:ℂ)=x s-x 0 from (by rw [mul_comm]; exact roll x)]; ring
lemma zip : strip (flight a f)=flight (a-1) (strip f):=by
    have hz: Great (strip f):= strip_tame_ray hf; have hc:= go (a:=a) hf
    have he(t:ℝ): (t:ℂ)*flight (a-1) (strip f) t=flight a f t-flight a f 0:=by
       rw [show (t:ℂ)*_=higher (flight (a-1) (strip f)) t from rfl,← up hz]; let c:Vec:= fun _=>f 0
       calc _ = flight a (higher (strip f)+c) t- flight a c t:= by rw [Flight.add (taller hz) (HasTemperateGrowth.const _),Pi.add_apply, add_sub_cancel_right]
            _ = _ :=by rw [show higher (strip f)+c= f from (strip_id _).symm]; simp [c,flight]
    have h(x:ℝ)(hx:x≠0): strip (flight a f) x=flight (a-1) (strip f) x:= mul_left_cancel₀ (ofReal_ne_zero.mpr hx) ((show (x:ℂ)*_=flight a f x-flight a f 0 from roll _).trans (he x).symm)
    funext z; by_cases hv:z=0
    swap; exact h _ hv
    subst z; apply tendsto_nhds_unique (l:=𝓝[≠] (0:ℝ)) ((strip_tame_ray hc).1.continuous.continuousWithinAt (x:=0));exact ((go (a:=a-1) hz).1.continuous.continuousWithinAt (x:=0)).congr' (eventuallyEq_iff_exists_mem.mpr ⟨{0}ᶜ,self_mem_nhdsWithin,fun x hx=> (h x hx).symm⟩)
lemma drop (i:ℕ): layer i (flight a f)=flight (a-i) (layer i f):=by
    induction i with
    | zero=> simp
    | succ i ih=> rw [layer_next,ih,zip (layer_tame_ray i hf),layer_next,Nat.cast_add,Nat.cast_one,sub_add_eq_sub_sub]
omit hf in
@[simp] lemma blank (a:ℂ): flight a 0=0:=by funext x; simp [flight]
omit hf in
@[simp] lemma across (a b:ℂ): flight a (fun _=>b)= (fun _=>a*b):=by funext x; simp [flight]
end YM.MSbar.Scale.Flight
