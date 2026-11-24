import YM.MSbar.Scale.Past
/-! Resolution along each ray. Keep epsilon-coordinate power pole; no MS subtraction inside the
scale endpoint (including resonance). -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Scale.Flight
open Function Filter Metric Set Complex Symbol MeasureTheory
open scoped Topology ContDiff BigOperators Classical
variable {f g:Vec}{a:ℂ}{n i:ℕ} {s: ℝ}

def rollout : ℕ→ℂ→Vec→Vec
    | 0,a,h=> past a h
    | n+1,a,h=> higher (rollout n (a-1) (strip h)) + fun _=> h 0 / a
-- use all degrees; only one potential resonance
lemma layer_strip : layer (i+1) f=layer i (strip f):= iterate_succ_apply ..
def Approved (a:ℂ)(f:Vec):Prop:= ∀ i:ℕ,a=↑i → layer i f 0=0
variable (h:Approved a f) (he: Great f)
include h
lemma goes_down : Approved (a-1) (strip f):= fun i hi=> by
    have hp: a=((i+1:ℕ):ℂ):=by push_cast; rw [sub_eq_iff_eq_add] at hi; exact hi
    rw [← layer_strip]; exact h _ hp
omit h
include he
lemma direct (hX:Land (a-n)): Great (rollout n a f):= by
    induction n generalizing a f with
    | zero=> exact growth he (by simpa using hX)
    | succ n ih=> exact (taller (ih (strip_tame_ray he) (show Land (a-1-n) by rw [← sub_add_eq_sub_sub,add_comm (1:ℂ)]; simpa using hX))).add (HasTemperateGrowth.const _)
lemma range_approved : Approved a (flight a f):= by intro i hi; rw [drop he,hi]; simp
include h
lemma solves (hL:Land (a-n)) : flight a (rollout n a f)= f:=by
   induction n generalizing a f with
   | zero=> exact solve_right he (by simpa using hL)
   | succ n ih =>
       have hN : Land (a-1-n):= by rw [← sub_add_eq_sub_sub,add_comm (1:ℂ)]; simpa using hL
       have hf:= strip_tame_ray he; have hc:= direct hf hN
       rw [rollout,add (taller hc) (HasTemperateGrowth.const _),up hc, ih (goes_down h) hf hN, across]
       funext t; change (t:ℂ)*_+a*_= _; rw [show (t:ℂ)*_ = f t-f 0 from roll f]
       rcases eq_or_ne a 0 with rfl|hv; rw [show f 0=0 from h 0 (by simp),div_zero]; ring; field_simp; ring
-- uniqueness out of all smooth-on-rays functions (only prove temperate version)
lemma unique (hv: flight a f=0) (hN:Land (a-n)): f=0:= by
    induction n generalizing a f with
    | zero => replace hN: Land a:=by simpa using hN
              rw [← solve_left he hN,hv]; ext x; simp [past]
    | succ n ih=>
       have heq := ih (goes_down h) (strip_tame_ray he) (by rw [← zip he,hv,strip_zero]) (by rw [← sub_add_eq_sub_sub,add_comm (1:ℂ)]; simpa using hN)
       have hz: f 0=0:= by
          rcases eq_or_ne a 0 with rfl|he'; exact h 0 (by simp); exact (mul_eq_zero.mp ((at_zero a f).symm.trans (congr_fun hv 0))).resolve_left he'
       funext t; exact (eq_of_sub_eq_zero (by have H:= roll (t:=t) f; simpa [heq,hz] using H.symm)) -- goal maybe
omit h
lemma approve {b:ℂ}: strip (higher f+fun _=>b)= f:=by -- replace constant generic
   have hh:=(taller he).add (HasTemperateGrowth.const (b)); let g:=higher f +fun _=>b;
   have ht(y:ℝ)(hy:y≠0): strip g y= f y:=by
       apply smul_right_injective ℂ hy; dsimp only; rw [roll]; simp [g,higher]
   funext x; by_cases hv:x=0; swap; exact ht x hv
   subst x; apply tendsto_nhds_unique (l:=𝓝[≠] (0:ℝ)) (show ContinuousWithinAt (strip g) {(0:ℝ)}ᶜ 0 from (strip_tame_ray hh).1.continuous.continuousWithinAt);exact he.1.continuous.continuousWithinAt.congr' (eventuallyEq_iff_exists_mem.mpr ⟨{0}ᶜ,self_mem_nhdsWithin,fun x hx=> (ht x hx).symm⟩)
lemma normalization (hx:Land (a-n)): Approved a (rollout n a f):= by
    induction n generalizing a f with
    | zero=> intro i hi; simp only [Land,hi,natCast_re,Nat.cast_zero,sub_re,zero_re] at hx; linarith [show (0:ℝ) ≤ (i:ℝ) from Nat.cast_nonneg i]
    | succ n ih=> intro i hi; cases i with
                  | zero=>rw [hi, Nat.cast_zero]; simp [rollout,higher]
                  | succ i=>
                      have hN: Land (a-1-n):= by rw [← sub_add_eq_sub_sub,add_comm (1:ℂ)]; simpa using hx
                      let y:= rollout n (a-1) (strip f); have ht:=ih (strip_tame_ray he) hN i (by rw [hi]; push_cast; ring)
                      rw [layer_strip,rollout,approve (b:=f 0/a) (direct (strip_tame_ray he) hN)]; exact ht
end YM.MSbar.Scale.Flight
