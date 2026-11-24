import YM.MS.ScaleForest.Sway
/-!
# Budgets, from retained log length to *all* scales for separated points

Seek smooth-momentum polynomial price bounds on a common complex aperture and uniformly in BOTH the
cutoff and the admissible parameters of the configuration. All analytic
properties here are real estimates; need actual `Waves` holomorphicity and
continuity in `Waves` next. Two-regime leverage, minus s is UV; plus s
will allow the proof of IR limit at the indicated dimensions. Carry co-moving normalization
explicitly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect Tone Momentum Osc Fiddle Metric
open scoped Topology ContDiff
variable {G : Gauge} {I J E F : Type}
   [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
   {a b x y R : ℝ} {v : I→ℝ}

abbrev Curtain (G : Gauge) (I : Type) := ℂ→ℝ→I→Mob G

variable {X Y : Curtain G I}

def Enough (R:ℝ) := 0<R ∧ R ≤ 1/4
namespace Enough
lemma norm (h : Enough R) {z:ℂ}(he:z∈disc R) : ‖z‖≤1 / 4 := (mem_ball_zero_iff.mp he).le.trans h.2
lemma town (h : Enough R): disc R⊆ Town:= by
   intro i hi; change 0< 2*i.re+1; nlinarith [Complex.abs_re_le_norm i,h.norm hi, neg_abs_le i.re]
lemma top (h : Enough R): (0:ℂ)∈disc R:= Metric.mem_ball_self h.1
lemma pair (h : Enough a) (he : Enough b): Enough (min a b):= ⟨lt_min h.1 he.1,(min_le_left ..).trans h.2⟩
lemma simple : Enough (1/4) := ⟨by norm_num,le_rfl⟩
end Enough

def levy (a b t:ℝ) : ℝ:= if t≤0 then exp (a*t) else exp (-b*t)
lemma ulev (a b :ℝ) {s:ℝ}(hs : s ≤ 0) : levy a b s=exp (a*s):= if_pos hs
lemma ilev (a b :ℝ) {s:ℝ}(hs : 0 ≤ s) : levy a b s=exp (-b*s):= by
   unfold levy; split; · congr 1; have hz:s=0:=le_antisymm (by assumption) hs; rw [hz,mul_zero,mul_zero]
   rfl
lemma posLevy (a b s:ℝ): 0< levy a b s:= by unfold levy; split <;> positivity
lemma levy_mul (a b x y s:ℝ) : levy a b s*levy x y s=levy (a+x) (b+y) s := by
   rcases le_total s 0 with h|h
   · simp only [ulev _ _ h]; rw [← Real.exp_add]; ring_nf
   simp only [ilev _ _ h]; rw [← Real.exp_add]; ring_nf
lemma levy_mono (ha : a ≤ b) (hx : x ≤ y) (s : ℝ): levy b y s ≤ levy a x s := by
   unfold levy; split
   · exact exp_monotone (mul_le_mul_of_nonpos_right ha (by assumption))
   rename_i h; exact exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg hx) (le_of_not_ge h))
theorem contin_levy (a b :ℝ): Continuous (levy a b) := by
   unfold levy; apply Continuous.if_le (by fun_prop) (by fun_prop) (f := fun x:ℝ=>x) (g:=fun _:ℝ=> (0:ℝ)) continuous_id continuous_const
   intro s hs; rw [hs]; ring_nf

/-- Unrestricted cost along all common tests, in particular in neighborhoods.
This is phrased with generic reindexing. -/
def OnTest (F:Curtain G I)(a:J→ℝ)(q:J→disc R)(s:J→ℝ)(v:J→I): Prop := fell 0 a (fun i=> F (q i) (s i) (v i))
def Envelope (R a b:ℝ)(F:Curtain G I) : Prop:=∀ (J:Type) (q:J→disc R) (s:J→ℝ) (v:J→I), OnTest F (fun i=> levy a b (s i)) q s v

theorem cheapRestrict {F:I→ Mob G}{X:I→ℝ}{S T:Set I}(h : fell 0 (S.restrict X) (S.restrict F))(he : T⊆ S) : fell 0 (T.restrict X) (T.restrict F) := price_shift h (fun i:T=> (⟨ (i:I),he i.property⟩:S))

/-- Paste two (not necessarily topologically closed) pieces in a COST
calculation. This pasting does not allow inferring cost by just knowing the
value on the common boundary. -/
theorem assemble {F:I→ Mob G}{X:I→ℝ}{S T:Set I}(hS:fell 0 (S.restrict X) (S.restrict F))
   (hT:fell 0 (T.restrict X) (T.restrict F))(he:∀ i:I,i∈S∨i∈T): fell 0 X F := by
   intro m E _ _ _ w; obtain hF:= hS m E w; obtain hv:= hT m E w
   apply Arc.hike
   · intro i; rcases he i with h|h
     exacts [hF.smooth (⟨i,h⟩:S),hv.smooth (⟨i,h⟩:T)]
   intro j; obtain ⟨C,hC,k,hk⟩:= Arc.ride hF j; obtain ⟨D,hD,v,hv'⟩:= Arc.ride hv j
   refine ⟨ C+D,by positivity,k+v,fun i p=>?_⟩
   rcases he i with h|h
   · refine (hk (⟨i,h⟩:S) p).trans ?_; have ht:X i≥0:=znon hS ⟨i,h⟩; simp only [Pi.zero_apply,Set.restrict,abs_zero,add_zero,one_mul]; gcongr <;> first | linarith | positivity | simp
   refine (hv' (⟨i,h⟩:T) p).trans ?_; have ht:X i≥0:= znon hT ⟨i,h⟩; simp only [Pi.zero_apply,Set.restrict,abs_zero,add_zero,one_mul]; gcongr <;> first | linarith | positivity | simp

namespace Envelope
variable (h : Envelope R a b X)
include h
lemma uprice (q:J→disc R) {s:J→ℝ}(he:∀ i,s i ≤ 0)(v:J→I): OnTest X (fun i=> exp (a*s i)) q s v:= by
   simp_rw [← ulev a b (he _)]; exact h J q s v
lemma iprice (q:J→disc R) {s:J→ℝ}(he:∀ i,0 ≤ s i)(v:J→I): OnTest X (fun i=> exp (-b*s i)) q s v:= by simp_rw [← ilev a b (he _)]; exact h J q s v
lemma relax (hx:x≤a)(hy:y≤b) : Envelope R x y X := fun _ q s v=> pay_price (b:=fun i=> levy x y (s i)) (h _ q s v) zero_lt_one (by simpa only [one_mul] using fun i=> levy_mono hx hy (s i))
lemma shrink (hx:x≤R): Envelope x a b X:= fun _ q s v=> h _ (fun i=>(⟨(q i).val,Metric.ball_subset_ball hx (q i).property⟩:disc R)) s v
lemma vicinity [TopologicalSpace J] {s:J→ℝ}(he:Continuous s)(q:J→disc R)(v:J→I): Vicinity (fun i=> X (q i) (s i) (v i)) := by
   intro x; let W(i:J):= levy a b (s i); let C:=1+W x; have hC : 0<C:=by have hh : 0<W x:= posLevy ..; unfold C; positivity
   let T:= {i:J|W i<C}; refine ⟨ T,?_ ,pay_price (price_shift (h _ q s v) (Subtype.val (p:=fun i=>i∈T))) hC (fun i=> ?_)⟩
   · exact ((contin_levy a b).comp he|>.tendsto x).eventually (gt_mem_nhds (show W x<C from by simp [C] ))
   simp only [Pi.one_apply,mul_one]; exact le_of_lt (show W i.val<C from i.property)
lemma fin_price {p:ℂ} (he:p∈ disc R)(s:ℝ)(q:I): kPrice (X p s q):= Rock.fee (h _ (fun _:Unit=> (⟨p,he⟩:disc R)) (fun _=>s) (fun _=>q)) ()
omit h
lemma zero (R a b:ℝ) : Envelope R a b (0:Curtain G I):= fun _ _ s _=> fall_zero (fun i=>(posLevy a b (s i)).le)
lemma paste (hS : ∀ (J:Type)(q:J→disc R) (s:J→ℝ) (v:J→I), (∀ i,s i ≤ 0)→ OnTest X (fun i=> exp (a*s i)) q s v)
   (hT : ∀ (J:Type)(q:J→disc R) (s:J→ℝ) (v:J→I), (∀ i,0 ≤ s i)→ OnTest X (fun i=> exp (-b*s i)) q s v) : Envelope R a b X := by
   intro J q s v; let S := {x:J| s x≤0}; let T:= {x:J| 0≤s x}
   apply assemble (S:=S) (T:=T) ?_ ?_ (fun i=> le_total (s i) _)
   · unfold Set.restrict; simp_rw [show ∀ i:S, levy a b (s i.val)= _ from fun i=> ulev a b (show s i.val ≤ 0 from i.property)]; exact hS (↥S) (S.restrict q) (S.restrict s) (S.restrict v) (fun i=> i.property)
   unfold Set.restrict; simp_rw [show ∀ i:T, levy a b (s i.val)= _ from fun i=> ilev a b (show 0≤s i.val from i.property)]; exact hT (↥T) (T.restrict q) (T.restrict s) (T.restrict v) (fun i=> i.property)
include h
lemma add (he : Envelope R a b Y) : Envelope R a b (X+Y) := fun _ q s v=> fall_add (h _ q s v) (he _ q s v)
lemma parity (c:ℂ): Envelope R a b (c • X) := by
   intro J q s v; unfold OnTest; simp_rw [Pi.smul_apply]; convert! fall_scale (U:=fun _:J=>c) (h _ q s v) (const_sc (z:= (0:UScale J)) _) using 1; simp
end Envelope
end YM.MS.ScaleForest
