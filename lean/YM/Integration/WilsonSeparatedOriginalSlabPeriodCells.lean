import YM.Integration.WilsonSeparatedOriginalSlabFourierScore

/-! A compact smooth spatial test is periodically extended outside its own central cube. The localized estimates use the original derivatives. The period-cell argument is specialized from RG10Quartz.Broadcast.Lip. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonSeparatedOriginalSlabPeriodCells
open Filter MeasureTheory Function UnitAddTorus Metric Set
open scoped BigOperators Topology Classical ContDiff
abbrev Room (J:Type*) := J→ℝ
abbrev Pitch (J:Type*) := J→ℤ
variable {J:Type*}[Fintype J]{V:Room J→ℂ}{x a:Room J}{P Q r:ℝ}

def flow (P : ℝ) (z : Pitch J) : Room J := fun i=> (z i : ℤ) • P
lemma flow_exposed {v w : Pitch J} (h : v≠w) (hp : 0<P) : P ≤ dist (flow P v) (flow P w):=by
 obtain ⟨i,hi⟩:= Function.ne_iff.mp h
 apply le_trans _ (dist_le_pi_dist (flow P v) (flow P w) i)
 change P ≤ dist ((v i:ℤ) • P) ((w i:ℤ) • P); rw [dist_eq_norm, ← sub_smul,zsmul_eq_mul, norm_mul,Real.norm_eq_abs, Real.norm_eq_abs,abs_of_pos hp]
 exact le_mul_of_one_le_left hp.le (by exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hi))

def orbit (a : Room J) (r P : ℝ) (F : Room J→ℂ) (x : Room J) : ℂ := if h : ∃ z:Pitch J,dist x (a+flow P z)≤ r then F (x - flow P h.choose) else 0
lemma each (h : support V⊆ closedBall a r) (hp : P>0) (hz : Pitch J) (hr:r+Q<P) (he : dist x (a+flow P hz) ≤ Q) : orbit a r P V x= V (x-flow P hz) := by
 unfold orbit; split
 next hh=>
   rw [show hh.choose=hz from ?_]; by_contra hx;have ht:= flow_exposed hx hp; have hv:= hh.choose_spec; have hb:= dist_triangle (a+flow P hh.choose) x (a+flow P hz); rw [dist_add_left,dist_comm _ x] at hb; linarith
 next hh=>
   symm; by_contra hx; apply hh; refine ⟨hz,?_⟩; have he:= Metric.mem_closedBall.mp (h hx)
   rw [dist_eq_norm] at *; rwa [show x - (a+flow P hz)=(x-flow P hz)-a by abel]

lemma strip (P : ℝ) (u x : Room J) (hp:0<P) : ∃ z : Pitch J, dist x (u+flow P z)≤ P/2 ∧ ∀ v : Pitch J,dist x (u+flow P z) ≤ dist x (u+flow P v) := by
 let a (i:J):ℝ:= (x i-u i)/P
 let z : Pitch J := fun i=>⌈a i-1/2⌉
 have hx i: a i-1/2 ≤ (z i:ℝ) ∧ (z i:ℝ)<a i+1/2:= ⟨Int.le_ceil _,lt_of_lt_of_eq (Int.ceil_lt_add_one _) (by ring)⟩
 have ht : dist x (u+flow P z) ≤ P/2:=by
   rw [dist_pi_le_iff (by positivity)]; intro i
   rw [dist_eq_norm,Real.norm_eq_abs,abs_le,Pi.add_apply]; unfold flow
   obtain ⟨h1,h2⟩:=hx i; unfold a at *; field_simp at h1 h2; rw [zsmul_eq_mul]; constructor <;> linarith
 use z,ht; intro y
 by_cases he:y=z; · rw [he]
 have hv:= flow_exposed he hp
 have hz:= dist_triangle (u+flow P y) x (u+flow P z); rw [dist_add_left,dist_comm _ x] at hz; linarith

lemma orbits (h : support V⊆ closedBall a r) (hp:0<P) (he:r+r<P)(x:Room J) :
   (∃ z : Pitch J, dist x (a+flow P z) ≤ r ∧ orbit a r P V =ᶠ[𝓝 x] fun y=> V (y-flow P z)) ∨ orbit a r P V=ᶠ[𝓝 x] 0 := by
 obtain ⟨z,h₁,h₂⟩:= strip P a x hp
 by_cases hh:dist x (a+flow P z)≤r
 · have hu: dist x (a+flow P z)<P/2:=hh.trans_lt (by linarith)
   refine Or.inl ⟨z,hh,?_⟩; filter_upwards [isOpen_ball.mem_nhds (mem_ball.mpr hu)] with y hy; exact each h hp z (by linarith) (mem_ball.mp hy).le
 let C:= dist x (a+flow P z)
 right; filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (x:=x) (show 0 < C-r from by unfold C; linarith))] with y hy
 unfold orbit; rw [dif_neg]; rfl
 intro e; obtain ⟨u,hu⟩:=e
 have ht: C ≤ dist x (a+flow P u):= h₂ u; have he:= dist_triangle x y (a+flow P u); have hf:= mem_ball.mp hy
 rw [dist_comm] at hf; linarith
lemma round (hf:ContDiff ℝ ∞ V) (h : support V⊆ closedBall a r) (hp : 0<P) (he : r+r < P) : ContDiff ℝ ∞ (orbit a r P V):=by
 rw [contDiff_iff_contDiffAt]; intro x
 rcases orbits h hp he x with ⟨z,hz,h'⟩|ht
 · exact (hf.comp (contDiff_id.sub contDiff_const)).contDiffAt.congr_of_eventuallyEq h'
 exact (contDiff_const (c:=(0:ℂ))).contDiffAt.congr_of_eventuallyEq ht
lemma periodic (F : Room J→ℂ) (x y : Room J) (hp : 0<P) (he : r+r<P) (h : support F ⊆ closedBall a r)
   (hv:∃ z:Pitch J, x=y+ flow P z): orbit a r P F x=orbit a r P F y := by
 obtain ⟨z,rfl⟩:=hv
 obtain ⟨w,h₁,h₂⟩ := strip P a y hp -- even outside
 have hW : ∀ x y:Pitch J, flow P (x+y)=flow P x+ flow P y:=fun x y=> by funext i; change ((x i + y i):ℤ) • P = _; rw [add_smul]; rfl
 have hP : r+P/2 < P:=by linarith
 rw [each h hp (w+z) hP (by rw [hW,←add_assoc, dist_add_right]; exact h₁),each h hp w hP h₁, hW]; abel

omit [Fintype J] in
lemma loops {x y : Room J} (h : WilsonSeparatedOriginalSlabFourierOrbit.wrap x=WilsonSeparatedOriginalSlabFourierOrbit.wrap y):∃ z:Pitch J,x=y+flow 1 z:=by
 have ht i := congrFun h i
 have hh (i:J): x i-y i ∈ AddSubgroup.zmultiples (1:ℝ):= by
   apply (QuotientAddGroup.eq_zero_iff _).1
   rw [QuotientAddGroup.mk_sub,sub_eq_zero]; exact ht i
 choose z hz using fun i=> AddSubgroup.mem_zmultiples_iff.mp (hh i)
 exact ⟨z,funext fun i=> by change x i=y i+z i • 1; rw [hz]; abel⟩


end YM.Integration.WilsonSeparatedOriginalSlabPeriodCells
