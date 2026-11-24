import YM.MSbar.Domain.Sum
/-! Layer operations: genuine continued high-pass Wick contraction.
Counting signs kept with first order Cartesian pairing conventions. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Diagram
open Super Domain Domain.DR Loops Dim Symbol Function Set Filter MeasureTheory
open scoped Topology BigOperators Classical ContDiff ENNReal
variable {C:Type} {I:Finset C} {W:Edition C} {m k j n:ℕ} {U:Set ℂ}
  {f g:Functionals C} {L P A:Links C} {d e l : Bit}
abbrev Grow (C:Type)(m:ℕ):= Words C m × Mom m

def edge (a b:C)(L:Links C)(f:Functionals C) : Record (Device (Grow C)) := fun z m v =>
    let u:=v.1.1.1; let y:=v.1.1.2; let i:=(a,v.1.2); let j:=(b,v.2)
    L z m i j y*f z m ((i,y)::(j,-y)::u)

def board (C:Type): Site (Grow C):= (arena C).prod momentum

def tread (W:Edition C)(a b:C)(L:Links C)(f:Functionals C) (z:ℂ):= duplex (board C).toMotion (W.vector a) (W.vector b) z (edge a b L f z)
def lapSum (W:Edition C)(L:Links C)(f:Functionals C): Record (Grow C):= fun z m v=> (2:ℂ)⁻¹ * ∑ a∈W.active,∑ b∈W.active,tread W a b L f z m v
-- call factor 1/2 once

def Lap (W:Edition C)(L:Links C)(F:Functionals C): Functionals C:= DR.loop (line C) (lapSum W L F)
variable (h : Full U k W d f) (hp : Pilot U j W e L)
section
private abbrev B(C:Type):= ((board C).prod Site.moving).prod Site.moving
private def bay (a b:C) (m) (p:Device (Grow C) m) : Words C m :=
    let k:=p.1.1.2
    ((a,p.1.2),k)::((b,p.2),-k)::p.1.1.1
private lemma draws (a b:C): Draw (B C) (arena C) (bay a b):= by
    constructor
    · intro i j V p; unfold bay; exact (by simp_rw [show ∀ x: Words C i, (arena C).move V x=(line C).move V x from fun _=> rfl,Domain.work, map_neg]; rfl)
    intro E _ _ _ i x hx
    let q(e:E) := (x e).1.1.2; have hh : HasTemperateGrowth q:= (moment_plot _).mp hx.1.1.2
    exact ⟨Plot.cons a _ _ hx.1.2 hh (Plot.cons b _ (-q) hx.2 hh.neg hx.1.1.1.1),fun v=> (lead _ _ (q v) _).trans (hx.1.1.1.2 v)⟩
include h hp
lemma layout (a b:C): Eligible U (j+k) (B C) (edge a b L f) := by
   have he : Draw (B C) home (fun i v=> (v.1.1.2,(v.1.2,v.2))) :=
       ⟨fun _ _=> rfl, by introv H; exact ⟨H.1.1.2,H.1.2,H.2⟩⟩
   exact ((hp.cost a b).arg he).mul (h.licensed.arg (draws a b))
lemma tread_cost (a b:C): Eligible U (j+k) (board C) (tread W a b L f):=by
   refine duplex_cost _ _ (layout h hp a b) ?_ ?_
   · intro z hz m x w; exact (hp.uniformL a b z hz m x.2 w).product (h.colors z hz m a x.2 [] (((b,w),-x.2)::x.1))
   intro z hz m x w; exact (hp.uniformR a b z hz m x.2 w).product (h.colors z hz m b (-x.2) [((a,w),x.2)] x.1)
lemma lapSum_cost : Eligible U (j+k) (board C) (lapSum W L f):= ((Eligible.sum' W.active (fun a _=> Eligible.sum' W.active (fun b _=> tread_cost h hp a b)))).scale (2:ℂ)⁻¹
omit hp in
lemma laps_neutral {z:ℂ} (hz:z∈U)(p : Mom m): Quiet (fun w=> lapSum W L f z m (w,p)):=by
    intro v hv; unfold lapSum;dsimp only; rw [Finset.sum_eq_zero (fun a ha=> Finset.sum_eq_zero (fun b hb=>?_)), mul_zero]; unfold tread; refine duplex_zero (F:=edge a b L f z) (board C).toMotion (v,p) _ ?_
    intro n V u w; let y:=taxi V p; let A:=(a,u);let B:=(b,w); change _* f _ _ ((A,y)::(B,-y)::(line C).move V v)=_; rw [h.quiet _ hz n _ ?_,mul_zero]; rw [lead,quiet_move]; simpa only [ne_eq,map_zero] using (taxi_inj V).ne hv
omit h hp in
lemma laps_band {L:Links C}{K:ℝ}(h:Band U L K) {z:ℂ} (hz:z∈U)(x:Words C m): Vanish K (fun p=> lapSum W L f z m (x,p)):=by
    intro p hp; unfold lapSum;dsimp only; rw [Finset.sum_eq_zero (fun a ha=> Finset.sum_eq_zero (fun b hb=>?_)),mul_zero]; unfold tread; refine duplex_zero (F:=edge a b L f z) (board C).toMotion (x,p) _ ?_; intro n V u w; change L _ _ _ _ (taxi V p)*_=0; rw [h _ hz n _ _ _ ?_,zero_mul]; simpa [Prod.norm_def,-aleph,show taxi V p=(p.1,V p.2) from rfl, V.norm_map] using hp

lemma situated {K:ℝ}(H:Band U L K)(hK:0≤K): Situated U (j+k) (arena C) K (lapSum W L f):= by
    have he:= lapSum_cost h hp
    refine ⟨he,fun z hz m x=>⟨?_,laps_band H hz _⟩,hK⟩
    by_cases hu : channel x=0
    · refine (he.ev _ (fun v=> (x,v)) ⟨?_,?_⟩).cost.slice hz
      · exact ⟨Plot.cte x,fun _=>hu⟩
      exact moment_plot (m:=m) id|>.mpr HasTemperateGrowth.id
    have hh(p:Mom m):lapSum W L f z m (x,p)=0:= laps_neutral h hz p x hu
    simp_rw [hh];exact HasTemperateGrowth.const _
omit hp in
lemma lap_quiet {z:ℂ}(hz:z∈U): Quiet (Lap W L f z m):=by
    intro v hv; unfold Lap DR.loop DR.turn; rw [integral_eq_zero_of_ae ?_ ,mul_zero]; filter_upwards with x; unfold sumP request; let k:=(up m); change plate z (fun q=> lapSum _ _ _ z (m+1) ((line C).move k v,x,q))=0 -- shape needs tuple?
    rw [show (fun q=> lapSum W L f z (m+1) ((line C).move k v,x,q))=(0:Hat (m+1)→ℂ) from funext (fun q=> laps_neutral (L:=L) h hz (x,q) _ (show channel ((line C).move k v)≠0 from ?_)),plate_zero]; rw [quiet_move]; simpa only [ne_eq,map_zero] using (taxi_inj k).ne hv
lemma budget {K:ℝ}(hB:Band U L K)(hK:0≤K)(hu:IsOpen U): Total U (1+(j+k)) (Lap W L f) := ⟨(situated h hp hB hK).costs hu,fun _ hz _ => lap_quiet h hz⟩
end
end YM.MSbar.Diagram
