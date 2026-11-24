import YM.OPE.Compatible.Tillage.Paradise
/-!
# Repeat wards
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Votive
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Flume Flume.Script Frequency
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{n c f L:Side}{P:Patch}{K:KernelChoices}{I J M:Type}{m k r d:ℕ}{σ C s u z:ℝ}{B:Sponsor G} {H:Seasons B}{V:ChartRatio G}{p:Clip}
namespace Alps
open Page Virgin Planned.PrimaryIntegral295.Carrier Boxes
structure Sailing (H:Seasons B)(P:Patch)(p:Clip)(V:ChartRatio G)(C:ℝ) where
    cost : ℝ
    fits : 1 ≤ cost
    U : ℕ→ Alps B H P.J cost
    R (t:ℕ) : (U t).clip=p
    fare : ℕ→ℝ
    shot (t): Charm P.L (U t) (U (t+1)) (fare t) V
    bound (t): |fare t|≤ C
namespace Sailing
variable (A:Sailing H P p V C)
lemma launchAt (u:Quota B H P.J P.J)(z:ℝ)(hz:1≤z)(hx:u.minL ≤ P.L.val)(he:u.tab P.L ≤ z)(hk:Mag P.J P.J)(hp: p.direct≤ B.γ P.J)(hv:LocalRatio V)(a:Alps B H P.J z)(hA:a.clip=p)(hT:big_cost u P.L≤ C):∃ A: Sailing H P p V C,A.cost=z ∧ HEq (A.U 0) a :=by -- dep HEq acceptable
    obtain ⟨V,hv,h,hF⟩:= drum u p hp hx he hk P.coarse P.odd_side hz hv a; have hh(i): (V i).clip=p :=by cases i; rw [h]; exact hA; exact (hF _).2.1
    exact ⟨⟨z,hz,V,hh,hv,fun i=>(hF i).2.2,fun i=>(hF i).1.trans hT⟩,rfl,h ▸ HEq.rfl⟩
def shiftS (i:ℕ):Sailing H P p V C:={A with
    U:=fun k=>A.U (i+k)
    R:=fun k=>A.R (i+k)
    fare:=fun k=>A.fare (i+k)
    bound:=fun k=> A.bound (i+k)
    shot:=fun k=> A.shot (i+k) }
lemma growing (i:ℕ): (A.U i).gear = folder P (A.U 0).gear i:=by induction i with | zero=>rfl | succ i ih=> rw [interlock P _ _ (A.shot i), ih];rfl
end Sailing
variable {x: ℝ}
-- All pairs. crest dynamics.
abbrev Crew (H:Seasons B) (P:Patch)(p:Clip)(V:ChartRatio G)(C:ℝ):= Sailing H P p V C × Sailing H P p V C
abbrev TileC (H:Seasons B) (P:Patch)(p:Clip)(V:ChartRatio G)(C:ℝ):= Crew H P p V C × ℕ
abbrev downK (x:M×ℕ):ℝ:= (1/2:ℝ)^x.2
abbrev upperX (p: TileC H P p V C):= max p.1.1.cost p.1.2.cost
abbrev UA (p: TileC H P p V C):= p.1.1.U p.2
abbrev VA (p: TileC H P p V C):= p.1.2.U p.2
abbrev betaA (p: TileC H P p V C):= p.1.1.fare p.2
abbrev betaE (p: TileC H P p V C):= p.1.2.fare p.2
abbrev fallsF (p:M×ℕ): M×ℕ:= (p.1,p.2+1)
lemma running (H: Seasons B)(P:Patch)(T:Medal P G B.K P.J)(p:Clip)(V:ChartRatio G)(C:ℝ)(h:Crest G P B.K m): ∃ t W:ℝ,0<t ∧ Roles (M:=TileC H P p V C) T UA VA W downK upperX ∧ Tip (K:=TileC H P p V C) t (fun i=> (UA i).root - (VA i).root) downK upperX :=by
    obtain ⟨t,v,D,B',hP⟩:= h.rows; obtain ⟨b,Hb⟩:=sanction hP; have hh:Tip (K:=TileC H P p V C) t (fun i=> (UA i).root - (VA i).root) downK upperX:=by
        refine ⟨max 0 b, le_max_left ..,0,fun i=>?_⟩; let A:= i.1.1; let V:=i.1.2; change (Op B.K (A.U i.2).gear-Op B.K (V.U i.2).gear).strip t _; rw [A.growing i.2,V.growing i.2]; refine strip_mono (Hb (A.U 0).gear (V.U 0).gear i.2 i.2 le_rfl) le_rfl ?_; simp only [pow_zero, mul_one]; exact mul_le_mul_of_nonneg_right (le_max_right ..) (pow_nonneg (by norm_num : 0 ≤ (1/2:ℝ)) _)
    obtain ⟨s,hS⟩:= rosters (T:=T) (U:=UA) (V:=VA) (fun i=>(Sailing.fits i.1.1).trans (le_max_left ..)) (fun i=>Sailing.R i.1.1 i.2) (fun i=>Sailing.R i.1.2 i.2) (fun i=>by change 0<(1/2:ℝ)^i.2; positivity) hh hP.height; exact ⟨t,s,hP.height,hS,hh⟩
end Alps
end YM.OPE.Votive
