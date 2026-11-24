import YM.OPE.Compatible.Glyph.Altar
/-! Stage flags and pads for repeated sunset. Compat clocks -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Votive
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Exterior WithLp Work.F08 Matrix Bloch Precision Stationary
open scoped Topology BigOperators Classical
variable {G:Gauge} (B:Sponsor G) (h:G.Simple) {i j:ℕ}{w v d a Ψ Φ:ℝ}
-- τ & a from actual paid; ensure patch width anchors for initial @ same or next. Use Moon choices
structure Seasons (B:Sponsor G) where
   peak (i:ℕ):ℝ
   positive i:0<peak i
   gradeL (i:ℕ):ℝ
   valL i:0≤gradeL i
-- stored cost
structure Quota (B:Sponsor G)(H: Seasons B)(i j:ℕ) where
   minL : ℕ
   tariff : ℝ
   target : ℝ
   assess : Side→ℝ
   tab : Side→ℝ
   σ : ℝ
   κ : ℝ
   traction : 0≤tariff
   opens : 0<target
   admits : Nudge B i j (H.gradeL i) (H.peak i) κ tariff σ target minL assess tab
   wind : H.peak j ≤ σ
   grip : κ≤ H.gradeL j

lemma seasons (B:Sponsor G) (h:G.Simple) (t:ℕ→ℝ) (u:ℕ→ℝ)(ht:∀ i,0<t i):∃ H: Seasons B,(∀ i,H.peak i ≤ t i ∧ u i ≤ H.gradeL i) ∧ ∀ (i:ℕ), Nonempty (Quota B H i i)∧Nonempty (Quota B H (i+1) i):=by
    choose κ s hk hs J using fun i j=> moonX B i j h
    let W(i) := min (min (s i i) (s i (i+1))) (t i); let A(i):=max (max (κ i i) (κ i (i+1))) (u i)
    have hx(i):0< W i:=lt_min (lt_min (hs i i) (hs i (i+1))) (ht i); have hp(i):0≤ A i:=(hk i i).trans ((le_max_left ..).trans (le_max_left ..)); let H: Seasons B:=⟨W,hx,A,hp⟩; refine ⟨H,fun i=>⟨min_le_right ..,le_max_right ..⟩,fun i=>?_⟩
    obtain ⟨c,t,M,U,y,hc,ht,hm⟩:= J i i (W i) (A i) (hx i) (hp i); obtain ⟨b,p,B,Q,Y,hb,hj,hB⟩:=J i (i+1) (W (i+1)) (A (i+1)) (hx _) (hp _)
    exact ⟨⟨⟨M,c,t,U,y,s i i,κ i i,hc,ht,hm,(min_le_left ..).trans (min_le_left ..),(le_max_left ..).trans (le_max_left ..)⟩⟩, ⟨⟨B,b,p,Q,Y,_,_,hb,hj,hB,(min_le_left ..).trans (min_le_right ..), (le_max_right ..).trans (le_max_left ..)⟩⟩⟩
lemma budget_mono (R: PathData G)(Z: Clip) (h:R.Bounds Z w v Ψ) (h':a≤w)(ha:0<a)(hd:v≤d)(hx:Ψ≤ Φ): R.Bounds Z a d Φ:=by
    have ht {α: Type} (f: α→ℝ)(F:α→ℕ)(x y:ℝ)(hp:x≤y)(g:0 ≤ f)(h:SumBudget (fun i=> f i*Real.exp (w*F i)) x): SumBudget (fun i=> f i * Real.exp (a*F i)) y:=by
        have hv:=budget_minor (f:=fun i=> f i * Real.exp (a*F i)) h (fun i=>by have hh:0 ≤ f i:=g i; positivity) (fun i=>mul_le_mul_of_nonneg_left (Real.exp_monotone (by gcongr)) (g _)); exact ⟨hv.1,hv.2.1,hv.2.2.trans hp⟩
    have he (j:ℕ)(U:ℕ→ Atom G j)(x y:ℝ)(hh:SumBudget (fun i=> (U i).budget w) x)(h:x≤y): SumBudget (fun i=> (U i).budget a) y:= ht (fun i=>(U i).magnitude) (fun i=>(U i).length) _ _ h (fun i=> Finset.sum_nonneg fun j _=>abs_nonneg _) hh
    refine { h with width:=ha, rows:=fun i=> ht _ _ _ _ hd (fun i=>abs_nonneg _) (h.rows i), two:= he 2 R.loop _ _ h.two hx, three:=he _ R.cubic _ _ h.three hd, four:=he _ R.quartic _ _ h.four hd }
structure Alps (H:Seasons B) (i:ℕ)(Λ:ℝ) where
    clip : Clip
    gear : Train i
    sky : Bed
    live : PathData G
    active : TicketBed B i clip gear sky
    fills : Attached sky live
    pays : live.Bounds clip (H.peak i) (H.gradeL i) Λ
end YM.OPE.Votive
