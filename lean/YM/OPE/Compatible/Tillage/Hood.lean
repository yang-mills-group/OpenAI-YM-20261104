import YM.OPE.Compatible.Tillage.Chair
/-! # Buyer. Cost universality for fixed sector-month (after first virtual step may fix clip). -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Votive
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Flume Flume.Script Frequency
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{n c f L:Side}{P:Patch}{K:KernelChoices}{I J M:Type}{m k r d:ℕ}{σ C s u z:ℝ}{B:Sponsor G}{H:Seasons B}
namespace Alps
open Page Virgin Planned.PrimaryIntegral295.Carrier Boxes
variable {Y Z v w:M→ℝ}{p q:Clip}
lemma word_cost (B:Sponsor G)(H:Seasons B)(i r m:ℕ)(p:Clip): ∃ c:ℝ,0 ≤ c∧∀ z:ℝ,∀ V:Alps B H i z,V.clip=p → soot m (V.word r) c:=by
    obtain ⟨x,hx⟩:= oath_earn G p (H.peak i) (H.gradeL i) (H.positive i) r m; let c:= ‖(r.factorial:ℝ)‖*(x*((r+1:ℕ):ℝ)^m); exact ⟨max c 0,le_max_right ..,fun _ V hv=> by
       have h : V.live.Bounds p _ _ _:= hv ▸ V.pays; unfold word; rw [hv]; exact ((silt_cost (hx V.live _ h).credit).scale_line (r.factorial:ℝ)|>.tips (show c≤ _ from le_max_left ..))⟩
lemma leaf_cash (B:Sponsor G)(H: Seasons B)(i r m:ℕ): ∃ c:ℝ,0 ≤ c∧∀ z:ℝ,0≤ z→∀ V:Alps B H i z,soot m (V.liftZ r) (c*z):=by
   obtain ⟨x,hx⟩:= oathLoop G (H.peak i) (H.positive i) r m; let c:= ‖(r.factorial:ℝ)‖ * x*((r+1:ℕ):ℝ)^m; exact ⟨max c 0, le_max_right .., fun z hz V=>((silt_cost (hx _ _ _ _ V.pays).credit).scale_line (r.factorial:ℝ)|>.tips (le_trans (le_of_eq (show _=c*z from by unfold c; ring)) (mul_le_mul_of_nonneg_right (le_max_left ..) hz)))⟩
lemma word_loan (p:Clip)(X:∀ i:M, Alps B H k (Y i))(h:∀ i,(X i).clip=p): Loan m (fun i=>(X i).word r) 1 Z:=by obtain ⟨c,hx,hc⟩:= word_cost B H k r m p; exact ⟨c,hx,0,fun i=>by simpa using hc _ (X i) (h i)⟩
lemma leaf_loan (X:∀ i:M, Alps B H k (Y i))(h:0≤ Y)(hp:Y ≤ Z): Loan m (fun i=>(X i).liftZ r) 1 Z:=by
    obtain ⟨c,hc,H⟩:= leaf_cash B H k r m; refine ⟨c,hc,1,fun i=>?_⟩; rw [Pi.one_apply,mul_one,pow_one]; exact (H _ (h i) (X i)).tips (mul_le_mul_of_nonneg_left (hp i) hc)
-- Fires. organize Pair local not Y smugs.
section career
variable (T:Medal P G B.K P.J) (U:∀ i:M, Alps B H P.J (v i)) (V:∀ i:M,Alps B H P.J (w i))
abbrev Qmark (i:M):Boxes G P B.K:= charmSeal T ((U i).gear)
abbrev boardA (r:ℕ)(i:M):= voteV P B.K (U i).live (U i).clip r -- P explicit?
lemma boardLoan (hx: Loan m (fun i=>(U i).word r) 1 Y)(hY:1 ≤ Y): Loan m (boardA U r) 1 Y:=by -- P explicit order missing
   have hh:= Loan.plat (drip G P.L) (drip_cash G P.L) hx; have ht:= hh.seize (Loan.fixed (X:=Y) (expose (stationCall P B.K G r)) (folkS (callCost P B.K G r) _)) hY zero_le_one; rw [show boardA U r= _ from ?_]; exact ht; ext1 i; exact vote_eq _ _ _ _ _
-- variation
lemma payTravel (hp:∀ i,folk ((U i).word r))(hE:∀ i,folk ((V i).word r))(h:Loan m (fun i=>(U i).word r-(V i).word r) Z Y): Loan m (boardA U r -boardA V r) Z Y:=by
    have H:= Loan.plat (drip G P.L) (drip_cash G P.L) h; rw [show boardA U r-boardA V r=_ from ?_]; exact H; ext1 i; change voteV _ _ _ _ _-voteV _ _ _ _ _=_; rw [vote_eq, vote_eq, add_sub_add_right_eq_sub, show payVolume _ ((U i).word r-_) = _ from volVSub (drip_cash G P.L) (hp i) (hE i)]
end career
end Alps
end YM.OPE.Votive
