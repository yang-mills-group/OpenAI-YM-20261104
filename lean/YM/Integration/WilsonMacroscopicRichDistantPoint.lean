import YM.Integration.WilsonMacroscopicRichRotatedPlane

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichDistantPoint
open YM YM.Spec YM.PhysMS YM.Trace.Pilot YM.Table.Pairing YM.Spin YM.Climb YM.Next.UVStress
open Filter Set WilsonMacroscopicRichReflectedRoster WilsonMacroscopicRichMovingPlane
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}

private abbrev Sides:=Axis×Bool
private def turning (d:Sides):Signed:=if d.2 then Signed.mirror d.1 else 1
private def component (d:Sides)(y:Points 1):ℝ:=((turning d).ortho.motion (y 0)) d.1
private lemma point (d:Axis):Continuous fun y:Points 1=>y 0 d:=by
  exact ((continuous_apply d).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _:Axis=>ℝ)).continuous).comp
    ((continuous_apply 0).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _:Fin 1=>E4)).continuous)
private lemma coord (d:Sides):Continuous (component d):=by
  exact ((continuous_apply d.1).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _:Axis=>ℝ)).continuous).comp
    ((turning d).ortho.motion.continuous.comp ((continuous_apply 0).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _:Fin 1=>E4)).continuous))

private theorem cover (L:Set (Points 1))(hL:IsCompact L)(clear:∀y∈L,y 0≠0):
    ∃δ:ℝ,0<δ ∧ ∀y∈L,∃d:Sides,δ≤component d y:=by
  rcases L.eq_empty_or_nonempty with rfl|pop
  · exact ⟨1,zero_lt_one,by simp⟩
  let size:Points 1→ℝ:=fun y=>∑a:Axis,|y 0 a|
  have cont:Continuous size:=continuous_finsetSum _ (fun a _=>(point a).abs)
  obtain ⟨u,hu,minimal⟩:=hL.exists_isMinOn pop cont.continuousOn
  have pos:0<size u:=by
    obtain ⟨i,hi⟩:∃i:Axis,u 0 i≠0:=by
      by_contra! h;apply clear _ hu;apply PiLp.ext;exact h
    exact Finset.sum_pos' (fun _ _=>abs_nonneg _) ⟨i,Finset.mem_univ _,abs_pos.mpr hi⟩
  refine ⟨size u/8,by positivity,?_⟩
  intro y hy
  obtain ⟨i,hi⟩:∃i:Axis,size u/8≤|y 0 i|:=by
    by_contra! all
    have bound:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=>(all i).le)
    have gate:size y≤4*(size u/8):=by simpa [size,Axis] using bound
    have low:size u ≤ size y:=minimal hy
    linarith
  by_cases h:0≤y 0 i
  · refine ⟨⟨i,false⟩,?_⟩
    have price:size u/8≤y 0 i:=by simpa [abs_of_nonneg h] using hi
    change size u/8 ≤ (Ortho.move (Signed.ortho (1:Signed)) (y 0)) i
    rw [show Signed.ortho (1:Signed) = 1 from Signed.inclusionO.map_one,Ortho.move_one];exact price
  · refine ⟨⟨i,true⟩,?_⟩
    have price:size u/8≤ -(y 0 i):=by simpa [abs_of_neg (lt_of_not_ge h)] using hi
    change size u/8 ≤ (ride i (y 0)) i
    simpa [ride] using price

/-- Uniform genuine physical correlation with one exterior point separated from the origin
in its own scaled compact.  The exterior need not stay in one fixed angular sector. -/
theorem original (F:Spec.Final C f S)(J:ℝ→tower S)(H:Leading F J){n:ℕ}
    (K:Set (Points n))(L:Set (Points 1))(hK:IsCompact K)(hL:IsCompact L)(xSafe:K⊆conf n)
    (clear:∀y∈L,y 0≠0)(v:Fin n→(Bel C.book).Tag)(w:(Bel C.book).Tag):
    ∃η:ℝ,0<η ∧ ∃B:ℝ,0≤B ∧ ∃U∈trail,∀r∈U,∀τ∈U,r/τ≤η → ∀x∈K,∀y∈L,
      ‖S.useAt S (placed r τ x y) (Fin.append (fun i=>physical J r (v i)) (fun _:Fin 1=>physical J τ w))‖≤B:=by
  obtain ⟨δ,pos,covers⟩:=cover L hL clear
  let T (d:Sides):Set (Points 1):=L∩{y|δ≤component d y}
  have compact (d:Sides):IsCompact (T d):=hL.inter_right (isClosed_le continuous_const (coord d))
  have bound(d:Sides): ∃η:ℝ,0<η ∧ ∃B:ℝ,0≤B ∧ ∃U∈trail,∀r∈U,∀τ∈U,r/τ≤η → ∀x∈K,∀y∈T d,
      ‖S.useAt S (placed r τ x y) (Fin.append (fun i=>physical J r (v i)) (fun _:Fin 1=>physical J τ w))‖≤B:=by
    apply WilsonMacroscopicRichRotatedPlane.original F J H (turning d) d.1 δ pos K (T d) hK (compact d) xSafe
    · intro y _ i j _; exact Subsingleton.elim i j
    · intro y hy j;rw [Subsingleton.elim j 0];exact hy.2
  choose η he B hb U hU bill using bound
  obtain ⟨d,low⟩:=Finite.exists_min η
  obtain ⟨e,high⟩:=Finite.exists_max B
  refine ⟨η d,he d,B e,hb e,{r|∀j:Sides,r∈U j},Filter.eventually_all.2 hU,?_⟩
  intro r hr τ hτ ratio x hx y hy
  obtain ⟨j,side⟩:=covers y hy
  exact (bill j r (hr j) τ (hτ j) (ratio.trans (low j)) x hx y ⟨hy,side⟩).trans (high j)

end YM.Integration.WilsonMacroscopicRichDistantPoint
