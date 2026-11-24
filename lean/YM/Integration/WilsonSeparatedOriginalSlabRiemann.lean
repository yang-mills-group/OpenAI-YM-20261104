import YM.Integration.WilsonWholeLimit

/-! Ordinary physical Riemann cells with the authenticated lattice volume on the original successive cutoff and period filter. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabRiemann
open Function Filter Set Metric MeasureTheory Wilson Lattice Extraction OPE OPE.Cards
open scoped Topology BigOperators Classical
variable {n:ℕ} (S:Schedule)

def centre {N p:ℕ}(x:Var S n N p):Points n:=points (S.place ∘ x)

theorem value (N p:ℕ)(h:Points n→ℂ)(x:Points n)(live:x∈Fund S p n):
    stair S (fun z:Var S n N p=>h (centre S z)) x=h (tag (S.a N) (address (S.a N) x)):=by
  have eq:address (S.a N) x=fun i=>lift (bucket (S:=S) N p x i):=found (N:=N) live
  rw [stair,indicator_of_mem live,eq];rfl

theorem tested (f:Extraction.Order)(h:Points n→ℂ)(cont:Continuous h)(compact:HasCompactSupport h):
    Tendsto (fun k:ℕ×ℕ=>(S.a k.1:ℂ)^(4*n)*∑z:Var S n k.1 k.2,h (centre S z)) f.fuse (𝓝 (∫x,h x)):=by
  obtain ⟨B,cap⟩:=compact.exists_bound_of_continuousOn (continuous_id (X:=Points n)).continuousOn
  let K:=closedBall (0:Points n) (|B|+2)
  have hi:IsCompact K:=isCompact_closedBall ..
  have roof(x:Points n)(live:h x≠0):‖x‖≤|B|:=(cap _ (subset_tsupport _ live)).trans (le_abs_self _)
  have periods:Tendsto (Prod.snd:ℕ×ℕ→ℕ) f.fuse atTop:=tendsto_atTop.mpr fun i=>show f.late (fun _ p=>i≤p) from (f.per.cofinal.eventually_ge_atTop i).mono fun _ hi=>Eventually.of_forall fun _=>hi
  have shrink:Tendsto (fun k:ℕ×ℕ=>(4*n:ℝ)*S.a k.1) f.fuse (𝓝 0):=by simpa using (S.shrinks.comp (OPE.Cards.largeMesh f)).const_mul (4*n:ℝ)
  apply Metric.tendsto_nhds.mpr;intro ε ep
  let M:=volume.real K
  have mp:0≤M:=measureReal_nonneg
  let δ:=ε/(M+1)
  have dp:0<δ:=div_pos ep (by linarith only [mp])
  obtain ⟨s,sp,close⟩:=Metric.uniformContinuous_iff.mp (compact.uniformContinuous_of_continuous cont) δ dp
  filter_upwards [periods.eventually (Extraction.room S hi),shrink.eventually_lt_const (lt_min sp zero_lt_one)] with k room small
  let v:=stair S (fun z:Var S n k.1 k.2=>h (centre S z))
  have lower(x:Points n)(hx:x∈K):x∈Fund S k.2 n:=fun i j=>⟨(room hx i j).1,(room hx i j).2.le⟩
  have within(x:Points n)(hx:x∈K):‖v x-h x‖≤δ:=by
    dsimp [v];rw [value S k.1 k.2 h x (lower x hx)]
    simpa only [dist_eq_norm] using (close ((approximate (S.a_pos k.1) x).trans_lt (lt_min_iff.mp small).1)).le
  have empty(x:Points n)(hx:x∉K):v x-h x=0:=by
    have outside:|B|+2<‖x‖:=by simpa [K,dist_zero_right] using hx
    have off:h x=0:=by by_contra q;linarith [roof x q]
    rw [off,sub_zero]
    by_cases inside:x∈Fund S k.2 n
    · dsimp [v];rw [value S k.1 k.2 h x inside];by_contra q
      have tagged:=roof _ q
      have gap:dist x (tag (S.a k.1) (address (S.a k.1) x))<1:= by rw [dist_comm];exact (approximate (S.a_pos k.1) x).trans_lt (lt_min_iff.mp small).2
      have tri:=dist_triangle x (tag (S.a k.1) (address (S.a k.1) x)) 0
      simp only [dist_zero_right] at tri;linarith
    · change (Fund S k.2 n).indicator _ x=0;rw [indicator_of_notMem inside]
  rw [←stair_integral (fun z:Var S n k.1 k.2=>h (centre S z)),dist_eq_norm,←integral_sub (stair_int (fun z:Var S n k.1 k.2=>h (centre S z))) (cont.integrable_of_hasCompactSupport compact)]
  change ‖∫x,v x-h x‖<ε
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero (s:=K) empty]
  calc ‖∫ x in K,v x-h x‖ ≤ δ*M:=norm_setIntegral_le_of_norm_le_const hi.measure_lt_top within
    _<ε:=by dsimp [δ];rw [div_mul_eq_mul_div,div_lt_iff₀ (by linarith only [mp])];nlinarith

end YM.Integration.WilsonSeparatedOriginalSlabRiemann
