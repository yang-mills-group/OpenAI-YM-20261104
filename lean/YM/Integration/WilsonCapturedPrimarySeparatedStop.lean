import YM.Integration.WilsonCapturedPrimaryGridGap
import YM.Integration.WilsonCapturedPrimaryCompactSites
import YM.Integration.WilsonFundedMeasuredWindow
import YM.RG05Readout.Aligned.Geometry

/-! At the funded fine stop each true compact child occupies its own Wilson
address. Both rounding and wrapping use the fine site's actual parent. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimarySeparatedStop
open Filter Set Lattice Wilson RG Source PhysicalNext.Repeat.Legato Next.Rank
open Extraction Cells Table RG12 RG16 XSpace RG05Readout
open scoped Topology Classical BigOperators
set_option quotPrecheck false
variable {G:Gauge} (R:Run G) (simple:G.Simple) (slow:WilsonWindowReportingPace.Slow R.kit)
local notation "C" => R.family
local notation "A" => (C).path.levels
local notation "cutB" i:max => ((A).budget i).B
local notation "k" h:max r:max => WilsonMeasuredWindow.stop (A) simple h r
local notation "χ" r:max N:max p:max => WilsonSeparatedOriginalThermometerCells.positions (R:=R) r (N,p)

include slow in
private theorem comparison (v:ℕ) (large:4<v) (η M:ℝ) (positive:0<η) (nonneg:0 ≤ M) :
    ∀ᶠ r:ℝ in 𝓝[>]0, let j:=k v r
      (32+4*(((cutB j)^2:ℕ):ℝ))*((C).S.a j/r)<η ∧
      ∀p,2*(M+32*((C).S.a j/r)) < (((C).side j p).val:ℝ)*((C).S.a j/r) := by
  obtain ⟨moves,measured⟩:=WilsonFundedMeasuredWindow.all_radii R slow simple (B:=v) (by omega)
  let f (i:ℕ) : ℝ :=RG05Readout.Lambda (A) i
  have ample:∀ᶠ i:ℕ in atTop, 2*((cutB i):ℝ)^2 < (η/20)*(f i)^v := by
    have native:=RG05Readout.shelf (X:=A) simple (show 0<η/20 by positivity) (B:=(v:ℝ)) (by exact_mod_cast large)
    simpa only [f,Real.rpow_natCast] using native
  have width : 0 < (1:ℝ)/(4*(M+32)) := by positivity
  filter_upwards [moves.eventually ample,Ioc_mem_nhdsGT ((C).S.a_pos 0),Ioc_mem_nhdsGT width] with r cut eligible small
  let j:=k v r
  have rp:=eligible.1
  have pay := (measured r rp eligible.2).1
  change f j^v  ≤  r/(C).S.a j at pay
  have stage : 1  ≤  ((cutB j):ℝ)^2 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ cutB j from ((A).budget j).B_pos))
  have log : 1  ≤  f j^v := one_le_pow₀ ((show 2<f j from RG05Readout.lambda_gt (A) j).le.trans' (by norm_num))
  have mesh : (C).S.a j  ≤  r := by
    simpa only [one_mul] using (le_div_iff₀ ((C).S.a_pos j)).mp (log.trans pay)
  have s := (le_div_iff₀ ((C).S.a_pos j)).mp pay
  have fixed : 32+4*(((cutB j)^2:ℕ):ℝ) < η*f j^v := by
    push_cast
    have c : 2*((cutB j):ℝ)^2 < (η/20)*f j^v := cut
    nlinarith only [c,stage]
  constructor
  · calc _=(32+4*(((cutB j)^2:ℕ):ℝ))*(C).S.a j/r := by ring
           _ < η := (div_lt_iff₀ rp).mpr ((mul_lt_mul_of_pos_right fixed ((C).S.a_pos j)).trans_le (by
             rw [mul_assoc];exact mul_le_mul_of_nonneg_left s positive.le))
  · intro p
    have root : 1  ≤  (((C).S.period p).val:ℝ) := by exact_mod_cast ((C).S.period p).property
    have diameter := (le_div_iff₀ (show 0<4*(M+32) by positivity)).mp small.2
    have ar : (0:ℝ) < M+32 := by linarith
    have bill : 2*(M*r+32*(C).S.a j) < (((C).S.period p).val:ℝ) := by
      nlinarith only [diameter,root,mesh]
    have span: (C).S.a j*(((C).side j p).val:ℝ)=(((C).S.period p).val:ℝ):=(C).S.span_side j p
    calc _=2*(M*r+32*(C).S.a j)/r := by field_simp;ring
         _ < (((C).S.period p).val:ℝ)/r := (div_lt_div_iff_of_pos_right rp).mpr bill
         _ = _ := by rw [←span]; ring


local notation "siteOf" r:max N:max p:max x:max a:max => wrap ((C).side N p) (address ((C).S.a N) (r • x) a)

include slow in
theorem translated {n:ℕ} (v:ℕ) (large:4<v) (φ:Test n) :
    ∀ᶠ r:ℝ in 𝓝[>]0, let j:=k v r
    ∀N p (live:j ≤ N) (x:Points n), x∈tsupport (fun x=>φ x) → ∀(offset:Site ((C).side N p)) (a c:Fin n),a ≠ c →
    (cutB j)^2 < separation (((C).S.toDepth live p).parent ((siteOf r N p x a)-offset))
      (((C).S.toDepth live p).parent ((siteOf r N p x c)-offset)) := by
  have pair (a c:Fin n) : ∀ᶠ r:ℝ in 𝓝[>]0, let j:=k v r
      ∀N p (live:j ≤ N) (x:Points n), x∈tsupport (fun x=>φ x)  → ∀offset:Site ((C).side N p), a ≠ c  → 
      (cutB j)^2 < separation (((C).S.toDepth live p).parent ((siteOf r N p x a)-offset))
          (((C).S.toDepth live p).parent ((siteOf r N p x c)-offset)) := by
    by_cases same:a=c
    · exact Eventually.of_forall fun _ _ _ _ _ _ _ ne=>(ne same).elim
    by_cases empty : (tsupport (fun x=>φ x)).Nonempty
    · let d (x:Points n) := dist (x a) (x c)
      have continuousD : Continuous d := by unfold d;fun_prop
      obtain ⟨u,hu,lower⟩:=φ.hasCompactSupport.exists_isMinOn empty continuousD.continuousOn
      obtain ⟨M,upper⟩:=φ.hasCompactSupport.exists_bound_of_continuousOn continuousD.continuousOn
      have positive : 0<d u:=dist_pos.mpr ((φ.tsupport_subset hu).ne same)
      have mn : 0 ≤ M:=(norm_nonneg _).trans (upper u hu)
      filter_upwards [comparison R simple slow v large (d u) M positive mn,self_mem_nhdsWithin] with r enough (rp:0<r)
      dsimp only
      intro N p live x paid offset _
      let two:Points 2:=points ![x a,x c]
      have metric : dist (two 0) (two 1)=d x:= rfl
      have min := lower paid
      have max : d x ≤ M := (Real.le_norm_self _).trans (upper x paid)
      apply WilsonCapturedPrimaryGridGap.translated R.family (p:=p) offset live r rp two ((cutB (k v r))^2)
        (by rw [metric]; exact enough.1.trans_le min) (by rw [metric];exact (enough.2 p).trans_le' (by linarith))
    · exact Eventually.of_forall fun _ _ _ _ x inside _ _=>(empty ⟨x,inside⟩).elim
  filter_upwards [eventually_all.mpr (fun a=>eventually_all.mpr (fun c=>pair a c))] with r geometry
  dsimp only
  intro N p live x support offset a c ne
  exact geometry a c N p live x support offset ne

include slow in
theorem on_support {n:ℕ} (v:ℕ) (large:4<v) (φ:Test n) :
    ∀ᶠ r:ℝ in 𝓝[>]0, let j:=k v r
    ∀N p (live:j ≤ N) (x:Points n), x∈tsupport (fun x=>φ x) → ∀a c:Fin n,a ≠ c →
    (cutB j)^2 < separation (((C).S.toDepth live p).parent (siteOf r N p x a))
      (((C).S.toDepth live p).parent (siteOf r N p x c)) := by
  filter_upwards [translated R simple slow v large φ] with r criterion
  dsimp only
  intro N p live x support a c ne
  simpa only [sub_zero] using criterion N p live x support 0 a c ne

include slow in
theorem original (v:ℕ) (large:4<v) (φ:Test 3) :
    ∀ᶠ r:ℝ in 𝓝[>]0, let j:=k v r; ∀N p (live:j ≤ N) (z:Fin 3 → Site ((C).side N p)),
      WilsonSeparatedOriginalThermometerCells.weight φ (χ r N p) z  ≠  0  → 
      ∀a c:Fin 3,a ≠ c  →  (cutB j)^2 < separation (((C).S.toDepth live p).parent (z a))
        (((C).S.toDepth live p).parent (z c)) := by
  filter_upwards [on_support R simple slow v large φ] with r geometry
  dsimp only
  intro N p live z amount a c ne
  obtain ⟨x,nonzero,rfl⟩:=WilsonCapturedPrimaryCompactSites.active R φ r (N,p) z amount
  exact geometry N p live x (subset_closure nonzero) a c ne

end YM.Integration.WilsonCapturedPrimarySeparatedStop
