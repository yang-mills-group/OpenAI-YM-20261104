import YM.GradedFar.ForkTest
/-!
# (G.5) part I: visible and polarized exterior costs from LogTrace
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Fork
open Finset Filter Function Set Spec Table Extraction OPE OPE.Orbits OPE.Log
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius
attribute [local instance] Orbits.measO Orbits.borelO YM.Work.A15.compact_ortho
-- geometry w/variable rotations; centers retained
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    {I J:Type} [Fintype I] [Fintype J] (d:I→ℕ) (h:ℕ)
structure Launch (I:Type) where
    x : I → E4
    center:E4
abbrev Tiny (M δ r : ℝ)(z:Launch I):Prop := WithinRoom r M δ z.x z.center
def wage {Z:Type*} (t:ℝ)(_z:Z) := t^(h+1)/t^(∑i,d i)
def TagCost {Z:Type*} (r:ℝ)(_z:Z) := badge r
lemma compact_pay {Z:Type*} (B:ℝ→Z→Prop) (q:ℕ) : Safe (𝓝[>]0) B TagCost (fun r _=> r^q/r^(∑i,d i)):=by
  filter_upwards [self_mem_nhdsWithin, (ge_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with r (hr:0<r) h1 z _
  exact ⟨le_add_of_nonneg_right (by exact neg_nonneg.mpr (Real.log_nonpos hr.le h1)),by positivity⟩
lemma wage_ok {Z:Type*}(B:ℝ→Z→Prop): Safe (𝓝[>]0) B TagCost (fun r z=>wage d h r z):=
  compact_pay d B (h+1)

omit [Fintype I] [Fintype J] in
lemma tiny_inj {t M δ:ℝ}{z:Launch I}(hp:0<t)(hd:0<δ)(hz:Tiny M δ t z): Injective z.x :=by
  intro i j h; by_contra ne; have hv:=hz.spaced i j ne; rw [h,sub_self,norm_zero] at hv; exact (mul_pos hd hp).not_ge hv
lemma occupied {M δ:ℝ}(P:Prescription F.sector.derivatives)(_hm:0≤M)(hd:0<δ)(n:ℕ): ∀ᶠ r:ℝ in 𝓝[>]0,∀ z:Launch I, Tiny M δ r z →
    orbitMargin P n z.x z.center := by
  -- directly adapt `Clearance.eventually_dock`
  have hm' : Tendsto (fun r:ℝ=> M*r) (𝓝[>]0) (𝓝 0) := by
    simpa using (tendsto_id (x:=𝓝[>] (0:ℝ))).mono_right (nhdsWithin_le_nhds) |>.const_mul M
  have bill (e:Exterior C.book)(j:Fin e.n) : ∀ᶠ r:ℝ in 𝓝[>]0, M*r < ‖bearing e j‖ := hm'.eventually
    (gt_mem_nhds (norm_pos_iff.mpr (Ne.symm ((beside_distinct.mp (bearing_clear e)).2.2 () j))))
  filter_upwards [(eventually_all_finset (bands F.sector.derivatives n)).2 (fun i _=>(eventually_all_finset (P.sheet i).support).2
    (fun e _=> eventually_all.mpr (bill e))),self_mem_nhdsWithin] with r hr (hp:0<r) z hz i hi k e he
  have hx := Ortho.move_injective k |>.comp (tiny_inj hp hd hz)
  apply beside_distinct.mpr; refine ⟨(away_inject _ _).2 hx, (beside_distinct.mp (bearing_clear e)).2.1,?_⟩
  intro u v h; apply (lt_of_le_of_lt (hz.span u) (hr i hi e he v)).ne
  have hv:‖away (Ortho.move k ∘ z.x) (Ortho.move k z.center) u‖=‖z.x u-z.center‖:=
    congr_arg norm (show _= Ortho.motion k (z.x u-z.center) from (map_sub (Ortho.motion k) _ _).symm) |>.trans
      (LinearIsometryEquiv.norm_map _ _)
  exact hv.symm.trans (congrArg norm h)

lemma swung_clear (e:Exterior C.book): ∃ c:ℝ,0<c ∧ ∀ k o, ClearOf o (swung e k o) c:= by
  have h:=beside_distinct.mp (bearing_clear e)
  have a (i:Fin e.n):∀ᶠ c:ℝ in 𝓝[>]0, c≤ ‖bearing e i‖:= (ge_mem_nhds
    (norm_pos_iff.mpr (Ne.symm (h.2.2 () i)))).filter_mono nhdsWithin_le_nhds
  have b(i j:Fin e.n)(he:i≠j):∀ᶠ c:ℝ in 𝓝[>]0,c≤‖bearing e i-bearing e j‖:= (ge_mem_nhds
    (norm_pos_iff.mpr (sub_ne_zero.mpr (h.2.1.ne he)))).filter_mono nhdsWithin_le_nhds
  obtain ⟨c,hc,h₁,h₂⟩:=((show ∀ᶠ c:ℝ in 𝓝[>]0,0<c from self_mem_nhdsWithin).and
    ((eventually_all.mpr a).and (eventually_all.mpr fun i=> eventually_all.mpr fun j=> eventually_all.mpr (b i j)))).exists
  refine ⟨c,hc,fun k o=> ⟨fun i=>?_,fun i j he=>?_⟩⟩
  · rw [norm_sub_rev]; change _ ≤ ‖(o+Ortho.motion k (bearing e i))-o‖; rw [add_sub_cancel_left,(Ortho.motion k).norm_map]; exact h₁ i
  change _ ≤ ‖(o+Ortho.motion _ _)-(o+Ortho.motion _ _)‖
  rw [add_sub_add_left_eq_sub,← map_sub,(Ortho.motion k).norm_map]; exact h₂ i j he

abbrev Spins (I:Type) := Ortho × Launch I
variable {M δ:ℝ} {P:Prescription F.sector.derivatives}
abbrev SmallSpin (M δ r:ℝ) (z:Spins I) : Prop := Tiny M δ r z.2
variable (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (bank:LogTrace F Q.port) (hm:0≤M)(hd:0<δ)

-- for companion G7 and horizon tests: caps fixed on y roster, clearance-uniform
variable (e:J→ℕ) {c:ℝ} (hc:0<c) (u:Labels S d)
include bank hm hd
include hc in
lemma OnLog (w:Labels S e) : ∃ k:ℕ,∀ᶠ r:ℝ in 𝓝[>]0,∀ z:Launch I, Tiny M δ r z →
    ∀ y:J→E4, ClearOf z.center y c → Injective (beside z.x y) ∧ Injective (beside (sole z.center) y) ∧
     ∀ v, ‖shadowError F z.x y z.center h v Q.port u w‖ ≤ (badge r)^k*wage d h r z := by
  obtain ⟨k,H⟩:=bank.horizons _ _ (names u) (names w) δ M c hd hm hc h
  refine ⟨k,H.mono ?_⟩; intro r h z hx y hy; obtain ⟨h0,h1,h2⟩:= h z.x y z.center hx hy
  refine ⟨h0,h1,fun v=>?_⟩
  rw [shadowError_apply, discrepancy_old _ _ _ _ _ _ _ (spectate F v) (spectate_respects F v) (spectate_ready F v) h1]
  exact h2.phaseBound v

variable {e}
-- fixed Near arguments; all rotations (guards through occupied)
lemma shadePrice (e:Exterior C.book){g: Ortho→Labels S (expo e)}{D:ℝ} (hp:0≤D)(hg:∀ k j, ‖g k j‖≤D) :
    Sold (𝓝[>]0) (SmallSpin M δ) TagCost (wage d h) (fun _ (p:Spins I)=>
      shadowError F p.2.x (swung e p.1 p.2.center) p.2.center h none Q.port u (g p.1)) := by
  obtain ⟨c,hc,H⟩:= swung_clear e
  let f(a:ℝ)(z:Spins I):= shadowError (e:=expo e) F z.2.x (swung e z.1 z.2.center) z.2.center h none Q.port u
  apply Sold.present (A:=f) ?_ (wage_ok d h _) hp (Eventually.of_forall fun _ _ _=>hg _)
  intro v; obtain ⟨k,h⟩:= OnLog F d h Q bank hm hd (expo e) hc u v
  refine ⟨k,1,zero_le_one,h.mono ?_⟩; intro r h p hp; rw [one_mul]; exact (h p.2 hp _ (H ..)).2.2 none

omit bank hm hd
abbrev bridgeError (v:Labels S d) (A:Launch I→ S.Field h) (l:Exterior C.book) (i:Spins I) :=
  discrepancy S h i.2.x i.2.center v (A i.2) (swung l i.1 i.2.center) (turnsPort F.sector.turns i.1 l)

-- uniform across rotations of supplied exteriors
include Q
private lemma turns_price (l:Exterior C.book) : ∃ b:ℝ, 0≤b ∧ ∀ k j, ‖turnsPort F.sector.turns k l j‖ ≤ b:=by
  choose b hb using fun i:Fin l.n=>
    isCompact_univ.exists_bound_of_continuousOn (Q.law.spin _ (fields S l i)).continuousOn
  obtain ⟨c,hc⟩:=Finite.exists_le b; exact ⟨max 0 c, le_max_left .., fun k i=> (hb i k (Set.mem_univ _)).trans ((hc _).trans (le_max_right ..))⟩

omit Q in
abbrev replaced (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)(i:Launch I) :=
  shadowOld Q.port h i.x i.center u
local notation "Ω" => replaced F d h u Q
include bank hm hd
lemma boughtAt (l:Exterior C.book): Sold (𝓝[>]0) (SmallSpin M δ) TagCost (wage d h)
    (fun _ (i:Spins I)=>bridgeError F d h u Ω l i) := by
  obtain ⟨D,hD,HD⟩:= turns_price F Q l
  exact (shadePrice F d h Q bank hm hd u l hD HD).congr (fun _ _=> shadowError_apply ..)

omit bank hm hd
lemma bar_price (l:Exterior C.book): ∃ b:ℝ,0 ≤ b ∧ ∀ k j,
    ‖bar F.room.kernel.spin (d:=expo l) (turnsPort F.sector.turns k l) j‖ ≤ b := by
  obtain ⟨b,hb,h⟩:= turns_price F Q l
  let Y j := (conjugateR F.room.kernel.spin (expo l j)).toContinuousLinearMap
  obtain ⟨c,hc⟩:=Finite.exists_le fun j=> ‖Y j‖*b
  refine ⟨max 0 c,le_max_left ..,fun k j=>?_⟩
  exact ((Y j).le_opNorm (turnsPort F.sector.turns k l j)).trans ((mul_le_mul_of_nonneg_left (h k j) (norm_nonneg _)).trans ((hc _).trans (le_max_right ..)))
include bank hm hd
lemma boughtColor (l:Exterior C.book): Sold (𝓝[>]0) (SmallSpin M δ) TagCost (wage d h)
    (fun _ (i:Spins I)=>bridgeError F d h (bar F.room.kernel.spin u) (fun z=>S.conj F.room.kernel.spin h (Ω z)) l i):= by
  let v k:=turnsPort F.sector.turns k l; let w k:=bar F.room.kernel.spin (v k)
  obtain ⟨c,hc,H⟩:= swung_clear l; obtain ⟨k,hk⟩:= OnLog F d h Q bank hm hd (expo l) hc u (w 1)
  obtain ⟨D,hD,H'⟩:=bar_price F Q l; apply (shadePrice F d h Q bank hm hd u l (g:=w) hD H').price
  refine hk.mono ?_; intro r ht p hp; rw [shadowError_apply]; have hE:=ht p.2 hp _ (H p.1 p.2.center)
  let f:= discrepancy S h p.2.x p.2.center u (Ω p.2) (swung l p.1 p.2.center) (w p.1)
  have hh := whole_bar (v:=u) (w:=w p.1) F.room.kernel.spin Q.continuum hE.1
  have hg:= whole_bar (v:=fun _=> Ω p.2) (w:=w p.1) F.room.kernel.spin Q.continuum hE.2.1
  change ‖_‖ ≤ ‖f‖; apply le_of_eq; rw [← norm_star f]; congr 1
  unfold f discrepancy bridgeError; rw [discrepancy,star_sub,← hh]; unfold w; rw [bar_bar]; apply congr_arg (_-·)
  unfold w at hg; rw [bar_bar] at hg; exact hg
end YM.Integration.GradedFar.Fork
