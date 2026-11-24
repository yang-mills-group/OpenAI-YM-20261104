import YM.Integration.WilsonAllDateHarvestRetainedCapture

/-! The original zero-mixed terminal field has an honest Bochner integral,
including the genuine old vacuum, all singleton marks and their shared exclusions. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabAdmission
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open WilsonAllDateHarvestAffine WilsonAllDateHarvestPropagation WilsonAllDateHarvestStability
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

section Dated
variable {G:Gauge} {C:Family G} {n m a per N d k:ℕ} {D:Address.Rail C}
variable (o:Fin 3→Site (C.side n per)) (E:Fin 3→Motion) (s:Fin 3→ℕ) (q:ManyStem C o n→Body)
variable (h:C.Makes) (stock:Storage C D) (P:(j:Fin 3)→Sight C (s j) per)
variable (S:(j:Fin 3)→Emblems C (s j)) (x:(j:Fin 3)→Palette C (s j)) (roster:Census (Fin 3))
variable {B:ℕ→ℕ→ℝ} {Q:ℝ}
set_option quotPrecheck false
local notation "t" => (m+1)
local notation "A" => Mine.tree o E
local notation "Λ" => (A).labelY
local notation "I" => headings o E q
local notation "H" => Mine.ward o E roster
local notation "Y" => C.path.rep N per
local notation "T" => plants (m:=t) s P S x
local notation "v" => Launch (m:=t) s S x
local notation "rows" => imprint h A I T
local notation "α" => fun i:ℕ=>(C.path.levels.budget i).supportExponent

include stock in
theorem filed (basis:∀j:Fin 3,Spine D B h n per (s j) N (P j) (S j))
    (nm:n ≤ m) (tN:t ≤ N) (occupied:Occupancy o (C.path.levels.clock.J n))
    (cap:∀j:ManyStem C o n,Cap (s (Λ n j)+2) (q j) 1)
    (sizeBound:∀j:Fin 3,size (x j) ≤ Q) (hQ:1 ≤ Q)
    (warm:Warm C n (d+1) k) (degree:∀j:Fin 3,s j ≤ d)
    (start:n ≤ a) (dated:a ≤ t) (single:∀j,Useful (Y t) (rows t tN j))
    (δ:ℝ) (positive:0 < δ)
    (R:Support (C.side t per)→ Config G (C.side t per)→
      Poly (Mine.masts o E start (barren o E roster a) t))
    (K:Box (C.side t per)→ Config G (C.side t per)→
      Poly (Mine.masts o E start (barren o E roster a) t))
    (legal:Carton ((A).supportX t) R K (Y t).p.threshold)
    (regular:Towed (fun _:ManyStem C o t=>1) id R (Y t).p.B ((α t)-1) δ)
    (forced:Towed (fun _:ManyStem C o t=>1) Prod.fst K (Y t).p.B ((α t)-1) δ) :
    let inc:=WilsonMixedTaggedSeparatedBoard.admitted o E roster start dated
    let opened:=WilsonAllDateHarvestEndpointOpening.opening inc (shadow A s I t)
    Integrable (fun U=>opened (density (Y t) (rows t tN) (fun _ _=>0) (fun _ _=>0) U))
      (prior G (C.side t per)) := by
  intro inc opened
  let amount:=Many.total C Q (d+1) t
  have nt:=nm.trans m.le_succ
  have qp:0 < Q:=zero_lt_one.trans_le hQ
  have purse:=ignite (Q:=Q) (m:=t) (N:=N) warm qp (d:=d+1) (by omega)
  have lesson:Lesson (D:=D) h s n N N per T B amount v:=by
    refine ⟨fun j=>⟨P j,S j,basis j,fun _=>rfl,fun i _ _=>nearpoints (S j) (x j) _,fun i ni iN=>?_⟩⟩
    exact head_cost (basis j) nt tN (Nat.add_le_add_right (degree j) _) (sizeBound j) ni iN
  have lamp:=Lesson.lights s h (lesson.revise s h (le_refl n) tN)
  obtain ⟨atBase,prepared⟩:=headlines (N:=N) o E q
  have samples:∀j:ManyStem C o n,Cap (s (Λ n j)+2) (I n j) 1:=by rw [atBase];exact cap
  have fitted:PreparedA A I n t le_rfl:=fun i ni it=>prepared i ni (it.trans_le tN)
  have reach (i:ℕ) (ni:n ≤ i):=Mine.pays o E ni occupied le_rfl
  have funded:=purse.slice (le_refl n) tN
  obtain ⟨left,_,_⟩:=WilsonAllDateHarvestCourseEntry.original A s I h stock (le_refl n) nm
    (Nat.lt_of_succ_le tN) funded lamp fitted samples (reach m nm).2 single
    (WilsonAllDateHarvestCourseEntry.tuning C t (d+1) k hQ)
    (WilsonAllDateHarvestAffine.actual o E roster start dated) δ positive legal regular forced
  have hr:scaled (0:ℂ) R=(fun _ _=>0):=by funext j U;exact zero_smul ℂ (R j U)
  have hk:scaled (0:ℂ) K=(fun _ _=>0):=by funext j U;exact zero_smul ℂ (K j U)
  have raw:=left.cleared
  dsimp only at raw
  rw [hr,hk] at raw
  exact (opened.toContinuousLinearMap.restrictScalars ℝ).integrable_comp raw

end Dated

section Physical
variable {G:Gauge}
variable (R:Run G)
local notation "C₀" => R.family

theorem original {n a t₀ N per d kHigh kLow:ℕ} (na:n ≤ a) (aturn:a ≤ t₀)
    (nt:n < t₀) (tN:t₀ ≤ N) (stock:Storage C₀ R.doors)
    {B:ℕ→ℕ→ℝ} (s:Fin 3→ℕ) (S:(v:Fin 3)→Emblems C₀ (s v)) (P:(v:Fin 3)→Sight C₀ (s v) per)
    (x:(v:Fin 3)→Palette C₀ (s v)) (o:Fin 3→Site ((C₀).side n per)) (E:Fin 3→Motion)
    (q:ManyStem C₀ o n→Body) (roster:Census (Fin 3))
    (basis:∀v,Spine R.doors B R.makes n per (s v) N (P v) (S v))
    (occ:Occupancy o ((C₀).path.levels.clock.J n))
    (cap:∀v:ManyStem C₀ o n,Cap (s v.val.1+2) (q v) 1)
    {Q δ:ℝ} (one:1 ≤ Q) (sizes:∀v,size (x v) ≤ Q)
    (warm:Warm C₀ n (d+1) kLow) (degree:∀v,s v ≤ d) (pos:0 < δ)
    (retained:WilsonReportHarvestReplayPhysical.Retained R na aturn tN s S P x o E q roster d kHigh Q δ) :
    let tr:=Mine.tree o E
    let shifts:=headings o E q
    let src:=plants (m:=a) s P S x
    let marks:=imprint R.makes tr shifts src t₀ tN
    let inc:=WilsonMixedTaggedSeparatedBoard.admitted o E roster na aturn
    let opened:=WilsonAllDateHarvestEndpointOpening.opening inc (shadow tr s shifts t₀)
    Integrable (fun U=>opened (density ((C₀).path.rep N per t₀) marks (fun _ _=>0) (fun _ _=>0) U))
      (prior G ((C₀).side t₀ per)) := by
  intro tr shifts src marks inc opened
  cases t₀ with
  | zero=>omega
  | succ m =>
    obtain ⟨_,board,_,_,H,K,legal,_,reg,hard⟩:=retained
    let raised:=WilsonAllDateHarvestRebook.raised s S x a (m+1)
    let cash:=Q*((C₀).S.a a/(C₀).S.a (m+1))
    have financed:1 ≤ cash:=one_le_mul_of_one_le_of_one_le one
      ((one_le_div ((C₀).S.a_pos _)).2 ((C₀).S.strictAnti.antitone aturn))
    have costs (v:Fin 3):size (raised v) ≤ cash:=WilsonAllDateHarvestRebook.sizeAt (basis v) na aturn tN (sizes v)
    have entries:plants (m:=m+1) s P S raised=src:=WilsonAllDateHarvestRebook.singleton s S x P a (m+1)
    have ready:=filed o E s q R.makes stock P S raised roster basis (Nat.le_of_lt_succ nt) tN occ cap
      costs financed warm degree na aturn (by rw [entries];exact board.fettled) δ pos H K legal reg hard
    dsimp only at ready
    rw [entries] at ready
    exact ready

end Physical
end YM.Integration.WilsonReportHarvestSlabAdmission
