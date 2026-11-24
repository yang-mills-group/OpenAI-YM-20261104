import YM.Integration.WilsonAllDateHarvestPhysical

/-! Separate real changes of the units of each original insertion on both sides
of the complete physical transfer, including motion and the cutoff child sum. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestRescaling
open Function Filter Finset Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Many RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {b m p N i d k:ℕ} {W:Type} [DecidableEq W] [Fintype W]

theorem point (S:Emblems C d) (x:Palette C d) (z:ℂ) (m i:ℕ):
    Many.point S (z • x) m i=z • Many.point S x m i:=by
  unfold Many.point; split <;> apply map_smul

private theorem bare (x:Palette C d) (z:ℂ):
    precinct C p N d (z • x)= z • precinct C p N d x := by
  funext f
  change entrance C d N p (z • x) 0 f = z • entrance C d N p x 0 f
  unfold entrance
  rw [Finset.smul_sum]; apply sum_congr rfl
  intro j _
  change (z*val x j) • _= z • val x j • _
  simp only [smul_smul,mul_assoc]

private theorem crop (g:Bin G (C.side N p)) (z:ℝ) (iN:i ≤ N):
    crops C N p N d le_rfl ((z:ℂ) • g) i iN=(z:ℂ) • crops C N p N d le_rfl g i iN:=by
  induction iN using Nat.decreasingInduction with
  | self=> rw [crops_head,crops_head]
  | of_succ i hi ih=>
    rw [crops_step _ _ hi,crops_step _ _ hi,ih]
    funext f
    change replenishes C p i N d hi ((z:ℂ) • crops C N p N d le_rfl g (i+1) hi) f=
      (z:ℂ) • replenishes C p i N d hi (crops C N p N d le_rfl g (i+1) hi) f
    unfold replenishes
    rw [Finset.smul_sum]; apply sum_congr rfl; intro j _
    dsimp only [Pi.smul_apply]; rw [Records.rot_scalar,Motion.scalar_real]
    exact smul_comm ..

theorem column (iN:i ≤ N) (x:Palette C d) (z:ℝ) (o:Site (C.side i p)) (E:Motion) (f:Body):
    clinic C p N d ((z:ℂ) • x) i o E f=(z:ℂ) • clinic C p N d x i o E f:=by
  unfold clinic uniform
  rw [dif_pos iN,dif_pos iN,bare,crop _ z iN,Pi.smul_apply,Records.rot_scalar,Motion.scalar_real]

variable (o:W→Site (C.side b p)) (E:W→Motion) (s:W→ℕ) (q:ManyStem C o b→Body)
local notation "A" => Mine.tree o E
local notation "Λ" => (A).labelY
variable (P:(j:W)→Sight C (s j) p) (S:(j:W)→Emblems C (s j)) (x:(j:W)→Palette C (s j)) (z:W→ℝ)
local notation "adjusted" => (fun j:W=>(z j:ℂ) • x j)
omit [DecidableEq W] [Fintype W] in
theorem source (iN:i ≤ N) (v:ManyStem C o i):
    WilsonAllDateHarvestPhysical.columns o E s q S adjusted m N i v=
      (z (Λ i v):ℂ) • WilsonAllDateHarvestPhysical.columns o E s q S x m N i v:=by
  unfold WilsonAllDateHarvestPhysical.columns Launch
  rw [point,column iN]

omit [DecidableEq W] [Fintype W] in
theorem row (h:C.Makes) (iN:i ≤ N) (v:ManyStem C o i):
    imprint h A (headings o E q) (plants (m:=m) s P S adjusted) i iN v=
      (z (Λ i v):ℂ) • imprint h A (headings o E q) (plants (m:=m) s P S x) i iN v:=by
  unfold imprint plants stages Launch
  rw [point,map_smul,LinearMap.smul_apply,spin_real _ _ _ (Motion.scalar_real ..)]

theorem own {T:Type*} [AddCommGroup T] [Module ℂ T] (l:W→ℂ) (X:W→T):
    Many.combine id l X = fun i=> l i • X i:=by
  funext i; unfold Many.combine; rw [Finset.sum_eq_single i]
  · simp
  · intro j _ ne; simp [ne]
  · simp

theorem width {a:ℝ} (ap:0<a) (mi:m ≤ i):
    envelope C m d k a i*a=envelope C m d k 1 i:=by
  unfold envelope west markWidth
  rw [rust_above mi,one_mul,one_mul,total_upper mi,total_upper mi,one_mul]
  rw [mul_comm a (stringCost C mi),div_mul_eq_div_div,div_mul_cancel₀ _ ap.ne']

end YM.Integration.WilsonAllDateHarvestRescaling
