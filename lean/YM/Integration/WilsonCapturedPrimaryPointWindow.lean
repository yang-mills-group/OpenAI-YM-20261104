import YM.Integration.WilsonCapturedPrimaryPointBasis
import YM.Integration.WilsonPhysicalProjectionHolonomyPrice
import YM.FormalBulk08.Pose.Wise

/-! Canonical finite-link detectors on the independent point field. The geometric
identities below are the pure finite-gauge portions of ProjectionScope, FiniteSlate,
HeldReadout and FiniteColumn. Here their native source is qualified directly beside
the point course without the unrelated averaged Wilson-campaign imports. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonCapturedPrimaryPointWindow
open Function Filter Finset Lattice Laurent Gauge Wilson Exterior Stationary Source Source.Drops
open FormalBulk08 FormalBulk08.Lava FormalBulk08.Lotus FormalBulk08.Mesa FormalBulk08.Gorge
open FormalBulk08.Reef FormalBulk08.Orb FormalBulk08.Shore FormalBulk08.Kemp FormalBulk08.Rift
open FormalBulk08.Pose FormalBulk08.City FormalBulk08.Flat FormalBulk08.Roof FormalBulk08.Dawn
open Planned.PrimaryIntegral295 Place Carrier Film Labels Precision Next.Free Next.Foundations
open scoped Classical Topology BigOperators ENNReal ContDiff
variable {G:Gauge} {r d s:ℕ} {n:Side}

def retained (n:Side) (B:ℕ) (v:chain (edgeL G) r):Prop:=
  ∀j:Fin r,
    wrap n (v j).1∈halo B {0} ∧
    wrap n (v j).1+step (bearing (v j))∈halo B {0} ∧
    Lattice.lift (wrap n (v j).1)=(v j).1

def lost (n:Side) (B:ℕ) (T:Tile (edgeL G) r):Tile (edgeL G) r:=
  fun v=>if retained n B v then 0 else T v

def held (n:Side) (B:ℕ) (T:Tile (edgeL G) r):Tile (edgeL G) r:=
  fun v=>if retained n B v then T v else 0

theorem split (n:Side) (B:ℕ) (T:Tile (edgeL G) r):T=held n B T+lost n B T:=by
  funext v
  change T v=(if _ then T v else 0)+(if _ then 0 else T v)
  split <;> simp_all

private theorem size_bound (n:Side) (z:Cover):pdist (wrap n z)≤ size z:=by
  apply le_trans _ (Lotus.skirt n z)
  exact Finset.sup_le fun i _=>Finset.single_le_sum (f:=fun k=>(Lattice.lift (wrap n z) k).natAbs)
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)

theorem filled (n:Side) (B:ℕ) (fit:2*B<n.val) (o:Loc G 1)
    (v:chain (edgeL G) r) (small:herb (fame _) (0,o) v<B):retained n B v:=by
  intro j
  let z:=(v j).1
  have inside:size z<B:=(seat_ink o v j).trans_lt small
  have here:pdist (wrap n z)<B:=(size_bound n z).trans_lt inside
  have just (y:Site n) (hy:pdist y≤B):y∈halo B {0}:=by
    apply halo_spec.mpr
    refine ⟨0,Finset.mem_singleton_self 0,?_⟩
    simpa [separation] using hy
  have dest:pdist (wrap n z+step (bearing (v j)))≤B:=by
    apply (pdist_triangle ..).trans
    exact (Nat.add_le_add_left (pdist_step (bearing (v j))) _).trans (by omega)
  refine ⟨just _ here.le,just _ dest,?_⟩
  apply lift_eq_iff.mpr
  refine ⟨rfl,fun k=>?_⟩
  have component:(z k).natAbs≤ size z:=Finset.single_le_sum (fun j _=>Nat.zero_le ((z j).natAbs)) (Finset.mem_univ k)
  change - (n.val:ℤ)<2*(z k) ∧ 2*(z k)≤n.val
  omega

def active (B:ℕ) (v:chain (wire G n) r):Prop:=
  ∀j:Fin r,(v j).1∈halo B {0} ∧ (v j).1+step (bearing (v j))∈halo B {0}

def masked (B:ℕ) (T:Tile (wire G n) r) (v:chain (wire G n) r):ℝ:=
  if active B v then T v else 0

def reading (B:ℕ) (T:Tile (wire G n) r) (d:ℕ):Snap G d→ℝ:=
  ∑v:chain (wire G n) r, masked B T v • Pose.tier (boil n ∘ v)

def measured (B:ℕ) (T:Tile (wire G n) r) (d s:ℕ):Slate G d s:=
  Tensor.coeff (reading B T d) s 0

theorem derivative (B:ℕ) (T:Tile (wire G n) r) (x:Fin s→Snap G d):
    measured B T d s x=∑v:chain (wire G n) r,masked B T v*Tensor.coeff (Pose.tier (boil n ∘ v)) s 0 x:=
by
  let f:chain (wire G n) r→Snap G d→ℝ:=fun v=>Pose.tier (boil n ∘ v)
  have smooth (v:chain (wire G n) r):ContDiffAt ℝ s (f v) 0:=
    (tier_diff (d:=d) (boil n ∘ v)).of_le le_top
  unfold measured reading
  exact stack_val (n:=s) (I:=chain (wire G n) r) (E:=Snap G d) univ (masked B T) f x (fun v _=>smooth v)

theorem canonical (B:ℕ) (v:chain (edgeL G) r) (fit:retained n B v):
    boil n ∘ (drip n ∘ v)=v:=by
  funext j
  exact Prod.ext (fit j).2.2 rfl

theorem centered (B:ℕ) (x:chain (wire G n) r):
    retained n B (boil n ∘ x)↔active B x:=by
  unfold active
  simp [retained,boil,bearing]

private theorem round (x:chain (wire G n) r):drip n ∘ (boil n ∘ x)=x:=by
  funext j;simp

theorem funded (B:ℕ) (o:Loc G 1) {w A:ℝ} (T:Tile (edgeL G) r)
    (ht:Knoxville (fame _) w (0,o) T A):Knoxville (fame _) w (0,o) (held n B T) A:=by
  refine ⟨ht.1,(ENNReal.tsum_le_tsum fun v=>?_).trans ht.2⟩
  by_cases h:retained n B v <;> simp [held,h]

theorem fold (B:ℕ) (T:Tile (edgeL G) r) (x:chain (wire G n) r):
    masked B (sieve n (held n B T)) x=held n B T (boil n ∘ x):=by
  have only:sieve n (held n B T) x=held n B T (boil n ∘ x):=by
    rw [sieve_i,tsum_eq_single (boil n ∘ x) ?_,if_pos (round x)]
    intro v other
    by_cases image:drip n ∘ v=x
    · have missing:¬retained n B v:=by
        intro fit
        apply other
        exact (canonical B v fit).symm.trans (congrArg (fun z=>boil n ∘ z) image)
      simp [image,held,missing]
    · simp [image]
  by_cases valid:active B x
  · simpa [masked,valid] using only
  · simp [masked,valid,held,(centered B x).not.mpr valid]

theorem near_read (B:ℕ) (o:Loc G 1) (T:Tile (edgeL G) r) {w A:ℝ}
    (pos:0<w) (ht:Knoxville (fame _) w (0,o) T A):
    measured B (sieve n (held n B T)) d s=slate (held n B T) d s:=by
  ext x
  rw [derivative,slate_read o (held n B T) x pos (funded B o T ht)]
  let f (v:chain (edgeL G) r):=held n B T v * Tensor.coeff (Pose.tier v) s 0 x
  let e:(chain (wire G n) r) ↪ (chain (edgeL G) r):=
    ⟨fun z=>boil n ∘ z,fun x y h=>(round x).symm.trans ((congrArg (fun z=>drip n ∘ z) h).trans (round y))⟩
  have finite:(∑' v,f v)=∑v∈univ.map e,f v:=by
    apply tsum_eq_sum
    intro v outside
    have missing:¬retained n B v:=by
      intro yes
      apply outside
      exact mem_map.mpr ⟨drip n ∘ v,mem_univ _,canonical B v yes⟩
    simp [f,held,missing]
  change _=∑' v,f v
  rw [finite,Finset.sum_map]
  apply Finset.sum_congr rfl
  intro v _
  rw [fold];rfl

def quote (F:Frame G d) (B:ℕ) (T:Tile (wire G n) r) (row:Letter F):ℝ:=
  (pocket F (measured B T d (slots F row)) (label F row) (mint F row)).re

theorem plus (B:ℕ) (T V:Tile (wire G n) r):
    measured B (T+V) d s=measured B T d s+measured B V d s:=by
  ext x
  rw [_root_.add_apply,derivative,derivative,derivative,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  by_cases good:active B z <;> simp [masked,good,Pi.add_apply,add_mul]

theorem balance (F:Frame G d) (B:ℕ) (row:Letter F) (o:Loc G 1) (T:Tile (edgeL G) r)
    {w A:ℝ} (pos:0<w) (ht:Knoxville (fame _) w (0,o) T A):
    quote F B (sieve n T) row-pearlJ F T (mint F row)=
      quote F B (sieve n (lost n B T)) row-pearlJ F (lost n B T) (mint F row):=by
  have h:=funded (n:=n) B o T ht
  have l:Knoxville (fame _) w (0,o) (lost n B T) A:=by
    refine ⟨ht.1,(ENNReal.tsum_le_tsum fun v=>?_).trans ht.2⟩
    by_cases used:retained n B v <;> simp [lost,used]
  have s0:=sieve_sub_add n (penn_total h pos.le).of_norm (penn_total l pos.le).of_norm
  have finite:quote F B (sieve n T) row=
      quote F B (sieve n (held n B T)) row+quote F B (sieve n (lost n B T)) row:=by
    conv_lhs => rw [split n B T,s0.1]
    unfold quote
    rw [plus,bunch,Pi.add_apply,Complex.add_re]
  have cover:pearlJ F T (mint F row)=pearlJ F (held n B T) (mint F row)+pearlJ F (lost n B T) (mint F row):=by
    conv_lhs => rw [split n B T]
    unfold pearlJ
    rw [slate_plus h l pos,bunch,Pi.add_apply,Complex.add_re]
  have same:quote F B (sieve n (held n B T)) row=pearlJ F (held n B T) (mint F row):=by
    unfold quote
    rw [near_read B o T pos ht];rfl
  rw [finite,cover,same];ring

end YM.Integration.WilsonCapturedPrimaryPointWindow
