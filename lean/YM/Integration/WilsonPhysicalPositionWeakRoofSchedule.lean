import YM.TraceExtension.Prom.Order.State

/-! Larger common weak reporting apertures are bought before the Wilson block
lengths are chosen. The room for every next grade is a single countable request. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.MergeProof.East.WilsonPhysicalPositionWeakRoofSchedule
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
  PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage Next.Rank Next.Rank.Tapes.West Perch Atlas Station
open Cells Edition Glyph Rise Alarm Paint Vac.Numbers Next.Rank.East Further.CorrectedLift Glimmer
open Analysis Next.UVStress Climb Ward Supply Accent
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge} {X:Sheet G} {D:Rolls X} {T:Protection D} {E:Delays T} {Z:Bar E}

def width (a:ℕ → Fin 3 → ℝ) (d:ℕ):ℝ :=
  1 + max 0 (a (d+1) 0 - a d 0)

theorem next_base (a:ℕ → Fin 3 → ℝ) (d:ℕ):
    a (d+1) 0 + 1 ≤ a d 0 + width a d := by
  unfold width
  linarith only [le_max_right 0 (a (d+1) 0 - a d 0)]

structure Asked (X:Sheet G) (B:MapPrices) (m:ℕ → ℕ) : Prop where
  menu : ∃ a:ℕ → Fin 3 → ℝ, Monotone (fun d=>a d 0) ∧ (∀ (d:ℕ) (i:Fin 3), (d:ℝ)+6 ≤ a d i) ∧
    (∀ d, ∃ c, Checks (a d 0) (a d 1) (a d 2) c (trays d) d) ∧
    ∃ P:∀ d, Fin 3 → Tapes.Panel d, ∃ K, AskSky X B trays m P K ∧
      ∀ d i, (P d i).arc = a d i + width a d

theorem shift_checks {a b e c x:ℝ} {n d:ℕ} (paid:Checks a b e c n d) (hx:0≤x) :
    Checks (a+x) (b+x) (e+x) c n d := by
  have ab : (a+x)-(b+x)=a-b := by ring
  have ae : (a+x)-(e+x)=a-e := by ring
  exact ⟨paid.negative,by linarith only [paid.boundA],
    by linarith only [paid.boundB],by simpa only [ab] using paid.limitA,
    by rw [ae];linarith only [paid.limitB,hx]⟩

private def floorAt (a:ℕ → Fin 3 → ℝ) : ℕ → ℝ
  | 0 => a 0 0
  | d+1 => max (floorAt a d) (a (d+1) 0)

private theorem dominates (a:ℕ → Fin 3 → ℝ) (d:ℕ) : a d 0 ≤ floorAt a d := by
  cases d with
  | zero => rfl
  | succ d => exact le_max_right ..

private theorem increasing (a:ℕ → Fin 3 → ℝ) : Monotone (floorAt a) :=
  monotone_nat_of_le_succ fun _=>le_max_left ..

theorem original (X:Sheet G) (B:MapPrices)
    (late:Tendsto (fun i=>(X.profile i).order) atTop atTop) : ∃ m, Asked X B m := by
  choose base large c tests using fun d => raises d (trays d)
  let a (d:ℕ) (i:Fin 3):=base d i + (floorAt base d - base d 0)
  have anchor (d:ℕ):a d 0 = floorAt base d := by dsimp [a];ring
  have monotone : Monotone (fun d=>a d 0) := by
    intro i j hij
    simpa only [anchor] using increasing base hij
  have size (d:ℕ) (i:Fin 3) : (d:ℝ)+6 ≤ a d i :=
    (large d i).trans (le_add_of_nonneg_right (sub_nonneg.mpr (dominates base d)))
  have checks (d:ℕ):Checks (a d 0) (a d 1) (a d 2) (c d) (trays d) d:=
    shift_checks (tests d) (sub_nonneg.mpr (dominates base d))
  have floor (d:ℕ) (i:Fin 3): (d:ℝ)+7 ≤ a d i + width a d := by
    unfold width
    linarith only [size d i,le_max_left 0 (a (d+1) 0 - a d 0)]
  obtain ⟨m,P,K,arc,ask⟩:=asks_sky X B trays (fun d i=>a d i + width a d) floor
    (fun _=>Nat.le_add_left ..) late
  exact ⟨m,⟨a,monotone,size,fun d=>⟨c d,checks d⟩,P,K,ask,arc⟩⟩

private def restrictPanel (d:ℕ) (P:Tapes.Panel d) (b:ℝ)
    (floor:(d:ℝ)+6 ≤ b) (roof:b ≤ P.arc) : Tapes.Panel d :=
  { P with
    arc := b
    huge := floor
    bag := fun i => vent (P.bag i) b
    factor := fun _ => rfl
    stable := P.stable
    vital := P.vital
    loose := fun i =>
      (le_trans (add_le_add_left (add_le_add_left
        (mul_le_mul_of_nonneg_right roof (Nat.cast_nonneg _)) _) _) (P.loose i)) }

structure Window {C:Family G} (B:Binding C) (H:C.Makes) (O:HaarBudget G) (J:ChartRatio G)
    (d:ℕ) (z:ℝ) (a:Fin 3 → ℝ) (w:ℝ) : Prop where
  shared : ∃ P:ℝ → Fin 3 → Tapes.Panel d, ∃ c,
    (∀ x∈Icc 0 w, Checks (a 0+x) (a 1+x) (a 2+x) c (trays d) d) ∧
    (∀ x∈Icc 0 w, ∀ i, (P x i).arc=a i+x ∧
      (P x i).currency=(P 0 i).currency ∧ (P x i).θ=(P 0 i).θ) ∧
    (∀ x y i j, (P x i).θ=(P y j).θ ∧ ∀ k:ℕ,
      ((P x i).bag k).era.coast.Q=((P y j).bag k).era.coast.Q) ∧
    ∀ᶠ k in atTop, ∀ x∈Icc 0 w, ∃ Y, PoisedSky (P x) B H O J (trays d) z k Y

theorem paid (B:MapPrices) (m:ℕ → ℕ) (booking:Asked X B m) (O:HaarBudget G)
    (J:ChartRatio G) (localRatio:LocalRatio J) (lengths:∀ i,m i ≤ (D.L i).val)
    (simple:G.Simple) (z:ℕ → ℝ) (hz:∀ i,0≤z i) (prior:Wait Z) :
    ∃ a:ℕ → Fin 3 → ℝ, Monotone (fun d=>a d 0) ∧ (∀ (d:ℕ) (i:Fin 3),(d:ℝ)+6 ≤ a d i) ∧ ∃ W:Wait Z,
      prior.minLength ≤ W.minLength ∧ prior.readyHere ≤ W.readyHere ∧ prior.window ≤ W.window ∧
      ∀ C:Family G, Paid W C.path.levels → ∀ B':Binding C, B'.prices=B →
        ∀ H:C.Makes, ParadeX C → ∀ d, Window B' H O J d (z d) (a d) (width a d) := by
  obtain ⟨a,monotone,size,checks,P,K,ask,arcs⟩:=booking.menu
  obtain ⟨W,Q,hm,hv,hw,geometry,pins,issued⟩:=forwardSky B prior ask O J localRatio lengths
    (fun _=>Nat.le_add_left ..) hz simple
  refine ⟨a,monotone,size,W,hm,hv,hw,fun C calendar binding same H path d=>?_⟩
  have arc (i) : (Q d i).arc=a d i+width a d := (geometry d i).1.symm.trans (arcs d i)
  have positive:0≤width a d := by unfold width;linarith only [le_max_left 0 (a (d+1) 0-a d 0)]
  let clamp (x:ℝ):=max 0 (min (width a d) x)
  have inside (x):clamp x∈Icc 0 (width a d):=
    ⟨le_max_left ..,max_le positive (min_le_left ..)⟩
  let panel (x:ℝ) (i:Fin 3):=restrictPanel d (Q d i) (a d i+clamp x)
    ((size d i).trans (le_add_of_nonneg_right (inside x).1))
    ((arc i).symm ▸ add_le_add_right (inside x).2 _)
  obtain ⟨c,tests⟩:=checks d
  refine ⟨panel,c,fun x hx=>shift_checks tests hx.1,fun x hx i=>⟨?_,rfl,rfl⟩,fun _ _ i j=>pins d i j,?_⟩
  · apply congr_arg (a d i+·)
    unfold clamp
    rw [min_eq_right hx.2,max_eq_right hx.1]
  filter_upwards [eventually_all.mpr (fun i=>issued C calendar binding same d i),
    stagingSky (ι:=Fin 3) (n:=trays d) (z:=z d) binding H O J simple 0 path
      (Q d 0).θ (Q d 0).enough] with k rods install x hx
  have charge i : topL C.path.levels k ≤ C.path.levels.clock.monitor k ∧
      ∃ l r, LegacyCostSky binding J (-3) (z d) ((panel x i).bag (C.path.levels.clock.J k))
        k (trays d) d O l r := by
    have floor:0≤a d i+clamp x := by linarith only [size d i,Nat.cast_nonneg (α:=ℝ) d,(inside x).1]
    refine rods i _ floor ?_
    rw [(Q d i).factor,arc]
    exact add_le_add_right (inside x).2 _
  exact install (panel x) rfl (fun i=>pins d 0 i) (charge 0).1 (fun i=>(charge i).2)

/-- All the original apertures of one finite experiment use one table at their
common date, prior to the two cutoff arguments. -/
theorem council {C:Family G} {B:Binding C} {H:C.Makes} {O:HaarBudget G} {J:ChartRatio G}
    {d:ℕ} {z:ℝ} {a:Fin 3 → ℝ} {w:ℝ} (room:Window B H O J d z a w)
    (simple:G.Simple) (actual:ParadeX C) :
    ∃ P:ℝ → Fin 3 → Tapes.Panel d, ∃ c,
      (∀ x∈Icc 0 w, Checks (a 0+x) (a 1+x) (a 2+x) c (trays d) d) ∧
      (∀ x∈Icc 0 w, ∀ i, (P x i).arc=a i+x ∧
        (P x i).currency=(P 0 i).currency ∧ (P x i).θ=(P 0 i).θ) ∧
      ∀ n:ℕ, ∀ᶠ k in atTop, ∀ x:Fin (n+1) → ℝ, (∀ i,x i∈Icc 0 w) →
        ∃ Y, PoisedSky (fun j:Fin (n+1) × Fin 3=>P (x j.1) j.2) B H O J (trays d) z k Y := by
  obtain ⟨P,c,checks,axes,pins,single⟩:=room.shared
  refine ⟨P,c,checks,axes,fun n=>?_⟩
  let ref:Fin (n+1) × Fin 3:=⟨0,0⟩
  filter_upwards [single,stagingSky (ι:=Fin (n+1) × Fin 3) (n:=trays d) (z:=z) B H O J
    simple ref actual (P 0 0).θ (P 0 0).enough] with k issued combine x admitted
  obtain ⟨_,base⟩:=issued (x 0) (admitted 0)
  apply combine (fun j=>P (x j.1) j.2) (pins (x 0) 0 0 0).1
    (fun j=>pins (x 0) (x j.1) 0 j.2) base.limit
  intro j
  obtain ⟨_,file⟩:=issued (x j.1) (admitted j.1)
  obtain ⟨l,r,cost,_⟩:=file.supply j.2
  exact ⟨l,r,cost⟩

end YM.MergeProof.East.WilsonPhysicalPositionWeakRoofSchedule
end
