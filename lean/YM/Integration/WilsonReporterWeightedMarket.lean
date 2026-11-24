import YM.Integration.WilsonReporterWeightedDeployment
import YM.Integration.WilsonReporterWeightedCash
import YM.Integration.WilsonReporterWeightedConnected
import YM.Integration.WilsonReporterWeightedOrdinary

/-! Dated purchase on the actual PoisedSky stamp. The ordinary comparison on
the selected held teacher and the unamplified free Maxwell profile share one
source, placement, thermal clock and reflection bank. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReporterWeightedMarket
open Next.Rank Next.Rank.Tapes Next.Rank.Tapes.West MergeProof MergeProof.Accent
open PhysicalNext PhysicalNext.RankCovariance PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft
open Precision Function Filter Set Lattice Wilson RG Source Cells Extraction Bid Station Atlas Ribbon
     Edition Normal Perch Market Glyph Exponential Marker Extra.Histories Radian
     PhysicalNext.Repeat.Legato.Bandage
open scoped Topology BigOperators Classical

variable {G : Gauge} {C : Family G} {W : Bid.Worth} {u₀ ψ φ δ : ℕ → ℝ} {r : ℕ → ℕ}
    {door : ∀ N p m : ℕ, m<N → GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (B : Binding C) (H : C.Makes) (h : G.Simple)
    (source : Scrim C W u₀ ψ φ δ (fly C.path.levels) r door)
    (O : HaarBudget G) (J : ChartRatio G) {m u D : ℕ} {d : Fin (m+1) → ℕ}
    (g : (i : Fin (m+1)) → C.label (d i)) {K : Set (Points (m+1))}
local notation "AX" => C.path.levels

def radius (add : Fin (m+1) → ℝ) (s : ℝ) (i : Fin (m+1)) := bill (add i) s

theorem compact (hK : IsCompact K) (sep : K⊆conf _) : ∃ A : ℝ, ∀ y∈K,
    ‖Read.maxProfile C y (jointX g)‖ ≤ A ∧
    Poly.price (fun _ => 1) (Read.maxProfile C y (jointX g)) ≤ A := by
  let f := fun y => Read.maxProfile C y (jointX g)
  have smooth := Maxwell.table_smooth C.labels
  have con : ContinuousOn f K := by
    apply continuousOn_pi.mpr; intro i
    exact (Read.profile_part_cont (standard C) smooth _ i).mono sep
  have price : ContinuousOn (fun y=>Poly.price (fun _=>1) (f y)) K := by
    unfold Poly.price
    exact continuousOn_finsetSum _ (fun i _=>continuousOn_const.mul
      ((Read.profile_part_cont (standard C) smooth _ _).norm.mono sep))
  obtain ⟨A,qa⟩ := (hK.image_of_continuousOn con.norm).bddAbove
  obtain ⟨B,qb⟩ := (hK.image_of_continuousOn price).bddAbove
  exact ⟨max A B, fun y hy=>⟨(qa (Set.mem_image_of_mem _ hy)).trans (le_max_left _ _),
    (qb (Set.mem_image_of_mem _ hy)).trans (le_max_right _ _)⟩⟩

theorem targets {q k : ℕ} {b : ℝ} {x : Points q} (fit : FitSky AX b k x)
    (V W : Fin q → (standard C).Tag)
    (same : Read.maxProfile C (tested AX b k x) V = Read.maxProfile C (tested AX b k x) W) :
    Ship.targetsSky C V fit = Ship.targetsSky C W fit := by
  have H₁ := Read.cumulative C (tested AX b k x) V (Ship.fittingSky fit)
  have H₂ := Read.cumulative C (tested AX b k x) W (Ship.fittingSky fit)
  rw [same] at H₁
  exact H₁.uniq H₂

theorem permitted {k k₀ : ℕ} {α : Purse} {z l v : ℝ}
    (L : LegacyCostSky B J (-3) z α k u D O l v)
    (enough : C.path.levels.clock.J k₀+1<C.path.levels.clock.J k) : k₀≤Station.widthSky AX α.band k := by
  by_contra! younger
  have walk := L.age.allot.permitted.bracket _ (le_refl _) ((widerSky _ _ _).trans (beforeSky ..))
  have clock := (C.path.levels).fits.mono younger.le
  omega

def Sale (panel : Tapes.Panel D) (k : ℕ) (A reserve z : ℝ) : Prop :=
  let α := panel.bag (C.path.levels.clock.J k)
  let s := clim AX k
    ∀ (add : Fin (m+1) → ℝ) (_ : ∀ i, add i≤reserve) (l v : ℝ)
      (L : LegacyCostSky B J (-3) z α k u D O l v) (N p : ℕ) (fine : k<N)
      (V : Rep G (C.side k p)) (_ : ActumSky B H O J panel L V fine)
      (x : Points (m+1)) (_ : tested AX α.band k x ∈ K) (_ : FitSky AX α.band k x)
      (F : (i : Fin (m+1)) → StampDuty C k N p (d i) α.taylor V α.era.coast.Q (PhysicalNext.RankCovariance.stamp AX N p))
      (t : (i : Fin (m+1)) → C.label (d i)),
    (∀ i, Price.Solves C (mag AX α.band k) (d i) k N p (F i).T (g i) (t i)) →
    let a := radius add s
    let w := WilsonReporterWeightedOrdinary.stretch C a g
    let f := WilsonReporterWeightedOrdinary.stretch C a t
    let visits := tested AX α.band k x
    Read.maxProfile C visits (jointX w) = Read.maxProfile C visits (jointX g) →
    (∀ y : Chamber G C.S (middleSky AX α.band k) p → ℝ, Wind AX y (fraction (m+1) α.taylor s) →
      ∀ i : modes (Fin (m+1)), ‖(spunW (track (PhysicalNext.RankCovariance.stamp AX N p))
        (fun j => prefaced (F j) (f j) (Station.choose AX α.band k x j)) (beforeSky AX α.band k) y).part i -
        (Read.maxProfile C visits (jointX g)).part i‖ ≤ bill (-63/64) s) →
    (∀ i, Interior ((Ship.yardSky C α.band fine.le p).chamber 0)
      (Read.probes C N p k (Station.choose AX α.band k x) (q_asked (C:=C) f) i)) →
    (∏ i, a i) * ‖C.numeric N p (q_asked (C:=C) t) (fun i =>
        Cells.location C.S k N p (Station.choose AX α.band k x i)) -
        (standard C).useAt (standard C) visits (jointX g)‖ ≤ A*Ship.budget AX u k

include source in
theorem onCourse {α : Purse} {l v z A : ℝ} {N p k : ℕ} {x : Points (m+1)}
    (grades : ∀ i,d i≤D) (two : 2≤u) (ones : m+1≤u)
    (L : LegacyCostSky B J (-3) z α k u D O l v) (fine : k<N)
    (P : (i:ℕ) → Rep G (C.side i p))
    (Fd : WhipSky B J α L.hours L.moves (isohypse H fine.le p) P (widthSky AX α.band k) le_rfl)
    (hpos : 0≤α.band) (bank : Ship.bank O AX (widthSky AX α.band k))
    (ticket : ∀ q : BudgetPoint, q.B ≤ Perch.walls (clim AX k) → Flux.Tickets q (Flux.kinetics (clim AX k)))
    (refs : ∀ i,C.ref (d i)≤k) (window : WallsSky α.band grades g K α.taylor k)
    (fit : FitSky AX α.band k x) (hx : tested AX α.band k x ∈ K)
    (F : (i:Fin (m+1)) → StampDuty C k N p (d i) α.taylor (P k) α.era.coast.Q
      (PhysicalNext.RankCovariance.stamp AX N p))
    (a : Fin (m+1) → ℝ) (pos : ∀ i,0<a i) (t : (i:Fin (m+1))→C.label (d i)) :
    let w := WilsonReporterWeightedOrdinary.stretch C a g
    let f := WilsonReporterWeightedOrdinary.stretch C a t
    let y := tested AX α.band k x
    Read.maxProfile C y (jointX w) = Read.maxProfile C y (jointX g) →
    Poly.price (fun _=>1) (Read.maxProfile C y (jointX g)) ≤ A →
    (∀ i,α.cash (clim AX k)*Spindle.moneys C (d i) k N p (f i) ≤ bill (-8) (clim AX k)) →
    (∀ i,Rise.coin ((F i).W (f i)) ≤ α.principal (clim AX k)) →
    (∀ i,Vac.Numbers.Hat (clim AX k)^z * Spindle.paid C (d i) k N p (f i) ≤ fly AX (d i) k) →
    WilsonReporterWeightedReturn.Signed (P:=P) (ξ:=α) w f fit F →
    (∀ i,Interior ((Ship.yardSky C α.band fine.le p).chamber 0)
      (Read.probes C N p k (Station.choose AX α.band k x) (q_asked (C:=C) f) i)) →
    (∏ i, a i) * ‖C.numeric N p (q_asked (C:=C) t) (fun i =>
        Cells.location C.S k N p (Station.choose AX α.band k x i)) -
        (standard C).useAt (standard C) y (jointX g)‖ ≤ A*Ship.budget AX u k := by
  intro w f y same price cash coins hard regular inside
  have em := targets fit (jointX w) (jointX g) same
  have target : Peak.sufficientlySky C (jointX w) α.band x k := by
    intro hf per cutoff top i
    rw [show Ship.targetsSky C (jointX w) hf=Ship.targetsSky C (jointX g) hf from em]
    exact (window.merry x hx).route hf per cutoff top i
  have kept := WilsonReporterWeightedDeployment.original B H J source L fine Fd hpos bank ticket refs F w f fit
    two ones ((window.replies x hx fit L.age.allot.permitted).1 p N fine.le) cash coins hard target regular
  have earn := WilsonReporterWeightedOrdinary.original C H fine.le fit a pos g t inside kept
  rw [show Read.maxProfile C (tested AX α.band k x) (jointX (WilsonReporterWeightedOrdinary.stretch C a g))=
    Read.maxProfile C y (jointX g) from same] at earn
  exact earn.trans (mul_le_mul_of_nonneg_right price (Ship.budget_pos AX u k).le)

include h source in
theorem original (panels : ℕ → Tapes.Panel D) (θ : ℕ) (e cap reserve z : ℝ)
    (school : ∀ k, (panels k).θ=θ) (budget : ∀ k, (panels k).currency=e)
    (arc : ∀ k, (panels k).arc ≤ cap)
    (large : ∀ k j, (panels k).arc*D+D+2+reserve ≤ ((panels k).bag j).credit)
    (grades : ∀ i, d i ≤ D) (tax : ∀ i, generator G (d i) ≤ z)
    (ones : m+1≤u) (two : 2≤u) (hK : IsCompact K) (sep : K⊆conf _) :
    ∃ A : ℝ, ∀ᶠ k : ℕ in atTop, Sale (u:=u) (K:=K) B H O J g (panels k) k A reserve z := by
  obtain ⟨A,bounded⟩ := compact g hK sep
  refine ⟨A,?_⟩
  let c : ℝ := D+6
  have lo : 6≤c := by unfold c; linarith only [Nat.cast_nonneg (α:=ℝ) D]
  have minimum (k) : c≤(panels k).arc := (panels k).huge
  have room := mural_castSky grades g hK sep H h c lo
    (fun i=>by unfold c; linarith only [Tapes.savings C (d i),show (d i:ℝ)≤D from Nat.cast_le.mpr (grades i)])
    θ (fun k=>(panels k).arc) minimum cap arc
  obtain ⟨k₀,old⟩ := eventually_atTop.mp (Ship.banking AX O h)
  filter_upwards [room,WilsonReporterWeightedCash.original C h H source θ e z d g grades tax,
    WilsonReporterWeightedConnected.original (C:=C) (n:=m+1) h A,
    (hat_rate AX h).eventually Flux.timing,(C.path.levels).fits.deep.eventually_gt_atTop ((C.path.levels).clock.J k₀+1),
    eventually_all.mpr (fun i:Fin (m+1)=>eventually_ge_atTop (C.ref (d i)))] with k walls wealth connected ticket enough refs
  unfold Sale
  intro α s add growth l v L N p fine V day x hx fit F t solved a w f visits same tests inside
  obtain ⟨P,eq,Fd⟩ := day.acts
  subst V
  have ht : α.taylor=θ := ((panels k).stable _).trans (school k)
  have he : α.f=e := ((panels k).vital _).trans (budget k)
  have hb : α.band=(panels k).arc := (panels k).factor _
  have hpos : 0≤α.band := hb ▸ (show 0≤(panels k).arc by linarith only [minimum k,lo])
  have account := wealth α α.band reserve hpos add he ht (hb ▸ large k _) growth L.moves.year N p fine.le F t solved
  have window : WallsSky α.band grades g K α.taylor k := by rw [hb,ht]; exact walls
  let allowed := L.age.allot.permitted
  have oldEnough := permitted B O J L enough
  have bounded' : ‖Read.maxProfile C visits (jointX w)‖≤A := by rw [same]; exact (bounded visits hx).1
  have regular := connected (P:=P) (ξ:=α) fit F w f bounded' (fun y event i=>by
    show ‖_- (Read.maxProfile C visits (jointX w)).part i‖≤_; rw [same]; exact tests y event i)
  exact onCourse B H source O J g grades two ones L fine P Fd hpos (old _ oldEnough) ticket refs window fit hx
    F a (fun _=>(Real.exp_pos _)) t same (bounded visits hx).2 account.2.1 account.2.2.1 account.2.2.2 regular inside

end YM.Integration.WilsonReporterWeightedMarket
