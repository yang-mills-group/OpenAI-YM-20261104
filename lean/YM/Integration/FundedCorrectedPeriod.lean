import YM.Integration.FundedRankTwoPackets
import YM.Integration.FundedPeriodPayload

/-! Realize a complete paid period bank with the original clover-corrected
quadratic rows and the original higher-rank rows, retaining every coupling grade. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FundedCorrectedPeriod
open Function Finset Lattice Wilson RG Marker
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open Comparison.Density Comparison.Density.Render AnalyticBridge.VerifiedReset WilsonStartup
open Extra.Iteration Next.Scheduling LocalComparison.Global IterationFour.Vacuum
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {σ C : ℝ}

def raw {r : ℕ} (P : ℕ → Atom G r) (n : Side) : Payload G n where
  labels := (rack n P 1 Frame.full).shelf ∘ numbering (Cycle n)
  action := (rack n P 1 Frame.full).table ∘ numbering (Cycle n)

theorem raw_unmasked (a : PrismA G) (U : Config G n) :
    unmaskedPayload (raw a.cells n) U = unmaskedPayload (FundedPeriodPayload.payload n a) U := by
  apply tsum_congr
  intro i
  change recipe 1 Frame.full _ * _ = (factor*1) * _
  simp [recipe,Frame.full]
  exact Or.inl rfl

theorem raw_amount (a : PrismA G) (B : BudgetPoint) (U : Config G n) :
    (raw a.cells n).amount B U = (FundedPeriodPayload.payload n a).amount B U := by
  apply tsum_congr
  intro i
  have h : (raw a.cells n).action i = (FundedPeriodPayload.payload n a).action i := by
    funext Z
    change recipe 1 Frame.full _ * _ = (factor*1) * _
    simp [recipe,Frame.full]
    exact Or.inl rfl
  rw [h]
  rfl

theorem residual_unmasked (P : Stack G 0) {d : ℕ} (hP : Commission P σ C d)
    (hd : 0 < d) (hσ : 0 < σ) (U : Config G n) :
    unmaskedPayload (FundedRankTwoPackets.payload P n 1) U = unmaskedPayload (raw P n) U := by
  let f (v : Cycle n) := factor * (P v.2).unmasked (v.1.view U) 0
  let e (v : Cycle n) := factor * Comparison.Density.Render.pollen (0:Site n) (P v.2) (v.1.view U)
  let bill (u : Seat n) := factor * ∑' j,(P j).unmasked (u.view U) 0
  have hf (u : Seat n) : HasSum (fun j => f (u,j)) (bill u) :=
    (NativeBoundedAtomSeries.value_summable P (fun _ => (0:Site n)) hσ
      (fun _ => le_rfl) hP.toll.2.1 (u.view U)).hasSum.mul_left factor
  have he (u : Seat n) : HasSum (fun j => e (u,j)) 0 := by
    simpa [e,Comparison.Density.Render.pollen] using
      (FundedRankTwoPackets.central P (hP.loan hd) (petals (u.view U) 0)).mul_left factor
  have orig := ConnectedActivityE6.Raw.finite_start f bill hf
  have clover : HasSum e 0 := by
    simpa only [Finset.sum_const_zero] using ConnectedActivityE6.Raw.finite_start e (fun _ => 0) he
  let N := numbering (Cycle n)
  calc
    _ = ∑' i : ℕ, (fun v => f v - e v) (N i) := by
      apply tsum_congr
      intro i
      change recipe 1 Frame.full (N i).2 * (_ - _) = _
      simp only [recipe,Frame.full,if_true,mul_one,f,e,mul_sub,Comparison.Density.Render.baseLine,N]
    _ = ∑' v : Cycle n, (f v - e v) := N.tsum_eq (fun v : Cycle n => f v-e v)
    _ = ∑' v : Cycle n, f v := by
      rw [(orig.sub clover).tsum_eq,orig.tsum_eq,sub_zero]
    _ = ∑' i : ℕ,f (N i) := (N.tsum_eq f).symm
    _ = _ := by
      apply tsum_congr
      intro i
      change factor*_ = recipe 1 Frame.full _ * _
      simp [recipe,Frame.full]
      exact Or.inl rfl

private def choosePayload (n : Side) (a : PrismA G) : Payload G n :=
  match a with
  | ⟨_,0,_,P⟩ => FundedRankTwoPackets.payload P n 1
  | ⟨_,_+1,_,P⟩ => raw P n

def credit (B : BudgetPoint) (σ C : ℝ) (a : PrismA G) : ℝ :=
  if a.rise=0 then Frame.cost B * (Frame.roseCharge 1 σ G B*C) else
    Frame.cost B * (|factor*1| * (Next.Scheduling.Wages.fund G B.power B.order (a.rise+2) B.supportExponent σ * B.threshold^(a.rise+2)*C))

def piece (n : Side) (B : BudgetPoint) (σ C : ℝ) (a : PrismA G) : Piece G n where
  power := a.grade
  rank := a.rise+2
  packet := choosePayload n a
  credit := credit B σ C a

theorem permits (Z : SeriesA G) (hZ : Draw Z σ C) (hG : G.Simple) (hn : 20<n.val)
    (B : BudgetPoint) (hσ : 0 < σ) (hB : B.supportExponent/B.B ≤ σ/4) (hc : 2≤B.B)
    (A : Activities G n) (hA : ∀ s b,A.Moves s b) :
    IterationFour.Vacuum.Render.permits (Z.map (piece n B σ C)) B := by
  intro L hL
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hL
  have H := hZ.2 a ha
  rcases a with ⟨d,r,hr,P⟩
  cases r with
  | zero =>
    simpa [piece,choosePayload,credit] using FundedRankTwoPackets.invoice P H hG hn 1 B hσ hB hc A hA
  | succ k =>
    let F := rack n P 1 Frame.full
    have hf := bandFits (F:=P) (n:=n) (a:=1) (h:=Frame.full) H.hue B
    have hnul := bandNull (n:=n) (F:=P) (a:=1) (h:=Frame.full) (by omega)
    have hr := Frame.authentic A hf hnul hG (by omega)
    have he := main_price (F:=P) (n:=n) (a:=1) (h:=Frame.full) A H.hue H.toll hσ hB
    change (raw P n).Invoice B _
    simp only [piece,credit,Nat.succ_ne_zero,if_false]
    refine ⟨hr.smooth,hr.at_flat,hr.vanish,?_,he⟩
    intro s b
    let m := Frame.move F A (hA s b)
    exact ⟨m.ep,fun i => ⟨m.reg_site i,m.reg_support i,m.valuesE i⟩⟩

theorem action (a : PrismA G) (ha : Commission a.cells σ C a.grade) (hd : 0<a.grade)
    (hσ : 0<σ) (U : Config G n) :
    unmaskedPayload (choosePayload n a) U = FundedPeriodAction.action n a U := by
  rw [← FundedPeriodPayload.unmasked n hσ a ha U,← raw_unmasked]
  rcases a with ⟨d,r,hr,P⟩
  cases r with
  | zero => exact residual_unmasked P ha hd hσ U
  | succ r => rfl

theorem restored (Z : SeriesA G) (hZ : Draw Z σ C) (hd : ∀ a∈Z,0<a.grade)
    (hσ : 0<σ) (B : BudgetPoint) (g : ℝ) (U : Config G n) :
    ActualGradedVacuum.restored (Z.map (piece n B σ C)) g U = FundedPeriodAction.rendered n Z g U := by
  induction Z with
  | nil => rfl
  | cons a Z ih =>
    change g^(a.grade+2-(a.rise+2))*unmaskedPayload (choosePayload n a) U +
      ActualGradedVacuum.restored (Z.map (piece n B σ C)) g U =
      g^(a.grade-a.rise)*FundedPeriodAction.action n a U + FundedPeriodAction.rendered n Z g U
    rw [show a.grade+2-(a.rise+2)=a.grade-a.rise by omega,
      action a (hZ.2 a List.mem_cons_self) (hd a List.mem_cons_self) hσ U,
      ih ⟨hZ.1,fun x hx=>hZ.2 x (List.mem_cons_of_mem a hx)⟩ (fun x hx=>hd x (List.mem_cons_of_mem a hx))]

def residual (B : BudgetPoint) {V : Type} [DecidableEq V] (R : Census V) (X : V→Type)
    (a : PrismA G) (U : Config G n) : ℝ :=
  match a with
  | ⟨_,0,_,P⟩ => ∑' i,(Frame.pours P B 1 V R X).real.value i U
  | ⟨_,_+1,_,_⟩ => 0

theorem weighted_field (a : PrismA G) (ha : Commission a.cells σ C a.grade) (hd : 0 < a.grade)
    (B : BudgetPoint) (hσ : 0<σ) (hB : B.supportExponent/B.B ≤ σ/4) (hc : 2≤B.B)
    (A : Activities G n) {V : Type} [DecidableEq V] (R : Census V) (X : V → Type) (U : Config G n) :
    (choosePayload n a).amount B U = PhysicalNext.Repeat.Song.billOf B a.cells U + residual B R X a U := by
  have base := (raw_amount a B U).trans (FundedPeriodPayload.masked n hσ a ha B U)
  rcases a with ⟨d,r,hr,P⟩
  cases r with
  | zero =>
    have H := FundedRankTwoPackets.all_fields P ha hd 1 B hσ hB hc A V R X U
    change _ = (FundedRankTwoPackets.payload P n 1).amount B U - (raw P n).amount B U at H
    change (FundedRankTwoPackets.payload P n 1).amount B U =
      PhysicalNext.Repeat.Song.billOf B P U + ∑' i,(Frame.pours P B 1 V R X).real.value i U
    rw [H,← base]
    ring
  | succ k =>
    simp only [choosePayload,residual,add_zero]
    exact base

theorem masked_list (Z : SeriesA G) (hZ : Draw Z σ C) (hd : ∀ a∈Z,0<a.grade)
    (B : BudgetPoint) (hσ : 0<σ) (hB : B.supportExponent/B.B ≤ σ/4) (hc : 2≤B.B)
    (A : Activities G n) {V : Type} [DecidableEq V] (R : Census V) (X : V→Type)
    (g : ℝ) (U : Config G n) :
    IterationFour.Vacuum.Render.renders (IterationFour.Vacuum.Render.prefactor g) B U (Z.map (piece n B σ C)) =
      (Z.map fun a => g^((a.grade:ℤ)-(a.rise+2:ℕ)) * PhysicalNext.Repeat.Song.billOf B a.cells U).sum +
      (Z.map fun a => g^((a.grade:ℤ)-(a.rise+2:ℕ)) * residual B R X a U).sum := by
  induction Z with
  | nil => simp [IterationFour.Vacuum.Render.renders]
  | cons a Z ih =>
    simp only [List.map_cons,IterationFour.Vacuum.Render.renders,List.sum_cons]
    rw [ih ⟨hZ.1,fun x hx=>hZ.2 x (List.mem_cons_of_mem a hx)⟩ (fun x hx=>hd x (List.mem_cons_of_mem a hx))]
    change g^((a.grade:ℤ)-(a.rise+2:ℕ)) * (choosePayload n a).amount B U + _ = _
    rw [weighted_field a (hZ.2 a List.mem_cons_self) (hd a List.mem_cons_self) B hσ hB hc A R X U]
    ring

end YM.Integration.FundedCorrectedPeriod
