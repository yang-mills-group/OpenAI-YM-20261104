import YM.UVExtension.Gale.Havens
import YM.OPE.Columns.Accounts
import YM.OPE.Columns.Buy
import YM.UVExtension.Gale.Sheets
/-!
# RG16. The actual UV column supplies the OPE triangle

The KFactory (G.08) exported in `Reports.ultraviolet` uses the UV extension's
`tide` chain, not the chain chosen in `squad_columns`. We prove the estimate
on the former chain. Don't change representatives. Use both norm estimates on
the leading map, and the full terrain norm of the previous actual column in
`sailC`. It is OK to forget the shared polynomial accounting when **exporting**
this coordinate estimate. It generally is not OK to use the estimate to
reconstruct that accounting.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Juniper
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat
open UVExtension Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Planned.GuardedAtom Guard Mast Flake Fitted Bid Motion
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace

/-- Extra pre-L reserve: our argument pays both the E and K costs, not replacing
  the sum of the two by a norm which is only their max. -/
def ColumnPre {G : Gauge} (S : Sheet G) (D : Rolls S) : Prop :=
  ∀ j d, d ≤ j →
    let u := Doors.rate (D.L j)
    (u + 2 * u * (S.profile j).columns) * orbitCost ((Labels.frames G).level d) ≤ barunit (D.L j)

variable {G : Gauge} {M : Metals G} {P : Rolls M.p} {A : Alloy M P}
    {X : Roost.Factor A} {hG : G.Simple} (S : Uses X hG)
    {C : ℕ → ℝ} {W : Bid.Worth} (R : Legato.Bandage X C W)

set_option quotPrecheck false
local notation "U!" => A.B.a
local notation "J!" => (U!).clock.J
local notation "F!" => (frames G)
open Lacing.RoutesF

section heads
variable (d N m n : ℕ) (hn : m < N) (hd : d+3 ≤ A.B.a.clock.J m)
local notation "k" => leadF S R d N m hd
local notation "u!" => (U!).S.block m

include S R hn hd
/-- Restore the real heading on `tide` using the true-offset wire. The caller
  uses the *fine* stage for L and column cost. No complex-frame growth is paid
  because we never continue away from the real offset in this lemma. -/
lemma true_heading (z : Rose S) :
    (∀ x, ((F!).level d).coeffSize ((k).map x) ≤ C (J! (m+1)) * ((F!).level d).coeffSize x ∧
      ((F!).level d).coeffSize ((k).map.symm x) ≤ C (J! (m+1)) * ((F!).level d).coeffSize x) ∧
    Tips (tide S R d N m n z) u! k (Doors.rate u!) (C (J! (m+1))) := by
  obtain ⟨b,hb⟩ := yells S N m n hn z
  obtain ⟨Q,U,hX,h⟩ := wire S R d N m n b hn hd
  rw [h z hb, Push.PriceCompiler.block_eq A.B.valid m]
  exact ⟨(tum S R d N m n b hn hd Q hX).1,(tum S R d N m n b hn hd Q hX).2.1⟩
end heads

section Stacking
variable {B : Org.Bolt A} {t : ℕ → ℕ} (arc : Upland.Arc X S B) (k₀ : Lisle t A.B.a)
local notation "K!" => centerB S arc
local notation "ρ" => Mast.roseA S
local notation "H!" => Orchard.Path S ρ

include k₀
set_option maxHeartbeats 800000 in
lemma stacked (hp : ColumnPre M.p P) (d N n : ℕ) (hn : t d ≤ N) :
    Legato.Bandage.StackedColumns K! (Cellar.gate ρ (cellar S R arc t k₀) d N n) (t d) W := by
  let T := cellar S R arc t k₀
  let Z := Cellar.gate ρ T d N n
  let Y := Cellar.cantors ρ T d n
  let V := Y.song N
  let hY := Y.lyr N hn
  let F := (F!).level d
  have hZ : Z.entries = (V.draft H!).inits := ((Cellar.launch ρ T d N n).choose_spec hn).2
  have hEq (i) (hi : t d ≤ i) (ht : i ≤ N) :
      (fun v => (Z.entries i v).x) = (V.tone i).index := by
    rw [hZ]; exact funext ((hY.earned.earned i hi ht).currents)
  intro m hm he
  change Triangle H! W m (fun v => (Z.entries (m+1) v).x) (fun v => (Z.entries m v).x)
  rw [hEq m hm he.le,hEq (m+1) (hm.trans m.le_succ) he]
  have ho : d+3 ≤ J! m := (k₀.tops d).trans ((U!).fits.mono hm)
  let j := J! (m+1)
  let L := (U!).S.block m
  let k := leadF S R d N m ho
  have hl : ∃ c, Push.Local.Leading (k).map.toLinearMap c := by
    exact ⟨_, Planned.PrimaryIntegral295.PPX.Seal.cap_lead (localSection G d) (sound G d)
      M.p.kernel.penalty_pos ((U!).clock.adm m) (Next.Foundations.valuation G d)
        (Planned.PrimaryIntegral295.Warehouse.flight H! N m)
        (le_trans (by omega : d ≤ J! m) (step_paid U! m).1) (Flake.vision R d m ho)⟩
  have h₁ := true_heading S R d N m n he ho (Orchard.rose0 S)
  have hcB : Buys H! F W m (C j) (Doors.rate L) := R.clock.fits H! rfl m d (by omega)
  let s := ((U!).params (m+1)).columns
  have hcC : C j ≤ W.K j := by
    refine (?_ : C j ≤ _).trans hcB.funds
    have hx := hcB.cost
    change C j ≤ (C j + Doors.rate L * s)*orbitCost F
    have hu : 0 ≤ Doors.rate L * s := mul_nonneg (Doors.rate_pos _).le (zero_le_one.trans ((U!).params (m+1)).columns_ge)
    exact (le_mul_of_one_le_right (zero_le_one.trans hx) (orbitCost_one_le F)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hu) (zero_le_one.trans (orbitCost_one_le F)))
  refine ⟨k,hl,fun y => ?_,fun v => ?_⟩
  · have ha := mul_le_mul_of_nonneg_right hcC (Work.G08.size_nonneg F y)
    exact ⟨((h₁.1 y).1).trans ha, ((h₁.1 y).2).trans ha⟩
  let ψ := fun _ : Motion => T.paths S ρ R d n m N
  let f := fun _ : Motion => hY.Vista (m+1)
  have hf (i : Motion) (x) : ‖f i x‖ ≤ s * F.coeffSize (F.core x) := by
    dsimp only [f]; rw [hY.takes _ (hm.trans m.le_succ) he]; exact Lyrics.climbs hY _ (hm.trans m.le_succ) he x
  have hsp := (Lyrics.spaceF hY m hm he v).1
  let x := (V.tone (m+1)).index v
  let hn' := glaring U! m n
  let u := Doors.rate L
  have hP : ∀ i : Motion, Tips (ψ i) L k u (C j) := fun _ => h₁.2
  change F.coeffSize ((V.tone m).index v - k.leads L x) ≤ Bid.barunit L * F.coeffSize (F.core x)
  rw [show (V.tone m).index v= major ψ f hn' x from hsp]
  refine (sailC ψ f hn' hP (zero_le_one.trans ((U!).params (m+1)).columns_ge) hf x).1.trans
    (mul_le_mul_of_nonneg_right (?_ : (u+2*u*s)*orbitCost F ≤ Bid.barunit L) (Work.G08.size_nonneg ..))
  have hs : s=(M.p.profile j).columns := congr_arg Stage.columns (params_eq A.B.valid (m+1))
  have heL : L=P.L j := Push.PriceCompiler.block_eq A.B.valid _
  dsimp only [u]; rw [heL,hs]; exact hp j d ((Nat.le_add_right ..).trans (ho.trans (step_paid U! m).1))
end Stacking
end YM.Juniper
