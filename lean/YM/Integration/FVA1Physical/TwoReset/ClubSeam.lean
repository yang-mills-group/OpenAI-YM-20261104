import YM.Integration.FVA1Physical.TwoReset.Artwork
import YM.Integration.FVA1Physical.TwoReset.Seats
import YM.Integration.FVA1Physical.TwoReset.PalettePages
import YM.QuadraticLocal.Fk.Untag

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.FVA1Physical.TwoReset
open Function Filter Finset Lattice RG RG.Supply Pressure Input Org Precision Tree YM.Wilson
open Push Push.AbsoluteSums PriceCompiler PhysicalNext Repeat Further.PhysicalPeriodLimitF933
open ConnectedActivityE6 Push.Uniform Next.Scheduling Extra.Iteration ThroughLaunch Roost
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Echo QuadraticLocal.Mentor QuadraticLocal.Earn RemainderComparison
open Seedlings Offices Cruise
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire
open Laurent Stationary AllOrder.Ink AllOrder.Ink.Money Comparison.RG02 Kinetic.Port Pane
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {X : Metals G}
variable (R : Roots (G:=G) X.p.profile X.K X.p.kernel) (D : Rolls X.p) (Q : R.Tab D)
variable (A : Alloy X D) (φ : ℕ→ℕ) (K0 : Offices.Books R D Q φ)
variable {m : ℕ}
local notation "x" => A.B.a.clock.J (m+1)
local notation "y" => A.B.a.clock.J m
variable (o : Opportunity (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (E : Epoch R D (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) o)
    (T : Card D R (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) (A.B.a.clock.adm (m+1)) (Burn.horizon E.vac))
local notation "baseHeight" => Burn.horizon E.vac

variable {ι V α : Type} [Fintype V] [DecidableEq V]
variable {c f : Side}
variable (u : f.val = c.val * (A.B.a.S.block m).val)
variable {J : Passport f V} {S : Marker.Census V} (M : ι → Row J S G α) (C : Club M)
variable (p : ℕ)
variable (v : Voter M (QuadraticLocal.Poetry.Agenda.seed R φ (Burn.horizon E.vac) (A.B.a.clock.J (m+1)))
    p o.count o.stage E.vac (A.B.a.clock.J m))
local notation "N" => Cruise.publish R D Q A φ K0 o E u M p v T
local notation "keys" => Club.Keys M C
local notation "loan₁" => (fun i: Club.Keys M C => (Club.troops M C i).lamp)
local notation "ticket₁" => Cruise.ticket R D A φ o E M C p v
local notation "rules₁" => Cruise.rules R D A φ o E u M C p v
local notation "art" => Mentor.artifact R D A φ o E ticket₁ rules₁ T
local notation "ledger" => (K0.lore x y o E ticket₁)
local notation "angle" => (ticket₁).val.angle
local notation "epoch" => Epoch.data R D Q o E
local notation "rate" => Wharf.rate (Wharf.title D R x y Q φ K0)
  (Wharf.upper D R x y Q φ K0) T.self.paid
local notation "σ" => Poetry.Agenda.poll R baseHeight x

variable {n B : Side}
variable (hB : B.val = n.val * (A.B.a.S.block m).val)
local notation "L" => Pane.panel A m hB
variable (c₀ : Clip) (u₀ : PathData G) (T' : Layout G)
    (Y : Bulk.Kernel (Pane.panel A m hB) c₀ u₀ X.O)
    (F : Forest (Pane.panel A m hB).ratio) (z : (Pane.panel A m hB).Choices)
    (ht : T' = T.extra) (hP : u₀ = T.self.north)
    (hC : c₀ = (X.p.profile (A.B.a.clock.J (m+1))).clip) (hl : Bid.Larger (G:=G) (Pane.panel A m hB))

local notation "seat₁" => Echo.Sara.seat (Mural.sheet X.p D E.wants) L
  (Plateau.Line.patch_here A hB) (rules₁).lodger
local notation "r" => (Pane.panel A m u).ratio
local notation "seat" => (fun (j:Club.Keys M C) (b:Site n)=>
    (L).ratio.assemble (b,(r).residue (Club.troops M C j).center))

private theorem locate_residue : seat₁ = seat := by
  funext i b
  let W (T:Side)(s:Site T):= s
  let k := Club.Keys M C
  let j:k:= i
  let α:= (Club.troops M C j).center
  let δ:= (r).residue α
  have he := congr_arg (r).residue (Cruise.seat R D A φ o E u M C p v i)
  exact congr_arg (fun z=> (L).ratio.assemble (b,z)) ((Ratio.assemble_res ..).symm.trans he)

variable (hc : c.val ∣ n.val) (hf : f.val ∣ B.val) (l: Stationary.Link G n)
local notation "b₁" => convey (coverWin hc) (Aperture.Bunch.mapC (Club.site M C r))
local notation "ρ" => (rate n * dearth σ n) * (2+ ‖l‖)^(baseHeight+4)
local notation "τ" => Step.tape (baseHeight+2)
open Marker

lemma rates : 0 < rate n * dearth σ n ∧ 0 < σ := by
  have hV : 0 < Wharf.upper D R x y Q φ K0 := (Wharf.ready ..).choose_spec.choose_spec.1
  have hP : 0 < σ := (AllOrder.Ink.Money.soprano _ (QuadraticLocal.Poetry.Agenda.receives R (Burn.horizon E.vac) x).choose_spec.1 _)
  refine ⟨?_, hP⟩
  unfold Wharf.rate dearth; exact mul_pos (mul_pos (mul_pos hV (pow_pos (by positivity) _))
    (pow_pos (Nat.cast_pos.mpr n.pos) _)) (Real.exp_pos _)

variable (s:V→ℕ)(g:V→ℝ)(t:α){d d' :ℕ} {U ε:ℝ}
variable (H : QuadraticLocal.Earn.Scene.Armada M g s ε U p d d') (he:0<ε)
local notation "cost" => Accumulate.rootPrice M g ε
local notation "paint" => (fun i:ι=> (M i).paint t)
local notation "dd" j:max => LinearLetters.mixedTerm (QuadraticLocal.Fk.money T' τ)
  (copiesLetter hf M) M paint Y F z (Stationary.arm G n 1 l) p j C -
  periodic_cluster M r N C hc t l j
include ht hP hC hl H he
lemma periodic_price (j:ℕ) (hj:j≤p) : Poly.price g (dd j) ≤ ρ * cost C := by
  have hp := artwork R D Q A φ K0 o E T u M C p v hB c₀ u₀ T' Y F z ht hP hC hl l b₁ j hj
  rw [locate_residue R D A φ o E u M C p v hB] at hp
  let Y' := production ((N).news C) l b₁ j
  let X' := response M C T' τ Y F z seat l b₁ p j
  let Rr := ρ
  have hr := (rates R D Q A φ K0 o E T (n:=n)).1
  have hY: ‖X'-Complex.ofReal Y'‖ ≤ Rr := hp.trans (mul_le_mul_of_nonneg_left (?_) hr.le)
  rotate_left
  · have hm: ‖mingle l b₁‖≤1+‖l‖:= by
      apply (pi_norm_le_iff_of_nonneg (by positivity)).2
      rintro ⟨a,j|j⟩
      · exact (norm_le_pi_norm l (a,j)).trans (le_add_of_nonneg_left zero_le_one)
      change ‖Aperture.Bunch.mapC (Club.site M C r) (_,j)‖ ≤ _
      refine le_trans (?_: ‖_‖ ≤ (1:ℝ)) (le_add_of_nonneg_right (norm_nonneg _))
      simp only [Aperture.Bunch.mapC]; split <;> simp
    apply le_trans (pow_le_pow_left₀ (by positivity) (b:=2+‖l‖) (by linarith only [hm]) _)
      (pow_le_pow_right₀ (by linarith [norm_nonneg l]) ?_)
    exact le_trans (Nat.add_le_add_right (Nat.add_le_add_right hj _) _) (Nat.add_le_add_right (v.tall C) _)
  have hb : dd j = Poly.send (Club.alliance M C) ((X'-Complex.ofReal Y') *
      ∏ i∈C.val,(M i).paint t) := by
    unfold LinearLetters.mixedTerm
    have heq:= seats_copy hc hf u hB M C T' τ
    rw [heq, sub_mul]; symm;
    change Poly.send _ (_ - _) = Poly.send _ _ - Poly.send _ _
    have f₁ (a b : ℂ) : Poly.send (Club.alliance M C) (a-b) = Poly.send (Club.alliance M C) a - Poly.send (Club.alliance M C) b := by
      ext1 v; simp only [Extra.Trajectories.part_sub,Poly.part_send]; split <;> simp
    exact f₁ _ _
  rw [hb]; apply Alliance.vault M paint s g H he (mul_nonneg hr.le (by positivity)) C
    (fun i=> H.honor i t) _ hY
end YM.Integration.FVA1Physical.TwoReset
