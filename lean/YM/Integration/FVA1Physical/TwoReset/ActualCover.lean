import YM.Integration.FVA1Physical.TwoReset.ClubTapes
import YM.Integration.FVA1Physical.TwoReset.ClubSeam
import YM.Integration.FVA1Physical.TwoReset.MarkCover

/-! Exact formal binding on the physical Step. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.FVA1Physical.TwoReset
open Function Filter Finset Lattice RG RG.Supply Pressure Input Org Precision Tree YM.Wilson
open Push Push.AbsoluteSums PriceCompiler PhysicalNext Repeat Further.PhysicalPeriodLimitF933
open ConnectedActivityE6 Push.Uniform Next.Scheduling Extra.Iteration ThroughLaunch Roost Legato
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Echo QuadraticLocal.Mentor QuadraticLocal.Earn RemainderComparison
open Seedlings Offices Cruise
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire
open Laurent Stationary AllOrder.Ink AllOrder.Ink.Money Comparison.RG02 Kinetic.Port Pane Marker
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} (R : Run G)
variable (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
variable {φ : ℕ→ℕ} (P₀ : Offices.Books D R.rolls Q φ)
variable {N m n : ℕ}
local notation "stage" => R.alloy.B.a.clock.J (m+1)
local notation "prev" => R.alloy.B.a.clock.J m
local notation "vol" => R.family.side
local notation "σ" i:max => R.alloy.B.a.S.oneStep m i
local notation "c" => vol m n
variable (hm : m<N)
variable (o : Opportunity (R.alloy.B.a.clock.J (m+1)) (R.alloy.B.a.clock.J m))
    (E : Epoch D R.rolls (R.alloy.B.a.clock.J (m+1)) (R.alloy.B.a.clock.J m) o)
    (T : Card R.rolls D (R.alloy.B.a.clock.J (m+1)) (R.alloy.B.a.clock.J m)
      (R.alloy.B.a.clock.adm (m+1)) (Burn.horizon E.vac)) (hT : Journey D R.alloy (m:=m) (N:=N) T)
variable (hd : Bid.Larger (G:=G) (R.family.path.levels.clock.op m n))
local notation "gov" => Burn.horizon E.vac
local notation "A" => Step.tape (Burn.horizon E.vac+2)
variable {V ι α : Type} [Fintype V] [DecidableEq V]
variable {J:Passport (R.family.side (m+1) n) V}{W:Marker.Census V}
variable (M : ι → Row J W G α) (w : V→ℕ) (p : ℕ)
variable (v : Voter M (QuadraticLocal.Poetry.Agenda.seed D φ (Burn.horizon E.vac) (R.alloy.B.a.clock.J (m+1)))
    p o.count o.stage E.vac (R.alloy.B.a.clock.J m))
local notation "S" => R.alloy.B.a.clock.op m n
local notation "Qp" => (S).ratio
local notation "press" => (Cruise.publish D R.rolls Q R.alloy φ P₀ o E (σ n).exact_size M p v T)
variable {ε e : ℝ} (P : Press.Receipt M (Cruise.publish D R.rolls Q R.alloy φ P₀ o E
    (R.alloy.B.a.S.oneStep m n).exact_size M p v T) ε e)
variable (d : ℝ)
local notation "Y" => Scene.letters M Qp press P d
local notation "K" => RunFormalChain.fromRun R
local notation "X₁" => Scene.Texts M Qp press
local notation "Ω" => Poetry.Agenda.poll D gov stage
local notation "quota" => Wharf.upper R.rolls D stage prev Q φ P₀
local notation "height" => Wharf.title R.rolls D stage prev Q φ P₀
local notation "rate" => Wharf.rate height quota T.self.paid
local notation "rτ" i:max => (rate i*dearth Ω i)
variable {a b s s' : ℝ} {x y i j : ℕ} {g g' : V→ℝ}
variable (L : Layout G) (ht : L=T.extra)

include hd
lemma room_covers (n':ℕ) (h : (c).val ∣ (R.family.side m n').val) :
    Bid.Larger (G:=G) (R.family.path.levels.clock.op m n') := by
  have hh : (vol (m+1) n).val∣ (vol (m+1) n').val := subdiv_dvd
    (σ n) (σ n') rfl h
  exact ⟨hd.1, hd.2.1.trans (Nat.le_of_dvd (vol (m+1) n').pos hh),
    hd.2.2.trans_le (Nat.le_of_dvd (vol m n').pos h) ⟩

include hd hT ht
-- constants for the seam identification may depend on the observation
-- period (even user-extended for copies), still Earth.L separate from seam.
open QuadraticLocal
local instance : NormedSpace ℝ (Marker.Poly W) := inferInstanceAs (NormedSpace ℝ (W.Mode → ℂ))

lemma exact_mark_binding (hM : QuadraticLocal.Earn.Scene.Armada M g w a b p i j)
    (ha:0<a) (hb:b≤1)
    (hY: ∀ t:α, Air.Staff Y (fun i=> (Y i).paint t) w s x) :
    RepresentsCover R hm L A p M w Y := by
  classical
  intro t X hX Y₁ P₁ l z hz
  let Ψ := peek hX Y w L A t z l
  let F:=R.alloy.B.a.S
  let f:=fun b:Covers F m X => (TwoReset.FkCover R hm L A p M w t X hX Y₁ P₁ l z b)
  let K₁:=K
  have hi := cover_size F m X
  let τ:= (2+‖l‖)^(gov+4)
  have hσ:= (rates D R.rolls Q R.alloy φ P₀ o E T (n:=X)).2
  have pulse : Ink.Echo.Pulsed rate := by
    have hp:0 < quota := (Wharf.ready ..).choose_spec.choose_spec.1
    refine ⟨quota * (1+|T.self.paid|)^height,height,mul_nonneg hp.le (by positivity),fun i=>?_⟩
    exact ⟨mul_nonneg (mul_nonneg hp.le (by positivity)) (pow_nonneg (Nat.cast_nonneg _) _),le_rfl⟩
  let q(j:ι):= (M j).paint t
  let e(b': Covers F m X):= Order.observe W p (Order.logMarked (Bulk.Fk (K₁.step N m b'.val hm)
    (Y₁ b') (P₁ b') (copyColor (tiled R hX b') M w q L A) (Stationary.arm G _ 1 (convey (coverWin b'.prop) l)) p)) z
  let cost:= Air.united c ( b *Breeze.areaBudget (c).val i (((Qp).count.val:ℝ)^4) )
  have cap := Alliance.airport M w g hM Qp hb
  obtain ⟨D',hD',Dh⟩ := Poly.equivalent_norm (R:=W) hM.positive
  refine (seam_limit (n:=X) hi pulse hσ (fun b:Covers F m X => b.prop) (C:=τ*cost*D')
    (a:=Ψ) (f:=e) ?_)
  filter_upwards [] with b'
  let d':=vol m b'.val
  let x' := convey (coverWin b'.prop) l
  have hh: (vol m n).val ∣ d'.val:= hX.trans b'.prop
  have hr := (rates D R.rolls Q R.alloy φ P₀ o E T (n:=d')).1
  let T' := (rτ d')*τ
  have hp:0≤T':= mul_nonneg hr.le (pow_nonneg (by positivity) _)
  have hl : Poly.price g (e b'-Pages X d' • Ψ) ≤ T'*cost := by
    apply cover_tolerance M Qp press P d hX t l z hz L A w b'.prop (tiled R hX b') (K₁.step N m b'.val hm) (Y₁ b') (P₁ b') rfl
      (hY t) (Air.license M q w g hM ha fun j=> hM.honor j t) _ g hM.positive
    refine budget_mono (budget_scale hp cap) (fun _=> Poly.nonnegative hM.positive _) (fun Z=>?_)
    let U := R.family.path.rep N b'.val (m+1)
    have h0: U.clip = (R.metals.p.profile stage).clip := (K₁.clips N b'.val (m+1) hm).trans
      ( congr_arg RG.Stage.clip (params_eq R.alloy.B.valid _) )
    have h1: U.path=T.self.north:= (K₁.selected N b'.val (m+1) hm).trans hT.books.north.symm
    exact (periodic_price D R.rolls Q R.alloy φ P₀ o E T (σ n).exact_size M Z p v (σ b'.val).exact_size U.clip
      U.path L (K₁.step N m b'.val hm) (Y₁ b') (P₁ b') ht h1 h0 (room_covers R hd b'.val hh) hh
      (tiled R hX b') x' w g t hM ha z hz).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0≤2+‖x'‖ from by positivity)
          (add_le_add_right (Ink.Echo.amounts ..) 2) _) hr.le) (cap.1 Z))
  rw [Nat.cast_smul_eq_nsmul ℝ]
  exact (Dh _).trans ((mul_le_mul_of_nonneg_right hl hD').trans_eq (by change (((rτ d')*τ)*cost)*D' = (rτ d')*(τ*cost*D'); simp only [mul_assoc]))
end YM.Integration.FVA1Physical.TwoReset
