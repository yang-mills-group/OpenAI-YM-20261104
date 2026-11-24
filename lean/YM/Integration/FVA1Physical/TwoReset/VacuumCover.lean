import YM.Integration.FVA1Physical.TwoReset.Period
import YM.QuadraticLocal.Rebirth.Card

/-!
# Identify the unmasked vacuum prescription, not assuming a Caliber

At each step and in its actual block kernel, take the exact coefficientwise
cover limit of `Integration.LocalFormal.Datum.vacuumAction`, relative
log-density (includes quadratic). Claim for ANY covering base and
external field. Input `PathData` of this SAME Run, standard charged
higher packets. All regulator choices. At the end allow ignoring
an unmarked additive constant in converting to the chosen full model.
Marked global terms in THIS normalization (`Order.logMarked` separately)
never ignored. Next file verifies that these identities determine also the
formal kinetic ratio for physical reset (quoted curvature completions,
affine normalization): not a caller-supplied guessed Caliber.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.TwoReset
open Function Filter Finset Lattice RG RG.Supply Pressure Input Org Precision Tree YM.Wilson
open Push Push.AbsoluteSums PriceCompiler PhysicalNext Repeat Further.PhysicalPeriodLimitF933
open ConnectedActivityE6 Push.Uniform Next.Scheduling Extra.Iteration ThroughLaunch Roost Legato
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open QuadraticLocal QuadraticLocal.Advent
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire
open Laurent Stationary AllOrder.Ink AllOrder.Ink.Money Comparison.RG02 Kinetic.Port Pane Marker
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} (R : Run G)
variable (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
variable {N n m i k y : ℕ} (hk : k+2 ≤ R.alloy.B.a.clock.J i)
set_option quotPrecheck false
local notation "sz"=> R.family.side
local notation "S" => R.alloy.B.a.S
local notation "K"=> RunFormalChain.fromRun R
local notation "op"=> R.family.path.levels.clock.op
local notation "B"=> R.alloy.B.kin.path N i
local notation "cl"=> ( R.alloy.B.a.params i ).clip
local notation "T"=> Step.tape ( k+2 )
local notation "W"=> R.alloy.B.a.clock.J i
local notation "F"=> R.alloy.B.a.clock.J (i+1)
local notation "ℓ"=> R.rolls.L F
local notation "hF"=> R.alloy.B.a.clock.adm (i+1)
variable (hi : i<N) (π π':Layout G) (q:Pace.Coin)
local notation "G₀"=> Pace.grouping q π' T cl B
variable (Z: Card R.rolls D (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i)
  (R.alloy.B.a.clock.adm (i+1)) k) (hZ:Journey D R.alloy (m:=i) (N:=N) Z)
local notation "Δ"=> litP D R.alloy Q hk Z
local notation "a₀"=> Step.vista (Δ).presence Z
local notation "F★"=> (R.metals.p.profile F).clip

section
variable {V:Type} [DecidableEq V][Fintype V] (J : Census V) (X: Side)
local notation "P" => Covers (R.alloy.B.a.S) i X
variable (U: (z : Covers (R.alloy.B.a.S) i X)→ Bulk.Colors J G (R.family.side (i+1) z.val))
variable (Y: (z : Covers (R.alloy.B.a.S) i X)→ Forest (R.family.path.levels.clock.op i z.val).ratio)
variable (t: (z : Covers (R.alloy.B.a.S) i X)→ (R.family.path.levels.clock.op i z.val).Choices)

def coveringDatum (k:ℕ) (z:P) : LocalFormal.Datum R.family J :=
  ⟨ N, z.val, i, hi, Y z,t z, QuadraticLocal.Fk.grant π (Step.tape (k+2)) (U z),0 ⟩
local notation "w"=>coveringDatum R hi π J X U Y t k
def coveringVac (x:Link G X)(z:P) := let l:= sz i z.val; (((l.val/X.val)^4:ℕ):ℝ)⁻¹ •
  (w z).vacuumAction (K) (k+2) y (Stationary.arm G _ 1 (convey (coverWin z.prop) x))
-- ensure default params? k,y omitted by type but autoImplicit section? audit
local notation "r₀"=> (Δ).revenue.b y Z
-- orientation + relative extensive scalar. Exact, ABA without Clip. Bind addresses.These use
-- ANY U; its `vac` NOT used (calculated from π), no choices at one normalization undone.
variable (hV : π=Z.extra) (hA : Bid.Larger (G:=G) ( R.family.path.levels.clock.op i n ))
include hV hA hk hZ
lemma cover_vista (hy:y ≤ k+2) (x:Link G X) :
    Tendsto (coveringVac (k:=k) (y:=y) R hi π J X U Y t x) (coverFilter S i X)
      (𝓝 (Complex.ofReal (a₀ y X x))) := by
  let A := S
  let v (z:P) : Side:= sz i z.val
  let f(z:P):= (w z).vacuumAction (K) (k+2) y (Stationary.arm G (sz i z.val) 1 (convey (coverWin z.prop) x))
  let l:= coverFilter S i X
  have hs : Tendsto (fun z:P => (v z).val) l atTop := cover_size ..
  haveI : Nonempty (Card R.rolls D (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i)
      (R.alloy.B.a.clock.adm (i+1)) k) := ⟨Z⟩
  have he: AllOrder.Ink.Echo.Pulsed (r₀) := AllOrder.Ink.Echo.scaleLean ((Δ).revenue.pay y hy).2.grade Z
  refine seam_limit hs he (Δ).revenue.pos (fun z : P=> z.prop) (f:=f)
    (C:=(1+‖x‖)^(y+2)) ?_
  filter_upwards [tendsto_comap.eventually_ge_atTop n] with z hz
  let s:= v z
  let op' := R.alloy.B.a.S.oneStep i z.val
  have hd:Bid.Larger (G:=G) (R.family.path.levels.clock.op i z.val) :=
    ⟨hA.1,hA.2.1.trans ((side_strict A (i+1)).monotone hz), hA.2.2.trans_le ((side_strict A i).monotone hz)⟩
  let a:= Y z; let q':=t z
  let Xf(z':Link G s):= (w z).vacuumAction (K) (k+2) y (Stationary.arm G (sz i z.val) 1 z')
  let win := coverWin z.prop; let x' := convey win x
  let c := R.family.path.rep N z.val (i+1)
  have hp : c.clip = F★ := ((K).clips N z.val (i+1) hi).trans (congr_arg RG.Stage.clip (PriceCompiler.params_eq R.alloy.B.valid _))
  have hW : c.path=Z.self.north:= ((K).selected N z.val (i+1) hi).trans hZ.books.north.symm
  let τ:= (r₀ s) * dearth (Δ).σ s
  obtain ⟨hm,hM⟩ : (∀ x,(Xf x).im=0) ∧ Fire.Prices (y+2) τ ((Complex.re ∘ Xf)-a₀ y s) := PlanV.cover R.rolls D _ (Δ) Z (op i z.val) (Plateau.Line.patch_here R.alloy op'.exact_size) R.alloy.B.valid.kernel hd (U z) c.path c.clip π ((K).step N i z.val hi) a q' hW hp hV hy
  have hs' : ‖x'‖≤‖x‖:= AllOrder.Ink.Echo.amounts win x
  have hx': Xf x'= Complex.ofReal (Xf x').re:=Complex.ext rfl (hm x')
  let b := (↑((s.val/X.val)^4:ℕ):ℝ)
  change ‖Xf x' - b • Complex.ofReal (a₀ y X x)‖ ≤ _
  nth_rw 1 [hx']; rw [Complex.real_smul, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, ← show a₀ y s x' = b*a₀ y X x from AllOrder.Ink.Echo.pay win ((Δ).presence y Z) x]
  exact (hM.2.2 x').trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (show 0 ≤ 1+‖x'‖ from by positivity) (add_le_add_right hs' _) _) hM.1)
end

-- All stem periods. Cover-prescription unmarked action. Equivalent convention:
-- subtract the origin in both numerator and denominator.
def MassCall (k:ℕ) : Prop:= ∀ (V:Type) [DecidableEq V][Fintype V] (J:Census V) (X:Side)
  (U:∀ z:Covers (R.alloy.B.a.S) i X, Bulk.Colors J G (sz (i+1) z.val))
  (Y: ∀ z:Covers (R.alloy.B.a.S) i X, Forest (op i z.val).ratio)
  (t: ∀ z:Covers (R.alloy.B.a.S) i X,(op i z.val).Choices), ∀ l≤ k+2,
    ∀ x:Link G X, Tendsto (fun z=>coveringVac (k:=k) (y:=l) R hi π J X U Y t x z -
       coveringVac (k:=k) (y:=l) R hi π J X U Y t 0 z) (coverFilter S i X)
       (𝓝 (-(Complex.ofReal ( Pace.grouping q π' (Step.tape (k+2)) cl B l X x -
                     Pace.grouping q π' (Step.tape (k+2)) cl B l X 0))))

variable (hA : Bid.Larger (G:=G) ( R.family.path.levels.clock.op i n ))
variable (hV : π=Z.extra) (hv : π' = ( litP D R.alloy Q hk Z ).laid Z) (hN : q = ( litP D R.alloy Q hk Z ).issue Z)
include hk Z hA hN hV hv hZ
lemma money : MassCall R hi π π' q k:=by
  intro V _ _ J X U Y t l hl x
  have ht (x z:Link G X): a₀ l X x + G₀ l X x= a₀ l X z + G₀ l X z := by
    rw [hv,hN, ← hZ.books.south, PriceCompiler.params_eq R.alloy.B.valid i]
    let p := Pace.grouping ((Δ).issue Z) ((Δ).laid Z) T (R.metals.p.profile W).clip Z.self.south l X
    have h : 0-a₀ l X x-p x=0-a₀ l X z - p z := (Δ).sustenance.calls Z X l (Nat.lt_succ_of_le hl) x z
    change a₀ l X x+p x=a₀ l X z+p z; linarith only [h]
  have he : a₀ l X x-a₀ l X 0 = -(G₀ l X x - G₀ l X 0):= by linarith only [ht x 0]
  rw [← Complex.ofReal_neg,← he, Complex.ofReal_sub]
  exact (cover_vista R D Q hk hi π Z hZ J X U Y t hV hA hl x).sub (cover_vista R D Q hk hi π Z hZ J X U Y t hV hA hl 0)
end YM.Integration.FVA1Physical.TwoReset
