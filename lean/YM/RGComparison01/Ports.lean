import YM.RGComparison01.Coast
import YM.RGComparison01.AgendaUV
import YM.RGComparison01.PhysicalHigh

/-!
# Ports current exceptional clause

 K and residual REG on *one and the same* output rep. Can designate any part
 of the input E list Ξ. Useful to throw any remaining non-homogeneous entries
 onto Ξ (e.g. path tails). qev before coupling reset and alignment. Future
 consumers should not use this as a claim of zero post-reset Hessian.

 Early data. Additive sign is minus. Use on *any* physical step of
 the same Flourished input, in particular when input itself has been
 reexpressed. For comparisons against RG02/03 likely need to enter also
 on auxiliaries. -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Ports
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration
open Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe
open PhysicalNext PhysicalNext.Repeat Height Song Time Opera
open Divides Selector Coin High Plev Quests Coast
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {X : Metals G} {D : Rolls X.p} {A : Alloy X D} (F : Roost.Factor A)
variable {c f : Side} {m N : ℕ} (sizes : f.val=c.val*(A.B.a.S.block m).val)
    {R : Rep G f} (H : Boulevard.Chartlet F.shape A N m sizes R)
local notation "I" => A.B.a.clock.J m
local notation "J" => A.B.a.clock.J (m+1)
local notation "S" => Pane.panel A m sizes
local notation "L₀" => (D.L J)
local notation "Q₀" => (F.target J I)
local notation "sP" => (X.p.profile I)
local notation "expn" => (F.expense J I)
local notation "θ₀" => (A.B.a.clock.hatBeta m)
local notation "μ₀" => (F.shape.μ J I)
local notation "T" => (Pane.orchestra A N sizes)
local notation "θv" => betaF G θ₀ L₀
local notation "gZ" => Height.grow G L₀ θ₀
local notation "γ" => A.B.kin.alpha N m
local notation "p" => A.B.a.budget m
local notation "O" => Chi.canonical
local notation "aH" => (selfA H)
local notation "Y₀" => (Beam.marquee H p)
local notation "P₀" => (Song.plusone H (aH) O γ)

abbrev costE (k : ℕ) (β : ℝ) := 2 * (2^k * Coin.coupling β^k)

abbrev costOld (m : ℕ) := let j:= A.B.a.clock.J (m+1); let i := A.B.a.clock.J m
                            let y:= A.B.a.clock.hatBeta (m+1)
                            turnFee (A.B.a.budget m) * (y^(F.expense j i).wanting + y ^ (-(7/16):ℝ))

structure Wet (k : ℕ) (Ω : ℕ→Prop) (e : ℝ) : Prop where
  -- demanded precursor still explicit: useful to instantiate any step
  allE : Collection.Local Y₀ p P₀ (costOld F m) (Coin.wage F m)
  low : Collection.Local Y₀ p (kept_out F sizes H Ω k) (costOld F m) (Coin.wage F m)
  bills : Meadow.Budget p (Y₀).reg (Coast.inherited F sizes H Ω).logRead e
  tails : Meadow.Budget p (Y₀).reg (weeded F sizes H Ω k).logRead (costE k R.beta)
  -- cheaper variants aligned to usual `norm`
  uncharge : ((Y₀).read (Coast.inherited F sizes H Ω)).EBound p e
  untail : ((Y₀).read (weeded F sizes H Ω k)).EBound p (costE k R.beta)
  hard : ((Y₀).read P₀).KBound p (Coin.wage F m)
  restart : Coin.wage F m ≤ (1/8:ℝ)*Time.forecastK A.B.a m F.scout R.beta
  discard : Coin.wage F m ≤ Real.sqrt (A.B.a.clock.forcedAllowance m)*Coin.coupling R.beta ^ k
  unnorm t : (S).push R.beta R.eval = earlyValue Y₀ (T).down (T).low p P₀ R.beta (weighty H O t) γ
  restores (μ) (V : Config G c) :
    earlyValue Y₀ (T).down (T).low p P₀ R.beta μ γ V = earlyValue Y₀ (T).down (T).low p (kept_out F sizes H Ω k) R.beta μ γ V *
        Real.exp (- ((Y₀).read (Coast.inherited F sizes H Ω)).additive p V - ((Y₀).read (weeded F sizes H Ω k)).additive p V)

lemma boards (he : Quests.Gates F.shape A.delay) (hm : m < N) (hr : Boulevard.SeekR F.shape A N m sizes H) (k : ℕ)
    (hk : k ≤ J) (hb : R.beta∈band A.B.a (m+1))
    (hs : gZ ^ High.countOrder k ≤ Real.exp ((Q₀).mark L₀ μ₀ θ₀))
    (hK : Coin.wage F m ≤ Real.sqrt (A.B.a.clock.forcedAllowance m)*Coin.coupling R.beta ^ k) (Ω : ℕ→Prop) {w : ℝ}
    (h : Meadow.Budget p (Y₀).reg (Coast.inherited F sizes H Ω).logRead w) : Wet F sizes H k Ω w := by
  obtain ⟨hL,hV⟩:= Plev.canopy F sizes (H:=H) hm hr
  have hL: Collection.Local Y₀ p P₀ (costOld F m) (Coin.wage F m):= by unfold costOld; rw [PriceCompiler.beta_eq A.B.valid m]; exact hL
  have hx:= Plev.meter_price F sizes (H:=H) hm he Ω k hk hb hs
  obtain ⟨h₁,h₂,h₃,h₄,hA⟩ := Coast.coast F sizes H Ω k hL h hx
  refine ⟨hL,h₁,h,hx,h₂,h₃,h₄,?_,hK,hV,hA R.beta⟩
  unfold Coin.wage Time.forecastK
  rw [PriceCompiler.beta_eq A.B.valid]
  exact F.pledging.conducts.income.earns _ _ (step_paid A.B.a m) _ (A.B.valid.pays m) _ (PriceCompiler.beta_eq A.B.valid m ▸ trial_in hb)

lemma aims (hG:G.Simple) (k:ℕ) : ∀ᶠ m in atTop,
    let Jf:= A.B.a.clock.J (m+1); let L:=D.L Jf; let x:=A.B.a.clock.hatBeta m; let i:= A.B.a.clock.J m
    k≤Jf ∧ grow G L x ^ countOrder k ≤ Real.exp ((F.target Jf i).mark L (F.shape.μ Jf i) x) ∧
      ∀ β ∈ band A.B.a (m+1),Coin.wage F m ≤ Real.sqrt (A.B.a.clock.forcedAllowance m)*Coin.coupling β^k := by
  filter_upwards [A.B.a.fits.deep.eventually_ge_atTop k,Coin.seeds_paid F hG (countOrder k),Coin.forced_price F hG k] with m hm hv hq
  exact ⟨hm.trans (A.B.a.fits.mono (Nat.le_succ m)),hv,hq⟩

/-- Aux entry without physical contraction, with SAME Weeds log weight
 and derivative convention on all labels. -/
lemma even_aux (hG:G.Simple) (k:ℕ) (he : Quests.Gates F.shape A.delay) : ∀ᶠ m in atTop,
    ∀ (N : ℕ), m<N → ∀ {c f : Side} (sizes : f.val=c.val*(A.B.a.S.block m).val) (R : Rep G f),
      R.beta∈band A.B.a (m+1) → ∀ (H:Boulevard.Chartlet F.shape A N m sizes R),
       Boulevard.SeekR F.shape A N m sizes H → Wet F sizes H k (fun _=>False) 0 := by
  filter_upwards [aims F hG k] with m hm N h c f size R hR H hh
  exact boards F size H he h hh k hm.1 hR hm.2.1 (hm.2.2 R.beta hR) _ (Coast.silent F size H)

variable {g : ℕ→ℝ}
theorem any_step (hG:G.Simple) (k:ℕ) (he:(Quests.zest G g).atFactor F) : ∀ᶠ m in atTop,
    ∀ (N n:ℕ), m<N → ∀ R : Rep G (A.B.a.S.side (m+1) n), R.beta∈band A.B.a (m+1) → Travels A.B N (m+1) n R →
      ∃ H : Boulevard.Chartlet F.shape A N m ((A.B.a.S.oneStep m n).exact_size) R,
      Boulevard.SeekR F.shape A N m ((A.B.a.S.oneStep m n).exact_size) H ∧ ∀ Ω : ℕ → Prop, ∀ e,
        (Tithe.portion R.activities Ω).EBound R.p e → e ≤ A.B.a.clock.allowance (m+1) →
          Wet F (A.B.a.S.oneStep m n).exact_size H k Ω (Ocean.fee F m *e) ∧ 0 ≤ Ocean.fee F m ∧
          Ocean.fee F m ≤ g (A.B.a.clock.J m) := by
  filter_upwards [aims F hG k] with m hm N n h R hb hR
  obtain ⟨h₀,h₁,h₂⟩:=he
  have hx:=F.pledging
  obtain ⟨Y,hY⟩:=Opera.feature (relieve A.B) F.shape h hx.conducts.full hx.conducts.income hR hb
  refine ⟨Y,hY,fun Ω e he ht=>?_⟩
  have hy: Quests.Gates F.shape A.delay := h₀
  have hv := A.B.valid; let β:=R.beta
  have hz : e≤ incomingE G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m):= by
    unfold incomingE; rw [← PriceCompiler.beta_eq hv]; exact ht
  obtain ⟨hN,hK⟩:= Ocean.contracts F (H:=Y) hy h h₁ hR hb Ω e he hz
  exact ⟨boards F _ Y hy h hY k hm.1 hb hm.2.1 (hm.2.2 _ hb) _ hK,hN,
    (show (Ocean.fee F m) ≤ _ from (by unfold Ocean.fee; rw [show turnFee (A.B.a.budget m)=_ from Rain.jersey (A:=A) (m:=m)|>.2.2.2]; exact h₂ _ _ (step_paid A.B.a m)))⟩
theorem at_step (hG:G.Simple) (k:ℕ) (he:(Quests.zest G g).atFactor F) : ∀ᶠ m in atTop,
    ∀ (N n:ℕ), m<N → ∀ R : Rep G (A.B.a.S.side (m+1) n), R.beta∈band A.B.a (m+1) → Lives A.B.bake N (m+1) n R →
      ∃ H : Boulevard.Chartlet F.shape A N m ((A.B.a.S.oneStep m n).exact_size) R,
      Boulevard.SeekR F.shape A N m ((A.B.a.S.oneStep m n).exact_size) H ∧ ∀ Ω : ℕ → Prop, ∀ e,
        (Tithe.portion R.activities Ω).EBound R.p e → e ≤ A.B.a.clock.allowance (m+1) →
          Wet F (A.B.a.S.oneStep m n).exact_size H k Ω (Ocean.fee F m *e) ∧ 0 ≤ Ocean.fee F m ∧
          Ocean.fee F m ≤ g (A.B.a.clock.J m) := by
  filter_upwards [any_step F hG k he] with m hm N n h R hp hv
  exact hm N n h R hp (YM.RGComparison01.visits hv)

end YM.RGComparison01.Ports
