import YM.LocalLTE.Sail.Chronicle
import YM.LocalLTE.XPane.Harbor
/-!
# Pinned mixed extension of Chronicles. Determine plantation appointments for
all horizons on *the same* prophecy scale. Uses old programmer before later choice
of rank needs for shared panels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Spiral
open Function Filter Set Lattice RG RG.Shoot Pressure Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Mallow ConnectedActivityE6 Push.AbsoluteSums LocalLTE.Vinca VoucherB LocalLTE.Fan
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe Pressure
open Legato.Spool
variable {G:Gauge} {s:Sheet G}{T:MapPrices}{C:Targets s T}{Y:Expenses C}{M TT q l:ℕ}{k e κ:ℝ}
-- rank compression
abbrev salesD (r:GuideF)(K n:ℕ):ℕ→ℕ→ℕ:=fun j i=> (K+1)*(r j i n + 1)
abbrev futureD (H:Almanac)(f:GuideF)(u j i:ℕ):ℕ:= match u with
    | 0=> H.demand j i 0
    | n+1=> H.demand j i (n+1)+max (f j j n) (f (j+1) j n)
noncomputable def outputRoll (H:Almanac)(K:ℕ)(F:GuideF):ℕ→ℕ→ℕ→ℕ
   | 0,j,i=> F j i (salesD H.demand K 0 j i)
   | n+1,j,i=> let s:= outputRoll H K F n; F j i ((K+1)*(H.demand j i (n+1)+max (s j j) (s (j+1) j)+1))
variable (H:Almanac)(K:ℕ)(F:GuideF)
noncomputable abbrev prophecy (j i u:ℕ):ℕ := outputRoll H K F u j i
noncomputable abbrev demandG (j i u:ℕ):ℕ:= futureD H (prophecy H K F) u j i
-- needed.Le
lemma dayG (i j u:ℕ) : F i j (salesD (demandG H K F) K u i j)= prophecy H K F i j u:=by
    unfold prophecy; cases u <;> rw [outputRoll]
structure Parch (Z:GuideF)(g:ℕ→ ConcertZ C M e)(v l:ℕ): Prop where
    price n i j : (g n).strength i j=e
    bound n i j : (g n).bbase i j=l
    spans i j n : n≤v→ StepStages i j→ H.demand i j n≤ Z i j n
    layers n i j k : n<v → StepStages j k→ StepStages i j →(g n).kap i j ≤ Z j k (n+1)
-- Pre-height forecast. Delay purchases cross spectrum.
variable (C Y)
variable (hR:∀ i j,3/8+(C i j).rate < aust)(he:∀ i j,East.stagnate q (C i j).halo<l)
variable (he0:0<e)(hy:e<M/100)(ht:e < (3/8:ℝ)*q)(hK:Reliable G k κ)
include hR he he0 hy ht hK
lemma flexible (N:ℕ) : ∃ W:ℕ→ℕ, ∀ A:Almanac, ∃ (Z:GuideF) (g:ℕ→ ConcertZ C M e), Parch A Z g N l ∧ ∀ n≤N,ConcertZ.ForecastX C (salesD Z K n) Y (g n) k W:=by
    have hp(i j:ℕ):= LocalLTE.Fan.EarnStepX (C i j) (Y i j) Mallow.aust (hR i j) (by norm_num [Mallow.aust]); choose w hw using hp
    let s':= s
    choose z f H using fun i j (h':ℕ)=> hw i j (s.profile j).order (s.profile j).power M q l h' e k κ hK he0 hy ht (he i j)
    refine ⟨fromMax w, fun A=>?_⟩
    let Z:= demandG A K f; let σ:= salesD Z K; let φ:= prophecy A K f
    let g n:ConcertZ C M e:= ⟨fun i j=> z i j (σ n i j),fun i j=>φ i j n,fun _ _=>l,fun _ _=>q,fun _ _=>e,fun i j _=>⟨le_rfl,he0,hy,ht,he i j⟩⟩
    refine ⟨Z,g,⟨fun _ _ _=>rfl,fun _ _ _=>rfl,?_,?_⟩,fun n _ i j hh L h a o b hx hb=>?_⟩
    · intro i j n _ h; cases n; exact le_rfl; exact Nat.le_add_right ..
    · intro n i j k _ _ hi; have hx : i=j ∨ i=j+1:=by unfold StepStages at hi; omega
      rcases hx with hx|hx
      · subst i; exact le_trans (le_max_left _ (φ (j+1) j n)) (Nat.le_add_left ..)
      subst i; exact le_trans (le_max_right (φ j j n) _) (Nat.le_add_left ..)
    have hz:= H i j (σ n i j) L ((le_fromMax w hh).trans h) a o b hx hb Push.SectorMeasure.Chi.canonical
    rw [show f i j (σ n i j)= φ i j n from dayG ..] at hz; exact hz
omit hR he he0 hy ht hK
section
variable {C Y} {D:Rolls s} {Q:Protection D} {w:Return.Wages} {v:ℕ→ℝ}(R:Register D Y w v) {N:ℕ}
variable {A:Almanac} (r: GuideF) (g:ℕ→ ConcertZ C M e) (V:Delays Q)
structure Mobility (Z:GuideF)(g:ℕ→ ConcertZ C M e)(K l N:ℕ) (k:ℝ): Prop where
   room: Parch H Z g N l -- Parch K param unused! rm below
   buys u: u≤ N→ ConcertZ.CalendarX R (salesD Z K u) (g u) k (fun _ _=>K) V
-- Threshold increments.P.Price policies.
variable {μ:ℝ}
lemma calendars_purchase (W:ℕ→ℕ)(hC:∀ n≤N,ConcertZ.ForecastX C (salesD r K n) Y (g n) k W)(he:∀ i,W i ≤ (D.L i).val)(Z:Delays Q) :∃ V:Delays Q, DelayLe Z V∧ ∀ U,DelayLe V U→ ∀ n≤N,ConcertZ.CalendarX R (salesD r K n) (g n) k (fun _ _=>K) U:=by
    induction N generalizing Z with
    | zero =>
       obtain ⟨f,hF,hv⟩:= ConcertZ.treasuryX R _ (g 0) k (fun _ _=>K) (hC 0 le_rfl) he Z
       exact ⟨f,hF,fun V hv' n hn=>by rw [Nat.eq_zero_of_le_zero hn]; exact hv V hv'⟩
    | succ n ih =>
       obtain ⟨f,hf,hP⟩:= ih (by intro k hk; exact hC _ (hk.trans (Nat.le_succ _))) Z -- order
       obtain ⟨V,hV,hi⟩:= ConcertZ.treasuryX R _ (g (n+1)) k (fun _ _=>K) (hC (n+1) le_rfl) he f
       refine ⟨V,hf.trans hV,fun U hu i hi'=>?_⟩
       obtain hx | rfl:= lt_or_eq_of_le hi'; exact hP U (hV.trans hu) i (Nat.le_of_lt_succ hx)
       exact hi U hu
end
end YM.PhysicalNext.Repeat.Legato.Spiral
