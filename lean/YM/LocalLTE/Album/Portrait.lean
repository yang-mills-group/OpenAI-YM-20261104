import YM.MergeProof.Stage
import YM.LocalLTE.Album.Costs
import YM.LocalLTE.Album.Stores
/-! Curve witness & receipts. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost
open UVNext.CouplingReset Animals
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open YM.LocalLTE.Inset ClockB Urns Trio Slide Marlin
-- NOTE scope. factor uses `T` Launch.
variable {G:Gauge} {X:Metals G} {D:Rolls X.p} {A: Alloy X D} (R: Roost.Factor A){p0:ℕ} -- use eta
variable {R} {ε : ℝ} (H:Funding R p0 ε)
local notation "Wf"=> H.w
variable {N m n k:ℕ} {s:Set ℝ} {a:ℝ} {Q:In A.B.a m n}(F:Career H N m n s a Q)
local notation "T" => A.B.a
local notation "x₀" => A.B.a.clock.hatBeta m
local notation "B" => (A.B.a.budget m)
local notation "C₀" => R.target
local notation "J"=> A.B.a.clock.J (m+1)
local notation "I"=> A.B.a.clock.J m
local notation "s₀"=> ClockB.lanternPay G (D.L J) (X.p.profile I) H.w.q x₀
local notation "z" => Trio.base (Trio.resize H.w.ℓ (Rain.lint R.target A m)) (radiusB x₀)
local notation "A₀" => A.B.a.S.side m n
local notation "O" => Chi.canonical
local notation "γ" => A.B.kin.alpha N m
open Coup Scarf East LocalLTE.Fan Pastel
-- Tag for outputs. Function for any Era. Layer J. `ψ` pre-general as low as needed at all stages.
variable {p:ℕ} (W : Trail H p) (hm:m<N)
-- Career lift. uniform Θ with Horites
variable (k':ℕ) (tag:ℕ→ℕ)
-- permits initial Loft post l_b. Needs W.l<chip.I ad.
local notation "P"=>X.p.profile I
local notation "L"=>D.L J

namespace Career
-- x physically. Tape choice. Avoid cancellation using arbitrary flags.
open Ovens Ovens.Pipes
open Collection.Price Progress.DirectedRecipe Refrain
variable (x:ℝ)(hx:x∈s)(J':Adorn H W) (hk:F.Accepts H k) (hF:∀ x∈s, Trail.Hired H W (Q x) tag)
local notation "R₀"=> A.B.kin.path N m
set_option quotPrecheck false
local notation "L₀"=> (A.B.a.params m).clip
local notation "Y₀"=> F.holds.latch x
local notation "V₀"=> (F.hearth H x)
local notation "f"=> F.daily H W k' tag k x
local notation "tap'"=> F.tap H W k' tag k x
local notation "τ"=>F.peeled H k x
local notation "e'"=>F.holds.base
local notation "P₀"=>F.porch H W k' tag
local notation "S₀"=>F.school H W k' tag
local notation "g"=>F.index H W k' tag k x
local notation "A'"=>F.barn H W k' tag
local notation "H₁" => F.tongue H W k' tag k x
local notation "Y₁"=> F.Voy H W k' tag k x

-- local secured reserve.T from overburn events. geometry spectra
open Coup Scarf Progress.DirectedRecipe
local notation "sR"=> W.crew H m*radiusB x₀
local notation "RB"=> (raiser B)
local notation "d!"=> F.panelX H W k' tag
local notation "e"=> Coup.freezes (G:=G) (D.L J) (X.p.profile I) H.w (Rain.lint R.target A m) x₀ (3*W.mass H m)
local notation "f3"=> Marlin.tithe (sR) (e) (raiser B) (ballCost (W.crew H m))

variable {ι:Type}[Fintype ι] (M:ι→Lotus.Leaf (Q (F.holds.latch x))) (rA:ι→ℝ)
open YM.Merge
set_option quotPrecheck false
variable {b v₁ b₁ t q t₁ t₂ L₁ b₂ w : ℝ}{n':ℕ}(TZ: Captain (F.hearth H x) (X.p.profile (A.B.a.clock.J m)).order t q v₁ t₁ L₁ b₂ t₂ b₁ b n' Chi.canonical)
    (h₇:Merchandise R.shape W.footprint W.ψ A.delay)
    (hp:Bikes (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (D.L (A.B.a.clock.J (m+1))) (R.shape.μ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (A.B.a.clock.hatBeta m) (R.expense (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)|>.earn) w b₁ (X.p.profile (A.B.a.clock.J m)|>.order) n')
    (hR: Palette.Plot M (F.hearth H x) rA)
local notation "Vb"=> Palette.shoot M V₀ Chi.canonical rA (V₀) (Meadow.intern V₀)
local notation "Z"=> R.expense J I
local notation "u"=> R.shape.μ J I
local notation "off'"=> R.target J I
local notation "st"=> stems u L G x₀
local notation "sw"=> straw u L G x₀
local notation "z₀" => (Real.exp (-(off').mark L u x₀)*(2*Daisy.pledgeQ L off' u x₀ b₁ (X.p.profile I).order n'))
-- Better `Vb` base? d!.kernel= using hmenu. use a') f'.
local notation "fU"=> F.cords H x
local notation "V'"=> Palette.shoot M (F.hearth H x) O rA (F.holds.base) fU
-- Funds exact.B.
include hR TZ hp
lemma kioskT : Motion.Pays ((F.panelX H W k' tag).pours (F.tap H W k' tag k x)) (raiser (raiser B)) V' z₀ ((raiser (raiser B)).supportExponent+1):=by
  let X':=(d!); let B₀:=raiser (raiser B); let T' := tap'
  let U:= Palette.ready M V₀ Chi.canonical rA hR hp TZ.balance (F.holds.base) fU B₀ X'.reg T'.regular rfl
  let s:=Refrain.read (F.holds.base) fU O X'.reg T'.regular
  refine ⟨fun j=> ?_,fun t r ht=> ?_,?_⟩
  · unfold Palette.shoot; rw [show (Palette.ways rA 0 j)=(fun _=>0) from (by ext; simp [Palette.ways]),Palette.at0 (t':=T'.regular) (E:=X'.reg)]; rfl
  · have h':= Palette.earned M V₀ Chi.canonical (F.holds.base) fU B₀ X'.reg T'.regular rfl (Palette.ways rA t r) -- order
    exact ⟨h'.sym,h'.symtest,h'.meas,h'.meas_test,h'.reads,h'.reads_test,h'.permit⟩
  obtain ⟨c,hC,hU⟩:=U
  have hi : ((raiser (raiser B)).supportExponent+1) ≤ (Z).earn:= by
    change (B).supportExponent+1+1+1 ≤ _; have he':= R.pledging.agenda _ _ (step_paid A.B.a m)|>.1; rw [Rain.jersey (A:=A) (m:=m)|>.2.2.1]; linarith
  change Ac.Hit (fun i=> (((X').pours T').forced i).support) _ _ _ _ at hU
  refine ⟨c,hC, fun i=> budget_mono (hU i) ?_ ?_⟩
  · intro i; split; exact mul_nonneg (Switch.Paid.rocket (hC _)) (Real.exp_pos _).le; rfl
  intro i; split
  next h=> exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hi (by positivity))) (Switch.Paid.rocket (hC _))
  rfl

def ivory (k:ℕ)(t:ℝ)(z':Finset ι): Code G (A₀):= Pipes.solid (Marlin.hak (d!)) B (spice (F.tap H W k' tag k x) (V' t z'))
def coconut (k:ℕ)(t:ℝ)(z':Finset ι): Code G (A₀):= Mallow.final.frigid (F.barn H W k' tag) (F.tongue H W k' tag k x) (fun y=>ivory H F W k' tag x M rA k y z') B t
local notation "m₀"=> ivory H F W k' tag x M rA k
local notation "c₀"=> coconut H F W k' tag x M rA k
include hm hx h₇ hF hk
lemma conserved : Motion.Pays ((F.barn H W k' tag).pours (H₁)) (raiser B) (ivory H F W k' tag x M rA k) st ((raiser B).supportExponent+1):=by
    have ht:= h₇ (J) (I) (step_paid A.B.a m) _ (A.B.valid.pays m)
    have hf:= F.kioskT H W k' tag x (k:=k) M rA TZ hp hR
    obtain ⟨h',hy,hκ⟩:= F.memories H W hm k' tag x hx hk hF
    have hh: z₀ ≤ Real.exp (-(off').mark L u x₀):= mul_le_of_le_one_right (Real.exp_pos _).le (by linarith only [hp.gains])
    have hα:0 ≤ z₀:= by obtain ⟨i,hp,he⟩:= hf.bought; exact budget_nonneg (he 0)
    obtain ⟨η,hη⟩:= ht.1 z₀ _ hα hy hκ hh; obtain ⟨he,hh,hp''⟩:=Motion.harvest hf h' hη (Marlin.hak (d!))
    exact ⟨he,fun t j ht=> let hA:=hh t j ht; ⟨hA.sym,hA.symtest,hA.meas,hA.meas_test,hA.reads,hA.reads_test,hA.permit⟩,hp''⟩
variable (G':G.Simple)
include J' G'
lemma shores : Motion.Pays ((F.Voy H W k' tag k x).activities) (raiser B) (coconut H F W k' tag x M rA k) (straw u L G x₀) (raiser B).supportExponent:=by
    have hf:= F.canopied H W hm k' tag x hx hk hF G'
    have hz:= F.leafT H W hm k' tag x hx J' hk hF G'
    have hh:= F.conserved H W hm k' tag x hx hk hF M rA TZ h₇ hp hR
    have ht : Time.Same (X.p.profile I) (B):= by rw [← params_eq A.B.valid]; exact ⟨rfl,rfl,rfl⟩
    obtain ⟨η,hη⟩:= h₇ (J) (I) (step_paid A.B.a m) x₀ (A.B.valid.pays m)|>.2 B rfl rfl ht _ (UVNext.CouplingReset.within_alpha («B»:=A.B) hm) _ hz.1 hz.2
    exact Motion.harvest (Motion.widening hh) (shown hf) hη (Progress.DirectedRecipe.folio G _)
end Career
end YM.PhysicalNext.Repeat.Mallow
