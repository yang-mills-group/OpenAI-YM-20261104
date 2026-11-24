import YM.QuadraticLocal.Class.Proxy
import YM.QuadraticLocal.Class.Registration

/-!
# Reading the reclosed logarithmic representation and its residual on the canonical interface

Uses *masked* rendering (identities also on bad fields!). For the optional
unmasked representation of the full analytic generator at INPUT, use `Boot.Bare` which
installs its additional forced partners. There's no dividing out those factors
silently for the output: it admits formal `Render` on masks and these K partners
(including ones from short-mask matching), on the whole polynomial density.

Every `Binder` has actual stencil/address retention on all its slots before tests, even when
the evaluated kernel at one of the tests vanishes. Including the optional projection into the per-
row real-slot linearity native Taste representation (under provided rectangle of tests). Costs
through complete `p` not `0`-th support geometry only. Positivity of the vacuum is provable
 here so there's a normalization, but not used as a license for any Gaussian error estimates
 *dividing by physical vacuum* at full fields. It's reported on the actual push term.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Advent.Sycamore.Eon

open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision Next.Scheduling
open Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces Extra.Iteration Extra.Histories
open Marker Integration.LocalComparison Affinity Earn
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius Asymptotics

variable {G: Gauge} (R:Run G)
variable {m n i b k N:ℕ}
variable (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
variable (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
variable (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)(Ψ:(i:ℕ)→RG.Rep G (R.family.side i n))
variable (v:Concourse R.alloy R.kit R.T π Γ m N n k Ψ)
variable (hℓ:m≤ i) (hz:i≤N)
set_option quotPrecheck false
local notation "P'" j:max=> Ψ j
local notation "S"=> R.alloy.B.a
local notation "Z"=> R.family
variable {Θ ι ιw α : Type} [Fintype Θ][DecidableEq Θ]{R₀: Marker.Census Θ}
variable {W': Θ→Type} [∀ i,AddCommGroup (W' i)][∀ i,Module ℝ (W' i)]
variable (Actors:∀ i, Set (W' i))(U:∀ i,Submodule ℝ (W' i))
variable (w:Θ→ℝ)(η:Θ→ℕ)(Z':Syl.School k)
local notation "σ"=> ( (Ψ i).p.supportExponent )
local notation "B"=> (Ψ i).p.B
local notation "T" j:max=> Pupil (Ψ j) R₀ ( Affinity.Wallet Actors )
variable (Vr:Pupil (Ψ i) R₀ ( Affinity.Wallet Actors )) (Vn:Pupil (Ψ (i+1)) R₀ ( Affinity.Wallet Actors ))
local notation "p"=> ( Ψ i ).p
local notation "Λ"=> Tint.Patrol.picture Vr.painter Vr.packet
local notation "Gp"=> (Coat.gStep (Ψ i).beta)
local notation "M"=> ( rendered Vr.painter p Gp )

-- Keep all of the actual pushed K partners **inside the residual**. For comparison it's
-- not featuring fictitious model force in the analytic germs. K tags involving even a
-- zeroth mark projection continue to be estimated in unnormalised receipts.
def remainder (x:Pupil ( Ψ i ) R₀ ( Affinity.Wallet Actors )): Gallery ( Affinity.Wallet Actors ) x.correction x.address.origin (Ψ i) R₀:= ⟨x.packet.old,x.packet.hard⟩
local notation "Σ_"=> ( remainder R Ψ Actors Vr )
local notation "δ₀"=> ( forcedDivisor R.family i )
local notation "Ω"=> ( (Vr).address.support )
local notation "Pc"=> (avatar R π Γ Ψ v hℓ hz)
local notation "Xr"=> ( R.family.path.rep N n i )
variable (hw:∀ i,0<w i) (W: Gallery (Affinity.Wallet Actors) α Vr.address.origin (Ψ i) R₀) (a c d:ℝ)
include v hℓ hz
open Ac GridRenewal.Rain
-- even if one uses an external vacuum normalization convention, keep actual evaluations.
structure Funded : Prop where
  paid : W.Pays w ((Ψ i).p.supportExponent) a (d * forcedDivisor R.family i)
  named : Collared Vr.address.support Actors U (Ψ i) W -- edit Psi
  exhibits (y:Affinity.Wallet Actors)(t:Config G ( R.family.side i n )) :
     (W.density y t).part R₀.quiet=(( Ψ i ).eval t:ℂ) ∧ ( Ψ i ).eval t=( R.family.path.rep N n i ).eval t ∧ (Integration.LocalComparison.normalized R.family N n i (W.density y) t).part R₀.quiet=1
  realist : ( Ψ i ).beta = R.family.path.β N n i
local notation "Qw"=> ( Funded R Ψ Actors U w Vr W a d )
include hw
lemma funding (H: W.Pays w σ a (d * forcedDivisor R.family i))(he:Collared Vr.address.support Actors U (Ψ i) W): Funded (N:=N) R Ψ Actors U w Vr W a d:=by
 let Hx:=( later R π Γ Ψ v hℓ hz ); refine ⟨H,he,fun y t=>?_,Hx.beta⟩
 have ht:= W.same H (Ψ i).p.exponent_pos.le hw y t
 have he:= congr_fun (Pc).vacuum t
 have hU := (YM.Multi.AxisShift.chosen_positive R.makes.wilson hz t).ne'
 refine ⟨ht,he,?_⟩; unfold Integration.LocalComparison.normalized; rw [← Complex.coe_smul, Poly.part_smul,ht,(show (Ψ i).eval t= _ from he), Complex.ofReal_inv]; exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hU)

omit v hℓ hz hw
open RG3.Script.Picnic Overlay
variable [Nonempty Θ][Nonempty (Affinity.Wallet Actors)] -- Taste padding in Ray & escalator
local notation "Ψt" v:max=> (Display.taste v)
local notation "Zp" v:max=> Display.Proxy.stands v Ω
variable [Countable α]
-- pull back full. optionally cost-relative. this is exactly `FullBudget` with real slot norm, not a separately defined norm
structure Reader :Prop where
   born : Funded (N:=N) R Ψ Actors U w Vr W a d
   title : RetainsDeclared (Zp W) (Ψt W) Ω
   linear : Display.Proxy.Read Actors U (Display.taste W)
   receipt : Nonempty (FullBudget (Ψ i).p (Display.taste W) w (forcedDivisor R.family i) (4*a) d)
   calls (t:Affinity.Wallet Actors) (x:Config G (R.family.side i n)):
      ( (Display.taste W|>.leaf t).density x = W.density t x ) ∧
     ( (Display.taste W|>.leaf t).log x = W.E.log t x ) ∧
     Bands.cluster ((Display.taste W|>.leaf t).contents) x=W.gas t x
local notation "Rω" v:max a:max=> ( Reader R Ψ (N:=N) Actors U w Vr v a d )

include v hℓ hz hw
lemma announced (he:Funded (N:=N) R Ψ Actors U w Vr W a d): Reader (N:=N) R Ψ Actors U w Vr W a d:=by
 obtain ⟨hv,hG,hL,hP⟩:= Display.present W (later R π Γ Ψ v hℓ hz|>.truep.valid.labels.forced) hw le_rfl (Graces.glyphBound S i).1 he.paid
 exact ⟨he, Display.Proxy.retention U W Ω he.named Vr.address.born, Display.Proxy.print U W Ω he.named, hv, fun y t=>⟨congr_fun (hP y) t,hL y t,hG y t⟩⟩

omit v hℓ hz hw
local notation "Wa"=> ( Ψt (Λ) )
local notation "Wb"=> ( Ψt ( Σ_ ) )
local notation "gp"=> ( ( Ψ i ).beta )
local notation "Φɛ"=> ( Integration.RunFormalChain.fromRun R )
local notation "Δ'" x:max=> Display.taste x
structure Key :Prop where
   entry : Reader (N:=N) R Ψ Actors U w Vr ( Tint.Patrol.picture Vr.painter Vr.packet ) a d
   completion : ( rendered Vr.painter (Ψ i).p Gp ).Paid w B σ a
   residual : Reader (N:=N) R Ψ Actors U w Vr (remainder R Ψ Actors Vr) c d
   orthogonal (y:Affinity.Wallet Actors)(t:Config G (R.family.side i n)): ( Wa|>.leaf y ).density t = Poly.pass ( ( M ).log y t ) * (Wb|>.leaf y).density t ∧ ( Wa |>.leaf y ).log t= (( M ).log y t)+(Wb|>.leaf y).log t ∧ Bands.cluster (( Wa |>.leaf y ).contents) t= Bands.cluster (( Wb|>.leaf y ).contents) t
include v hℓ hz hw
lemma publishes (H:(Tint.Patrol.picture Vr.painter Vr.packet ).Pays w ((Ψ i).p.supportExponent) a (d * forcedDivisor R.family i))
    (hH:Tableau U Actors Vr.painter) (hC:Affinity.Taut Vr.address.support Actors U Vr.packet.old ∧ Affinity.Crown Vr.address.support Actors U Vr.packet.hard) (hv:Vr.packet.old.Paid w B σ c): Key (N:=N) R Ψ Actors U w Vr a c d:=by -- replace AffOk
    let Hc:= ( remainder R Ψ Actors Vr ); let A:= announced R π Γ Ψ v hℓ hz Actors U w Vr hw (Λ) a d (funding R π Γ Ψ v hℓ hz Actors U w Vr hw ( Λ ) a d H ⟨ Affinity.Polish.Static.spawn ( hH.line p Gp ) hC.1, hC.2⟩);
    let P:= announced R π Γ Ψ v hℓ hz Actors U w Vr hw Hc c d (funding R π Γ Ψ v hℓ hz Actors U w Vr hw Hc c d ⟨hv,H.wages⟩ ⟨hC.1,hC.2⟩)
    let hX:=(M).inlPaid w Vr.packet.old H.budget -- arg order
    refine ⟨A,hX,P,fun y t=> ?_⟩; let H':=(Λ); let x:= ( M ).log y t; have hs:= hv.sums (Ψ i).p.exponent_pos.le hw y t; have ht:=hX.sums (Ψ i).p.exponent_pos.le hw y t
    have he: H'.E.log y t= x+Hc.E.log y t:= Lamps.joinLog y t ht hs -- same order
    obtain ⟨h₁,h₂,h₃⟩:= A.calls y t; obtain ⟨h₅,h₄,h₆⟩:= P.calls y t
    refine ⟨?_,h₂.trans (he.trans (by rw [h₄])),h₃.trans h₆.symm⟩ -- HE defeq
    have hz:x.part R₀.quiet=0:= Lamps.quiet_of_hasSum y t ht; let z:= Hc.E.log y t; have hh:z.part R₀.quiet= 0:= Lamps.quiet_of_hasSum y t hs; have h :Poly.pass (x+z)=Poly.pass x * Poly.pass z:=by rw [← GridRenewal.Rain.passes _ (show (x+z).part R₀.quiet=0 from (by rw [Poly.part_plus,hz,hh,add_zero])), GridRenewal.Rain.plus, GridRenewal.Rain.passes _ hz,GridRenewal.Rain.passes _ hh]
    rw [h₁,h₅]; change (( Ψ i ).exponent _|> Real.exp|>Complex.ofReal) • (( Poly.pass ( H'.E.log y t ) )* Hc.gas y t)= (Poly.pass x) * _; rw [he,h]; unfold Gallery.density; rw [mul_assoc,← mul_smul_comm]

end YM.QuadraticLocal.Advent.Sycamore.Eon
