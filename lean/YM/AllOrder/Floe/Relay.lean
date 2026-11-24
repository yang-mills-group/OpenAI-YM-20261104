import YM.AllOrder.Floe.Sailboat
import YM.AllOrder.Floe.Campus
import YM.Extension.UV.Canon.Trading
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe.Step
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Pace Aero StateE
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge}{ι:Type}[Nonempty ι]{a b C D Z Λ ε σ Ω:ℝ}{k r m n N l:ℕ}{j:Side}
open Rent PriceCompiler
namespace PlanV
open Aero Kinetic.Port Laurent Bloch Further.PhysicalPeriodLimitF933 Shingle Macrame PhysicalNext ThroughLaunch Pane
variable {X:Metals G} {D:RG.Supply.Rolls X.p}(R:Roots (G:=G) X.p.profile X.K X.p.kernel)(x y:ℕ) -- x stage fine from D
open Exterior Plateau.Line RG.Supply Roost
set_option quotPrecheck false
-- Ops.L from Paid: required orientation.
variable (A:Alloy X D) (F:Factor A)
local notation "E" => A.B.a
local notation "Xz" => A.B.a.clock.J (m+1)
local notation "Xy" => A.B.a.clock.J m
local notation "D₀"=>ConnectedActivityE6.loopBill G (D.L Xz) (A.B.a.clock.hatBeta m)
local notation "M"=> A.B.M
local notation "K"=> X.p.kernel
local notation "C₀"=>A.B.M.H N m
local notation "C₁"=>A.B.M.H N (m+1)
local notation "W"=> A.B.kin.path N (m+1)
local notation "V"=> (X.p.profile Xz).clip
local notation "P"=> Mural.sheet X.p D (A.B.a.clock.adm (m+1))
local notation "P'"=>Mural.sheet X.p D (A.B.a.clock.adm m)
local notation "ℒ"=> (A.B.a.S.block m)
variable (h:m<N)
-- actual coherent directed flow still only for vacuum Stamped.Phone. Also keeps top.After.Sp.Horizon.Section.
variable (Q:R.Tab D)
local notation "I"=> Card D R Xz Xy (A.B.a.clock.adm (m+1)) k
abbrev litP (hx:k+2≤ A.B.a.clock.J m)(i:I):= Q.income _ _ (A.B.a.clock.adm _) (PriceCompiler.step_paid A.B.a m) _ hx ⟨i⟩
local notation "Θ"=> R.pre k
abbrev capprice (k m:ℕ)(i:Age):= authority k i (strengthP (A.B.a.clock.hatBeta m))
lemma capf (i:Age): authority k i D₀= capprice A k (m+1) i:= by unfold capprice; rw [PriceCompiler.beta_eq A.B.valid m]; rfl
def StateF (k m:ℕ)(u:Layout G): Prop:= ∀ i∈Age.scope (k+2), Quoted (u i) (R.pre k (A.B.a.clock.J m) i) (capprice A k m i)
def Path (k N n:ℕ)(V': ℕ→Layout G)(Γ:ℕ → Coin):Prop:=
  (∀ j, n≤j→ j≤N → StateF R A k j (V' j)) ∧
  V' N=Crest.tile (A.B.a.params N).clip G ∧ ∀ m :ℕ, n ≤ m →  m < N → ∃ (u:Card D R (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) (A.B.a.clock.adm (m+1)) k) (hx:k+2 ≤ A.B.a.clock.J m), Journey R A (m:=m) (N:=N) u∧V' (m+1)=u.extra∧V' m=(litP R A Q hx u).laid u∧Γ m=(litP R A Q hx u).issue u
structure Spec (A:Alloy X D) (F: Factor A):Prop where
    rentsK : ∀ x,R.Rise x ((D.L x).val:ℝ)
    bear : Roots.Receives D R Q A.delay
    ladder : Shop.Lodge D F.shape (fun _ i=> Shop.edgeW i) A.delay
    terra : Extension.UV.Archive A.B
    triad : ∃ m, RankCovariance.ShapePort A.B.a A.B.M m
variable (U: Spec R Q A F)
include U
lemma readable (u:I) (hx:k+2≤A.B.a.clock.J m) (a: Journey R A (m:=m) (N:=N) u) : StateF R A k m ((litP R A Q hx u).laid u) ∧ ∀ i∈Age.scope (k+2),i.r=2→ |(litP R A Q hx u).issue u i.e|≤ capprice A k m i:= by
 let h:=U.bear.due _ _ (step_paid (E) m) _ (A.B.valid.pays m) (A.B.a.clock.adm _) (step_paid (E) m) k hx ⟨u⟩ u a.books.fisc; exact ⟨fun i hi=> (h i hi).1,fun i hi=> (h i hi).2⟩
lemma begun (h:k+2≤ A.B.a.clock.J N) : StateF R A k N (Crest.tile (A.B.a.params N).clip G):= by rw [PriceCompiler.params_eq A.B.valid N]; apply (U.bear.cream _ _ (step_paid A.B.a N) _ (A.B.valid.pays N) _ h)
include h
lemma fromst (S:Layout G)(hs: StateF R A k (m+1) S)(hY:k+2 ≤ A.B.a.clock.J m): ∃ i:I, Journey R A (N:=N) i ∧ i.extra=S:= point R A F h U.triad.choose_spec U.rentsK hY U.ladder S (fun i hi=> (capf A (m:=m) (k:=k) i).symm ▸ hs i hi) -- check arg order R unused
omit h
lemma began (N n:ℕ)(hk: n≤ N)(hY:k+2 ≤ A.B.a.clock.J n): ∃ Kx F', Path R A Q k N n Kx F':= by -- Kx local notation binder problematic
 induction hk using Nat.decreasingInduction with
 | self=> let Kx i:= Crest.tile (A.B.a.params i).clip G; exact ⟨Kx,fun _=>0,⟨fun j hj hi=> (le_antisymm hi hj).symm ▸ begun R A F Q U hY,rfl, fun m h₁ h₂=> by omega⟩⟩
 | of_succ m hm ih=>
     obtain ⟨p,B,h,hU,hκ⟩:= ih (le_trans hY (A.B.a.fits.mono (Nat.le_succ m))); obtain ⟨i,hi,r⟩:= fromst R A F hm Q U (p (m+1)) (h _ le_rfl (by omega)) hY
     let y:= litP R A Q hY i; let Ky:= y.laid i; let Γ:=y.issue i; let q:=Function.update p m Ky; let B':= Function.update B m Γ;
     have hx : StateF R A k m (q m) := (show Ky=q m from (Function.update_self m Ky p).symm) ▸ (readable R A F Q U i hY hi).1; have he j (hj:m<j) : q j=p j∧ B' j=B j:=⟨Function.update_of_ne hj.ne' .., Function.update_of_ne hj.ne' ..⟩
     refine ⟨q,B', fun j hj hv=>?_, (he N hm).1.trans hU,fun j hj hv=>?_⟩
     · rcases lt_or_eq_of_le hj with hj|rfl; exact (he j hj).1.symm ▸ h j hj hv; exact hx
     rcases lt_or_eq_of_le hj with hj|rfl; · rw [(he j hj).1,(he _ (by omega : m<j+1)).1,(he j hj).2]; exact hκ j hj hv
     exact ⟨i,hY,hi,(he _ (Nat.lt_succ_self _)).1.trans r.symm, Function.update_self ..,Function.update_self ..⟩
-- path equality. needs energy at regulator top using Atop.
lemma started (p:ℕ→Layout G)(B:ℕ → Coin)(h:Path R A Q k N n p B) (j:Side)(hp:r≤k+2) : Pace.grouping 0 (p N) (Age.scope (k+2)) (A.B.a.params N).clip (A.B.kin.path N N) r j=jet (Wilson.energy ∘ Stationary.input G j) (r+2):= by
 rw [h.2.1,(U.terra.top N)]; exact Crest.summit _ k (U.terra.startup N).clip.direct hp j
end PlanV
end YM.AllOrder.Floe.Step
