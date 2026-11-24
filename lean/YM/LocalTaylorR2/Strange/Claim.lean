import YM.LocalTaylorR2.Exponent.Statute
import YM.LocalTaylorR2.Capstone.South
import YM.LocalTaylorR2.Mesh.Grace
/-!
 # Earned argument-Taylor on any Chartlet at stage m, same refinements used for Zeal. Cost H projected through all permitted Books. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Strange
open Exponent
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Gas Ursell Trees Multiple OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration RG.Shoot Push.SectorMeasure Supply Input Testing Push.PriceCompiler Org
open ConnectedActivityE6.Blaze Blaze.March Captain Silica PhysicalNext PhysicalNext.Repeat Height Refrain Song
open PhysicalNext.Repeat.Greenbelt Match Roof Roost Geo Time Opera
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Progress.DirectedRecipe RG01.Vacuum Tail RG01.Survive
variable {G : Gauge}
variable {X: Metals G} {D:Rolls X.p} {A : Alloy X D} (Ξ:Observatory G) (R:Factor A) {m n N : ℕ}
open Boulevard CalendarStep Capstone
variable {c f:Side} (h : f.val=c.val*(A.B.a.S.block m).val) {u: RG.Rep G f}
local notation "b" => A.B.a.budget m
local notation "β" => A.B.a.clock.hatBeta m
local notation "α" => (Alpha (A:=A) N m)
local notation "j₀" => A.B.a.clock.J m
local notation "j₁" => A.B.a.clock.J (m+1)
variable (H:Chartlet R.shape A N m h u) (hm:m<N)
set_option quotPrecheck false
local notation "h₀"=> R.target (j₁) (j₀)
local notation "Γ"=> R.expense (j₁) (j₀)
local notation "Wg"=>A.B.a.clock.forcedAllowance m
local notation "Ef"=>Opera.earlyFee (p:=R.expense) A.B N m u.beta
local notation "L!"=>D.L (j₁)
local notation "Z!" => Song.posting (b) H
local notation "ι" => (RG01.Survive.identityX H)
local notation "C!"=>plusone H ι Chi.canonical α
local notation "μ" => R.shape.μ j₁ j₀
local notation "order" => (b).order
local notation "σ" => (b).power
local notation "δ" => ((Γ).one / 2)
local notation "xF" => A.B.a.clock.hatBeta (m+1)
local notation "χ" => Chi.canonical
local notation "Tx" => Pane.panel A m h
-- Use all letters of Orders l through `i`; flavors & credential.
structure Factus (l:ℕ) (H:Chartlet R.shape A N m h u)(ε v q e t:ℝ) (y : H.ThinP→Orders l→ℝ) (z:H.ThinP→ℝ):Prop where
    probed : ReadyAll χ (Mesh.issue H (Ξ.upgrade H l) χ) v (order) y z t
    buoy : Ready H.smallAt (radiusB β) (fun i=>2^order*z i) ((Γ).earn+δ) e δ (1/2)
    charges (i:ℕ) : i ≤ l+1 → readerCost (G:=G) b order σ t δ β e (1/2) i ≤ xF^(requested i ε)
    nonzero : 0<v
    launch : Sailor G (b).threshold q order
    prices : 0≤q ∧ order*q≤v
include hm
lemma loaded (hp:Mallow.RG12.Earned (Exponent.reckon Ξ) R.shape A.delay) (l:ℕ)(hy:l ≤ j₁)(ε:ℝ)(hε: loss j₁ ≤ ε) :
    ∃ (C' d v w A₀ a r B q D' x w' t θ:ℝ) (i:ℕ) (N':Captain H order C' d v w A₀ a r B q (i+order) χ),
       Factus Ξ R h l H ε v q w' t (YM.LocalTaylorR2.Exponent.heavies N' D' x θ t) (YM.LocalTaylorR2.Exponent.resultN N' θ (l+1:ℝ) t D' x l) := by
   let μ' := μ
   have hv:= H.laws.data.funds
   have hu:=hp _ _ (A.B.valid.pays m) _ (step_paid A.B.a m) ⟨(Tx).patch,hv.funds.kernel,hv.length_eq,hv.funds.atStep⟩ l hy
   have hf := params_eq A.B.valid m
   have hh : ManifestX Ξ h₀ L! (R.walls j₁ j₀) μ' β (loss j₁) δ (turnFee b) order σ l (R.shape.o j₁ j₀) χ := by
     change ManifestX Ξ _ _ _ _ _ _ _ (Push.Local.turnCost (A.B.a.params m).order (A.B.a.params m).power) (A.B.a.params m).order (A.B.a.params m).power _ _ _; rw [hf]; exact hu
   obtain ⟨A₀,a,C',x,d,v,w,r,B,K,q,t,y,w',θ,i,k,hh,H'⟩:= hh
   obtain ⟨N',hB,hX,hCr,H0,j₂,hI⟩:=hh.chooses _ _ _ _ (Pane.ovation A N h hm R.pledging.conducts.full) _ _ H
   obtain ⟨h,ht,hθ,hζ,hδ,hs,hl,hk,hd,hM,hg,hp⟩:=hh.gates; unfold μ' at *
   have hU' := YM.LocalTaylorR2.Exponent.earns Ξ N' hB hX hI hh.gates
   have hc : (Γ).earn+δ+δ ≤ (h₀).exp := by linarith only [(Γ).worth,(Γ).second]
   refine ⟨C',d,v,w,A₀,a,r,B,q,K,x,w',t,θ,i,N',hU', YM.LocalTaylorR2.Exponent.medals N' hB hX hh.gates hc (half_pos (Γ).first) hh.overruns,?_,N'.position,?_,N'.income,N'.near⟩
   · intro j hj; rw [Push.PriceCompiler.beta_eq A.B.valid]
     apply (H' j hj).trans; exact Real.rpow_le_rpow_of_exponent_le h (show requested j (loss j₁)≤requested j ε from by unfold requested; linarith)
   refine ⟨fun c u h=> N'.weigh.stroke c _ (h.trans N'.talent)⟩
variable {v q e t ε:ℝ} {l:ℕ} {y:H.ThinP→Orders l→ℝ} {z:H.ThinP→ℝ} (hD:Factus Ξ R h l H ε v q e t y z) {u':Rep G f} {I:Chartlet R.shape A N m h u'} (T: Match.Alliance I H 1 0)
omit hm
include hD
lemma bequeath {r:ℕ}(hs:r≤l+1)(F:ℕ→Prop)(hh:∀ i,F i → r ≤ i):
    Meadow.Budget b (Beam.marquee I b).reg ((cohort H («χ»:=χ) T α (M:=l) (Mesh.issue H (Ξ.upgrade H l) χ) false F).logRead) (xF^(requested r ε)):= by
  have h₀' : preExponent b ≤ (Γ).earn:= by unfold preExponent; rw [Rain.jersey (A:=A) (m:=m)|>.2.2.1]; exact (R.pledging.agenda _ _ (step_paid A.B.a m)|>.1)
  obtain ⟨i,hi,hj⟩:= Capstone.guarded H hD.probed T (α) b rfl rfl le_rfl σ le_rfl q hD.prices.1 hD.launch hD.prices.2 hD.nonzero h₀' (half_pos (Γ).first) hD.buoy F r hh
  exact ⟨i,fun x=> Cost.enlarge (hi x) (hD.charges r hs),hj⟩
end YM.LocalTaylorR2.Strange
