import YM.FVA2.CorrectionW
/-!
# Attach full stationary & inversion options on ONE SEQUENCE

Exact step costing link (scarce pole & update with corrected image terms). Works on a `LongEnough`
 Fabric (for supplementary FULL period comparison at open coarse fields,
 complete-segment `Bid.Larger` conditions needed in that realization). Fully separate from limits;
we showed the prescribed quantitative formal Wilson to MS comparisons on the inversion spaces directly.
No comparison of $Steady$ actual analytic shelves to rotations after full re-exp.A common path can
thus support QLOCAL integration program via the FULL-period unmasked action/kernel data below even
though proving the multistep continuation bounds for that path and stitching that **other** period
continuation back to the inversion prediction after removal are separate tasks from using the paired
algorithm and are not assumed/proved here.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.Both.Passage
open Function Filter Topology MeasureTheory Lattice Gauge RG _root_.YM.Wilson
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10 FormalOPE.RG10.Inherit FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice FormalOPE.RG10.BlockGauge
open PertExtension.Orb Precision GaussianScore RGComparison.Core16 RGComparison.Core16.Descent Tree Exterior Push.BetaTransport Tandem Luggage
open MeasureTheory.Measure (IsAddHaarMeasure)
open Contacts.Lyre Contacts.Lyre.Align Fabric CityHistory Mirror Blocking PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{f c n : Side}
variable (z:ℕ→PowerSeries ℝ)

def rates (z:ℕ→PowerSeries ℝ)(i j:ℕ): PowerSeries ℝ:= z (i-j)
def Front {f:Side} (L:Fabric G f)(i:ℕ): L.Cost→ℕ:= -- use explicit :
    match L with
    | .endcap _ _=> Empty.elim
    | .layer _ _ _ _ L => Option.elim' i ( Front L (i+1)) -- args
lemma returns (i:ℕ) : parentZ (rates z (i+1))= rates z i:=by funext j; rw [parentZ,rates,rates]; congr 1; omega

abbrev itemUp (z:ℕ→PowerSeries ℝ){L: Fabric G f}(i:ℕ): L.Cost→PowerSeries ℝ:= z ∘ (Front L i)

structure Exhibit (L:Fabric G f) where
   chart: ChartRatio G
   checked: LocalRatio chart
   quotes:ℕ→PowerSeries ℝ
   account: Legacy.SoundZ quotes
   top0: quotes 0=1

namespace Exhibit
variable {Z:ChartRatio G}
def selectC {n:Side} (L:Fabric G n) : Cloth L:= match L with
    | .endcap n h=> .floor n h (Fabric.endcap n h (G:=G)).atop
    | .layer S k t g L => .inLayer (canopy S) (selectC L)
variable {L: Fabric G f}(W:Exhibit L)
def capz (w: Exhibit L) : L.Accounts→PowerSeries ℝ := fun i=> i.elim 1 (itemUp w.quotes 0)
lemma unitC (w: Exhibit L) : w.capz none=1:= rfl
def prescription (w: Exhibit L) : IteratedWilsonPrescription G f := {
   ofEven:=L.even
   L:=L
   ratio:=w.chart
   calibrated:=w.checked
   goods:=selectC L
   z:=capz w
   entitled i:= by
      rcases i with _|i
      · change 0<( coeff 0 (1:PowerSeries ℝ)); rw [coeff_zero_one]; exact zero_lt_one
      change 0 < coeff 0 (w.quotes _); rw [ coeff_zero_eq_constantCoeff_apply,w.account ]; exact zero_lt_one
   pure:= unitC w }
end Exhibit
-- synchronize using a strong common path through *number of steps requested*. Later Exhibit supplies actual history & all Fk forecasts.Density differences tracked, not eliminated through other support norm.No θ.Protect.
local notation "τx"=> Exhibit.selectC
section
variable (S:StepData c f)(he:Even f.val) (h:Bid.Larger (G:=G) S)(hc:Even c.val)(b:S.Choices)(d:Descent n f)(H:d.Room G)(t:d.Tags)
variable (Z:ChartRatio G)(hz:LocalRatio Z) (U:Unmasked G f) (hs:(gated (canopy S) U b (z d.depth)).core.RespectsPrice)
local notation "T"=> Forestry S
local notation "P"=> canopy S
local notation "Bc"=> receipt P b Z (z d.depth) U
local notation "R"=> retained d t H
local notation "Ψ"=> gateQ S T b R
local notation "Ω"=> gated P U b ( z d.depth )
local notation "hp"=> useful S T d t b h H
local notation "T₀"=> Mirror.House.join (lights G S he) (Both.orb G c hc)
local notation "hκ"=> ( show ( Descent.push S (Forestry S) d ).Room G from ⟨ h,H ⟩ )
local notation "Η"=> gives ( Descent.push S ( Forestry S ) d ) ( show (Descent.push S (Forestry S) d).Tags from (b,t) ) hκ
local notation "L0"=> μLedger d Z t H ( rates z d.depth )
local notation "V₀"=> fire S T b ( L0 ) Z (z d.depth)
local notation "Δc"=> (Ω).uptake (tangent G (Blocking.Index S P)) hs
local notation "$τ"=> d.depth
local notation "ψν"=> (lights G S he).ε
local notation "$κ"=> (show (Descent.push S (Forestry S) d).Tags from (b,t))
open RGComparison.Core16.Lumen

-- collect explicit links. lean binder macro limitations use in contextual step.Child.Elem.
structure Lining : Prop where
   thisPair : Mirror.Related (Both.orb G f he) (retained d t H) U.Q
   accountant : Mirror.Related ( T₀ ) (Ψ) Ω
   documented : Bc^2= boost (blankRight (canopy S)) (Δs L0 U.W)* boost ( T₀ ).ε V₀
   carried (x:Flats G c) : (lights G S he).ε (Quadratic.skew Ω hs x)= Quadratic.skew Ψ hp ( (Both.orb G c hc).ε x )
   covariance (p q: Module.Dual ℝ (Future G S T)): (( hs ).inner).wick (p ∘ₗ (lights G S he).ε) ( q ∘ₗ (lights G S he).ε )= (( hp ).inner).wick p q + (( hp ).inner).wick p ( q ∘ₗ (lights G S he).t ) -- h.inner notation parse
   seam : Δs ( μLedger ( Descent.push S T d ) Z $κ hκ ( rates z ( $τ +1 ) )) (( Update P b Z (z d.depth) U hs ).W) = ( Quadratic.uptake Ω (tangent G (Blocking.Index S P)) hs Bc )^2 * Return (boost (Trans.coverL G c) (Quadratic.uptake Ψ (tangent G ( Forestry S ).Free) hp V₀))
   inversion: Perch.TrueStep P b U ( z d.depth ) Z hs
   full (x: Pins G c): let p := Yurt.promise S T Z d H b t x ( rates z ( $τ + 1 ) );
                         let X:=Yurt.sea S T b R x
                         ( PowerSeries.mk ( Fk.birth X Z )* p 1=C ( RayScatter.basePower Ψ hp x (tangent G ( Forestry S ).Free ) 1 * overhead Z ( Forestry S ).Free ) * Stack.read x (Quadratic.uptake Ψ (tangent G ( Forestry S ).Free) hp V₀ )) ∧ ∀ A:Ticket (Future G S T× Pins G c), Stack.read x ( solenoid S T d t b Z ( rates z ( $τ+1 ) ) h H A )= p A*(p 1)⁻¹ -- binder newline
lemma pop_head (i:ℕ): rates z (i+1) 1=z i:= by unfold rates; simp
lemma spacings : let V:= μLedger ( Descent.push S T d ) Z $κ hκ ( rates z ( $τ + 1 ) ); V = Quadratic.uptake Ψ (tangent G (Forestry S).Free) hp V₀:= by
    intro V; unfold V; rw [judgment S T d t b _ _ h H, returns, pop_head ]; -- let variant W.Meta

include h hc hz
lemma affirmed (hJ:Legacy.SoundZ z)(hv:incline U.W)(r:Mirror.Related ( Both.orb G f he ) ( retained d t H ) U.Q): Lining z S he h hc b d H t Z U hs where
  thisPair:=r
  accountant:= together_r he S h.1 hc b _ U r _ (hJ _)
  documented:= invoice_step he S h.1 hc b Z hz _ ( L0 ) (marketZ d Z t H _ hz) U -- verify argument order he?
  carried:= frameMean he S h.1 hc b _ U r _ (hJ _) hp hs
  covariance:= WickRule he S h.1 hc b _ U r _ (hJ _) hp hs
  seam:= by unfold Δs; rw [show μLedger _ Z _ _ _ = _ from spacings z S h b d H t Z ]; rfl
  inversion:= Perch.fromEach P b h.1 U (z d.depth) Z hz hs hv -- order
  full x:= by
       intro p X; obtain Hx:= spacings z S h b d H t Z; refine ⟨?_, Yurt.issued S T Z hz d H b t x _ h⟩;
       rw [← show _ = Quadratic.uptake Ψ (tangent G ( Forestry S ).Free) hp V₀ from Hx ]; exact Yurt.gross S T Z hz d H b t x (rates z _) h
end
namespace Cohort
open Exhibit
-- require `Bid.Larger` from full-period branch.Ph.Level.Mesh.Geom. sufficient for paired.Hessian along path.
def Long {f:Side}(L: Fabric G f): Prop:= match L with
   | .endcap _ _=> True
   | .layer S _ _ _ L=> Bid.Larger (G:=G) S ∧ Long L

variable (Z:ChartRatio G)(hz:LocalRatio Z)(z:ℕ→PowerSeries ℝ) -- duplicate z from above; fix?
variable {U:Unmasked G f}
-- right weights used by `course` on partial history, exact extension via shift.Brand.
local notation "τ"=> Exhibit.selectC
lemma split_quote (S:StepData c f)(h:S.patch.Branches S.kernel G)(b:S.Choices)(he:Even f.val)(L:Fabric G c)(i:ℕ): itemUp z (L:=Fabric.layer S h b he L) i none=z i ∧ ((itemUp z (L:=Fabric.layer S h b he L) i) ∘ some) = itemUp z (i+1) := ⟨ rfl,rfl⟩
noncomputable section
variable {z}
abbrev Linked (U:Unmasked G f)(L:Fabric G f)(H:Long L)(w:L.Cost→PowerSeries ℝ):Prop:= Commission Z (Exhibit.selectC L) U w

-- Carry actual z' on inversion branch.Param recursion using carried rates only.
variable (z)

def Chain {f:Side}(L:Fabric G f)(H:Long L) (d:Descent n f)(K:d.Room G)(t:d.Tags)(W:Unmasked G f)(w:L.Cost→PowerSeries ℝ)(C: Commission Z (Exhibit.selectC L) W w): Prop:=
  Mirror.Related (Both.orb G f L.even) (retained d t K) W.Q ∧ w=itemUp z d.depth ∧ incline W.W ∧ match L with
    | .endcap _ _ => True
    | .layer (c:=c) S h p he L => ∃ (hx:( Quadratic.core (gated (canopy S) W p (z d.depth)) ).RespectsPrice), Lining z S he H.1 L.even p d K t Z W hx ∧
        Chain L H.2 (Descent.push S ( Forestry S ) d) ⟨ H.1,K⟩ (p,t) (Update (canopy S) p Z (w none) W (Exists.choose C)) (w ∘ some) (Exists.choose_spec C)
   -- include `z,Z` variable if keyword scope

variable (hψ:Legacy.SoundZ z)
include hz hψ

lemma kit {f:Side}(L:Fabric G f)(H:Long L)(d:Descent n f)(K:d.Room G)(t:d.Tags)(W:Unmasked G f)(w:L.Cost→PowerSeries ℝ)(C:Commission Z (Exhibit.selectC L) W w)(he:w=itemUp z d.depth)(h:incline W.W)(hr: Mirror.Related (Both.orb G f L.even) (retained d t K) W.Q): Chain Z z L H d K t W w C:= by
   rw [Chain.eq_def]; refine ⟨hr,he,h,?_⟩; cases L with
   | endcap=> trivial
   | @layer c f S hp p hff L=>
       subst w; have hc : ( Quadratic.core (gated (canopy S) W p (z d.depth)) ).RespectsPrice:= Exists.choose C
       refine ⟨ hc, Passage.affirmed z S hff H.1 L.even p d K t Z hz W hc hψ h hr, kit L H.2 (Descent.push S ( Forestry S ) d) ⟨ H.1,K⟩ (p,t) ( Update (canopy S) p Z ( z d.depth ) W hc ) ((itemUp (L:=L) z) (d.depth+1)) (Exists.choose_spec C) ?_ ?_ ?_ ⟩;
       · rfl
       · exact funded hz _ h _
       obtain hV:= Both.cap_next hff S hp (L.even) p (retained d t K) W hr _ (hψ d.depth) (CityHistory.useful S ( Forestry S ) d t p H.1 K) hc; have hE:= CityHistory.future S ( Forestry S ) d t p H.1 K; apply hE ▸ hV
termination_by structural L
end

open Exhibit
variable {L:Fabric G n} (w:Exhibit L) (Z':Long L)
local notation "δ"=> w.prescription
local notation "∅q"=> ( Descent.nil (top:=n) ) -- 
local notation "U"=> initialFull G n 1
local notation "τ0"=> (show (Descent.nil (top:=n)).Tags from () )

lemma earns : Chain w.chart w.quotes L Z' ∅q (show Descent.Room G ∅q from trivial) τ0 (initialFull G n 1) (w.capz ∘ some) (Open.protocol δ):= by
   apply kit w.chart w.checked w.quotes w.account L Z' _ _ τ0 U (w.capz∘some); · rfl
   · exact OpenSlots.restores 1 (firstBill (G:=G) (n:=n))
   exact Both.commencement L.even _ -- signature
lemma center : Δs (μLedger ∅q w.chart τ0 trivial (rates w.quotes 0)) (initialFull G n 1).W=1:= by
    obtain h:= Both.terrain (G:=G) L.even τ0 w.chart (rates w.quotes 0); rwa [show rates w.quotes 0 0 =_ from w.top0] at h
end Cohort
end YM.FVA2.Both.Passage
