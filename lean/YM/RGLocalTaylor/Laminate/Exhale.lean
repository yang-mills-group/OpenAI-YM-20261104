import YM.RGLocalTaylor.Laminate.Ahead
import YM.RG12.Burst.Cotton
import YM.MergeProof.Tanger
import YM.MergeProof.Groom

/-!
# Strengthened forced/source budget in parallel with the other Taylor books

Here preserving actual γ wages. Also includes Pungent/Minty in the same construction.
No dropping additional forced test, reserve `√w` paid *after* all costs here.
Monopoly at real values of Crix and all τ quota and covering N. Adaptation of
Mallow.Paprika proof. Includes EXTRA post-hatted powers for accumulating
coarse losses (ensure request j≥ each horizon).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor.Laminate
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Time Supply Input Testing PriceCompiler
open PhysicalNext PhysicalNext.Repeat
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Mallow Opera
open Daisy.Charity.RG12
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {s : Supply.Sheet G} {K : MapPrices} {X : Targets s K} {D : Rolls s} {Θ : Protection D} {p : Expenses X} {u : Return.Wages} {l : ℕ→ℝ} {P : Teller G}

set_option quotPrecheck false
-- Pungent grants after (with geometry de facto). Tariff for all shipping capacity.
structure Assets (P:Teller G)(Q:ConnectedActivityE6.Target G P)(L:Side)(N:ℕ)(μ x:ℝ):Prop where
    small (M m:ℕ)(hm:m ≤ N+1)(hM:M ≤ N+1):
      (betaF G x L)^m * (straw μ L G x / Blush.glyph x) ≤ ((Mayer.arcRadius G L x)^M)⁻¹
    shipped : Mallow.Tariff Q L (N+1) μ x
    cards c k (hc:0≤c) (hk:0≤k)
        (hk': k ≤ Real.exp (Trio.coverTicket Q.halo) * (betaF G x L)^ (-(1/8):ℝ))
        (hx: c ≤ Real.exp (-Q.mark L μ x)):∃ κ, Payments.Rates (radiusB x) (stems μ L G x) c k κ
    weather : ∀ V:BudgetPoint,V.threshold=Pressure.temp x→V.B=radiusB x→Time.Same P.below V→∀ α:ℝ,|α|≤ (P.top.drift + |G.slopeConstant * Real.log L.val|) → let q:=P.below; let f:= YM.Merge.Spicy.opens G V q.clip q.width q.paths α (Time.credit G q * δE x);0≤f→∃ κ,Payments.Rates (radiusB x) (straw μ L G x) (stems μ L G x) f κ

-- some tokens grammar hy ref
lemma exhaled (Q:ConnectedActivityE6.Target G P)(L:Side)(N:ℕ)(μ:ℝ)(hμ:0<μ) : ∀ᶠ x: ℝ in atTop, Assets P Q L N μ x:=by
  have he (M m:ℕ): ∀ᶠ x:ℝ in atTop, (betaF G x L)^m * (straw μ L G x / Blush.glyph x) ≤ ((Mayer.arcRadius G L x)^M)⁻¹:=by
       let a:= -(m:ℝ)- Mayer.height*(M:ℝ)-1
       have hp : Rate G L 1 (fun x=> betaF G x L):= Rate.congr Rate.power (Eventually.of_forall (by intro x; simp only [Real.rpow_one]))
       have hi : Rate G L Mayer.height (Mayer.arcRadius G L):=Rate.power
       have hv := (((hp.pow m).mul (Blush.efferv (L:=L) (G:=G) hμ a)).mul (hi.pow M))
       filter_upwards [Delay.shift_pos G L,hv.below (by dsimp only [a]; ring_nf; norm_num) _ one_pos] with x hx hu
       rw [← one_div,le_div_iff₀ (pow_pos (show 0<Mayer.arcRadius G L x from Real.rpow_pos_of_pos hx _) _)]; simp_rw [div_eq_mul_inv,mul_comm (straw ..)]; exact (le_abs_self _).trans hu
  have hl: ∀ᶠ x:ℝ in atTop, ∀ M m:Fin (N+2), (betaF G x L)^(m.val) * (straw μ L G x / Blush.glyph x) ≤ ((Mayer.arcRadius G L x)^M.val)⁻¹ := eventually_all.mpr (fun i=> eventually_all.mpr (fun j=> he i j))
  filter_upwards [hl,Mallow.thaws Q L (N+1) μ hμ,mingle (G:=G) L _ (show 0<μ/4 by positivity) (he:=zero_lt_one) (by norm_num : -(1/8:ℝ)<0) (Rate.power.mul_left (Real.exp (Trio.coverTicket Q.halo))), mingle (G:=G) L _ (show 0<μ/8 by positivity) zero_lt_two (by norm_num : -(1/4:ℝ)<0) Rate.power, offerSp L P.below (P.top.drift+|G.slopeConstant*Real.log L.val|)] with x h hF hz hv hB
  refine ⟨fun M m hm hM=> h ⟨M,Nat.lt_succ_of_le hM⟩ ⟨m,Nat.lt_succ_of_le hm⟩,hF,fun c k hu hk h hh=>hz _ _ hu hk h (by rwa [one_mul,← syrup (μ:=μ) L Q]),?_⟩
  intro V hK hf hR α hα q f hΩ
  have hs : stems μ L G x= 2*lauge L (μ/8) x 1 G:=by unfold stems lauge; ring_nf
  have hC:0≤ stems μ L G x:=by unfold stems lauge; positivity
  obtain ⟨z,hp⟩:= hv _ f hC hΩ (hB _ hK hf hR α hα) hs.le
  exact ⟨z,show Payments.Rates _ (straw μ L G x) _ _ _ from by rw [show straw μ L G x=2*lauge L (μ/8) x (1/2) G from by unfold straw lauge; ring_nf]; exact hp⟩

def exhale (G:Gauge): Decal G:= ⟨fun P Q _ L _ μ _ _ N x=> Assets P Q L N μ x, fun _ Q _=>⟨0,fun _ _ _ μ _ _ _ _ _ hμ=>exhaled Q _ _ μ hμ⟩⟩

lemma fullBudget (R:PhysicalNext.Repeat.Register D p u l)(Z:Delays Θ)(h : Mallow.RG12.Earned (exhale G) R Z): Mallow.Minty R (·+1) Z:=by
  refine ⟨fun j x hx i hi=> ?_,fun j x hx i hi=> (show Assets _ _ _ _ _ _ from h j x hx i hi).shipped⟩
  have hp:= show Assets _ _ _ _ _ _ from h j x hx i hi; exact ⟨hp.cards,hp.weather⟩

def decals (G:Gauge): Decal G:=(lease G).paired (exhale G)
end YM.RGLocalTaylor.Laminate
