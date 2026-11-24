import YM.SignedWilsonExpansion.F9.Harbinger
/-!
# Top inversion transport for Pₛ macro-axis shelf

No divergence from the launch epochs without a lamp payment. Estimate as sum over the
same price escrows (post)+Stencil Leasing cluster period power. Clock down is the funding
charge of comparing top orbit regulator (forward meter) to lore. Use common Deck FΩ.
-/
set_option autoImplicit false
set_option maxHeartbeats 760000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries XSpace
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open Pill Cloth StationA
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b T N M i j l r d p u n :ℕ}
variable {B Q D Z X Y η t a ρ:ℝ}{E W U V:Credit}{P:Era G ℝ}{R:Realm G (e+1) E}
local notation "κ'"=> ((n+1)*k)
variable {F:Frames G}{H:Hol G}(A':∀ h, Survey G H h)(K:∀ h,Rays G h H)(H' :Hol G) -- H' unnecessary (Q.Sound separate)
namespace Stair
variable {A' K}{Q:Council F}
variable (p':Stair Q (launch F H A' K k) A Ñ m c c h e k u Z)
local notation "F'"=> (F.level h)
abbrev raft (v:d≤h)(i:(F.level d).Index): BankP (F.level d) e:= loftP (p'.supply d v) (p'.charm d v) i
set_option maxRecDepth 1800
protected def Mora (v:d≤h)(i j:(F.level d).Index): Cost:= stamps (F.level d) (p'.raft v i) j
-- local prop in headers explicitly
lemma capMora (v:d≤h)(i j:(F.level d).Index): FitS e (p'.Mora v i j) ((Enough (F.level d) e u k).buy Z):= by
    intro e hx; unfold Stair.Mora; rw [stampsFee _ _ _ hx]; exact (loft_allow (p'.supply _ v) (p'.charm _ v) i).1 _
/-- whole top roster -- right dimension. path prefix through i.List contains kernels at that sheet.PureBasisQ -/
abbrev Stock (F:Frames G)(h:ℕ):= Σ d:Fin (h+1),(F.level d).Index -- abbrev
abbrev dimensions (i:Stock F h) : ℕ:= i.1.val
abbrev doors (H:Hol G)(F:Frames G)(A:∀ h, Survey G H h)(K:∀ h,Rays G h H)(k:ℕ)(i:Stock F h): Cloth G k:= Nest (L:=F) H A K k i.1.val i.2
abbrev ownStock (F:Frames G)(v:d≤h)(i:(F.level d).Index): Stock F h:= ⟨⟨d,by omega⟩,i⟩
lemma stock_faith (F:Frames G)(v:d≤h): Injective (ownStock F v):=fun i j v=> eq_of_heq ((Sigma.mk.inj v).2)
def dye (ρ:ℝ)(v:d≤h)(i:(F.level d).Index)(j: Stock F h): Cost:= if p:∃ j', j=ownStock F v j' then (sizeT A ρ c^d)⁻¹ • p'.Mora v i p.choose else 0 -- direct variant entire Claim, choose legal yes.Equal strain.
def hymn (ρ:ℝ)(i:(F.level h).Index): Stock F h→ Cost:= p'.dye ρ ((F.level h).bound i) (downL F ((F.level h).bound i) i (le_refl _))
lemma dye_here (ρ:ℝ)(v:d≤h)(i j:(F.level d).Index): p'.dye ρ v i (ownStock F v j)=(sizeT A ρ c^d)⁻¹ • p'.Mora v i j:=by have hp:∃ j', ownStock F v j=ownStock F v j':= ⟨j,rfl⟩; unfold dye; rw [dif_pos hp,(stock_faith F v hp.choose_spec).symm]
lemma page_start (v:d≤h)(i:(F.level d).Index): p'.personal c v i=∑ j, trim (p'.Mora v i j) (photo (doors H F A' K k (ownStock F v j))):= (pier_top (p'.hAxis v i)).trans (rack_as (F.level d) _ _)
lemma runway (ρ:ℝ)(v:d≤h)(i:(F.level d).Index): (sizeT A ρ c^d)⁻¹ • p'.personal c v i= ∑ j:Stock F h, trim (p'.dye ρ v i j) (photo (doors H F A' K k j)):=by
    let S:=Finset.univ.image (ownStock F v); rw [page_start p',Finset.smul_sum,←Finset.sum_subset (Finset.subset_univ S)]; swap; · intro j _ hb; unfold dye; rw [dif_neg]; exact Prod.ext (funext fun _=> no_tariff _) (no_tariff _); rintro ⟨j,rfl⟩; exact hb (Finset.mem_image.mpr ⟨_,Finset.mem_univ j,rfl⟩)
    unfold S; rw [Finset.sum_image (stock_faith F v).injOn]; exact Finset.sum_congr rfl fun j _=>by rw [dye_here,trim_lib]
lemma dispatch (ρ:ℝ)(i:(F.level h).Index): p'.tab ρ c i= ∑ j:Stock F h, trim (p'.hymn ρ i j) (photo (doors H F A' K k j)):= runway _ ..

lemma canMora (F:Frames G)(h k u e:ℕ): ∃ B:Credit,∀ Z:ℝ,1≤Z→∀ d≤h,(Enough (F.level d) e u k).buy Z≤ B.buy Z:=by
    obtain ⟨W,h⟩:= uniformPays (P:=fun i W=>∀ Z:ℝ,1≤Z→(Enough (F.level i) e u k).buy Z≤ W.buy Z) (Finset.Iic h) (fun i _=>⟨_,fun _ _=>le_rfl⟩) (fun _ _ _ _ v x i b=> (x i b).trans (v _ b)); exact ⟨W,fun Z t d b=> h d (Finset.mem_Iic.mpr b) _ t⟩
lemma dye_price (hρ:0<ρ)(v:d≤h)(i:(F.level d).Index)(j:Stock F h): FitS e (p'.dye ρ v i j) (((canMora F h k u e).choose).buy Z*(sizeT A ρ c^d)⁻¹):=by
    let C:=(canMora F h k u e).choose; have hv:1≤Z:=(p'.charm _ v).pos; have ht:0≤(sizeT A ρ c^d)⁻¹:=inv_nonneg.mpr (pow_nonneg (sizeT_pos A hρ c).le d); unfold dye; split; · rw [mul_comm]; exact (((p'.capMora v i _).more ((canMora F h k u e).choose_spec Z hv d v)).spray (a:=(sizeT A ρ c^d)⁻¹)).more (le_of_eq (by rw [abs_of_nonneg ht]))
    exact FitS.zero.more (mul_nonneg (zero_le_one.trans (C.purchase hv)) ht)
lemma hymn_cost (hρ:0<ρ)(i:(F.level h).Index)(j:Stock F h) (cap:sizeT A ρ c≤1): FitS e (p'.hymn ρ i j) (((canMora F h k u e).choose).buy Z*(sizeT A ρ c^h)⁻¹):=by
    have hb:= (F.level h).bound i; have hp:= sizeT_pos A hρ c; exact (p'.dye_price hρ hb _ j).more (mul_le_mul_of_nonneg_left (inv_anti₀ (pow_pos hp _) (pow_le_pow_of_le_one hp.le cap hb)) (zero_le_one.trans (Credit.purchase _ (p'.charm h le_rfl).pos)))
end Stair
end YM.WilsonCoeffUV.Mer.Xa
