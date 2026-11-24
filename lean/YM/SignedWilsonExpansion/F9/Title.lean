import YM.SignedWilsonExpansion.F9.EvaluateQ
/-! # Bounds on pruned cap after h response. Keep full rank × weight at valuation. -/
set_option autoImplicit false
set_option maxHeartbeats 630000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries XSpace
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b N M j l r d p u n :ℕ}
variable {B Q D Z X Y η t a ρ:ℝ}{E W U V:Credit}{P:Era G ℝ}{R:Realm G (e+1) E}
local notation "κ'"=> ((n+1)*k)
variable {F:Frames G}{H:Hol G}{A':∀ h, Survey G H h}{K:∀ h,Rays G h H}
local notation "Rι"=> (F.level h)
namespace MarqueQ
namespace PorchK
open SignedWilsonExpansion.Commission Method Method.Epic Asymptotics Stair MergeTrip Looms Crops Taught
open Normalize (Sec)
open XSpace.Cirrus
variable {W':Initialize G}{Q':∀ h,Rays G h W'.hol}{Ω:Council F}
variable {P':Hol G}{ι:Type} {L:Filter ι}{Y θ μ ν :ι→ℝ}
variable (x:PorchK W' F Q' Ω R h k u)(q:ι→ PorchK W' F Q' Ω R h k u)(Wn:Normalize.Store G)
variable (K':Rose.Pick Wn)(St:∀ i≤e, Across L Y ℂ (fun j=>(q j).toEpic.tenor W' Wn i))(U':RateQ.Costy L Y (fun i=>(q i).toEpic.voice W' K') e)
variable (Bf:FrontQ q L Y θ μ ν)(pτ:ι→ℝ)(w:∀ᶠ i in L,0< θ i)(pt: TimeQ L θ pτ)
variable {S:SectionData (F.level d)} (hS:S.Sound P')(p0: Bid.pop S)(v₀:d≤h)
-- numerical frame ON appointed accounts. linear.MP.Turn.Chance.Paid.H.Weight.Row units through d.Bind.Coeff measures independently.
noncomputable def gown (k':ℕ)(S:SectionData (F.level d))(τ:ℝ): (F.level d).Coeff→ₗ[ℂ] Sec G h:= citeS k' τ ∘ₗ ( (x.canv.snapD W' S Wn x.mesh x.l x.r x.ρ) ∘ₗ (x.duty d • LinearMap.id) )
lemma atgown (k':ℕ)(z:(F.level d).Coeff) (τ:ℝ): x.gown Wn k' S τ z=citeS k' τ (account Wn x S z):= rfl
-- prune PSU. no use of *global* lower bounds until h Gram computed.
protected def prune (d:ℕ)(h:ℕ): Sec G h→ₗ[ℂ] Sec G d:= ∑ i:Fin (d+1), Normalize.en (Nat.le_of_lt_succ i.isLt) ∘ₗ Normalize.part h i
abbrev bodyD (k':ℕ)(S:SectionData (F.level d))(τ:ℝ): (F.level d).Coeff→ₗ[ℂ] Sec G d:= PorchK.prune d h ∘ₗ x.gown Wn k' S τ
lemma crown (x:Sec G h)(w:d≤h){i:ℕ}(t:i≤d): Normalize.part h i (Normalize.up w ( PorchK.prune d h x ))= Normalize.part h i x:=by
    rw [Normalize.part_up]; unfold PorchK.prune; rw [LinearMap.sum_apply, map_sum]; rw [Finset.sum_eq_single (⟨i,Nat.lt_succ_of_le t⟩:Fin ( d+1 ))]; · exact Normalize.part_same (Normalize.part h i x) t
    · intro j _ tj; apply Normalize.part_other _ _ (Nat.le_of_lt_succ j.isLt); exact fun h=> tj (Fin.ext h.symm)
    simp
lemma regalia (x:Sec G h)(w:d≤h): x-Normalize.up w ( PorchK.prune d h x)=∑ i∈ (Finset.univ.filter fun i:Fin (h+1)=> d < i.val), Normalize.en (Nat.le_of_lt_succ i.isLt) (Normalize.part h i x):=by
    let P(y:Sec G h)i (u:i ≤ h):= Normalize.en u (Normalize.part h i y); let H(i: Fin (h+1)):= P x i (Nat.le_of_lt_succ i.isLt); let W:= Normalize.up w ( PorchK.prune d h x); let X' i:= P (x-W) (i:Fin (h+1)).val ( Nat.le_of_lt_succ i.isLt ); change x-W= _; rw [← show ∑ i,X' i=x-W from Normalize.enfits _]; rw [← Finset.sum_subset (s₁:=Finset.univ.filter fun i:Fin (h+1)=> d < i.val) (s₂:=Finset.univ) (Finset.subset_univ _)]; swap
    · intro i _ hi; unfold X' P; rw [map_sub,crown x w (show i.val≤ d from (?_)),sub_self,map_zero]; exact not_lt.mp (fun u=>hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,u⟩))
    refine Finset.sum_congr rfl fun i hi=>?_ ; unfold X' P W; rw [map_sub,Normalize.part_up,Normalize.part_zero ( Finset.mem_filter.mp hi |>.2 ),sub_zero]
-- true spin w.Light.Note.Gown
include hS p0 v₀
lemma titleSpin (s:Signed)(k':ℕ)(x': (F.level d).Coeff): x.gown Wn k' S t ((F.level d).act s.ortho x')= Normalize.ori s.ortho h (x.gown Wn k' S t x'):= by
    simp only [atgown, account, resource, ← map_smul ((F.level d).act s.ortho), snap_spin (F:=F) W' x.canv S Wn x.mesh _ hS p0 v₀ s]; unfold citeS; simp_rw [LinearMap.sum_apply,map_sum]; exact Finset.sum_congr rfl fun i _=> by simp only [ Tape.layer,LinearMap.coe_mk,AddHom.coe_mk, LinearMap.proj_apply,LinearMap.smul_apply,map_smul] -- need explicit
lemma titleReal (k':ℕ)(x': (F.level d).Coeff): x.gown Wn k' S t (star x')= Normalize.reel h (x.gown Wn k' S t x'):= by
    simp only [atgown,account]; rw [show x.resource S (star x')=star ( x.resource S x' ) from ?_]; swap; · ext1 i; simp [resource, StarModule.star_smul,duty]
    unfold citeS; simp_rw [LinearMap.sum_apply,map_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; simp only [LinearMap.smul_apply,LinearMap.proj_apply, snap_star, (Normalize.reel h).map_smulₛₗ]; simp
lemma titleUnit (k':ℕ) : x.gown Wn k' S t ( (x.markW:ℂ)^d • (F.level d).e0 ) = Normalize.leaf G h:=by
    rw [atgown,account,resource,smul_smul,x.restore_one,one_smul,x.canv.snap_leaf W' S Wn x.mesh hS p0]; unfold citeS; rw [LinearMap.sum_apply]; simp_rw [LinearMap.smul_apply, LinearMap.proj_apply,Tape.side_read,coeff_one]; simp [ite_smul, smul_ite]
omit hS p0 v₀
lemma pruned_spin (f:Sec G h)(s:Signed): Normalize.ori s.ortho d (PorchK.prune d h f)= PorchK.prune d h (Normalize.ori s.ortho h f):=by unfold PorchK.prune; rw [LinearMap.sum_apply, LinearMap.sum_apply,map_sum]; exact Finset.sum_congr rfl fun i _=> Subtype.ext ( Normalize.part_ori s.ortho f i ).symm
lemma pruned_real (f:Sec G h): Normalize.reel d ( PorchK.prune d h f )= PorchK.prune d h (Normalize.reel h f):=by unfold PorchK.prune; rw [LinearMap.sum_apply, LinearMap.sum_apply,map_sum]; exact Finset.sum_congr rfl fun i _=> Subtype.ext ( Normalize.part_reel f i ).symm
lemma pruned_up (z: Sec G d)(w:d≤h): PorchK.prune d h (Normalize.up w z)=z:=by unfold PorchK.prune; rw [LinearMap.sum_apply]; simp_rw [ LinearMap.comp_apply, Normalize.part_up ]; exact Normalize.enfits _
-- Fee lift.Support.V.World. λ.Go ties need already prop.
end PorchK
end MarqueQ
end YM.WilsonCoeffUV.Mer.Xa
