import YM.RGComparison01.Marks.Corner
import YM.RGComparison01.Marks.Pillow
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Pledge
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas Ursell Trees Height Sail
open PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {H : Cash W s μ L Q o C T R} {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} 

    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
namespace Resin
open Multiple OmitClusters Palette Switch Daisy
variable [Fintype ι]
variable (M:ι→Leaf R) (ρ:ι→ℝ) (H:Cash W s μ L Q o C T R)
local notation "q" => Q.mark L μ s
local notation "Pp" => H.faresP
local notation "Xg" => Palette.sign M S
set_option quotPrecheck false
local notation "p₀"=> fun i:H.ThinP=> tune M H ρ 0 0 i.val
local notation "p₁"=> fun i:H.ThickP=> tune M H ρ 1 0 i.val

variable (χ : Chi)
variable (he : Ringlet H M ρ a δ A B) (U:Config G c) (X' : Forest S.ratio)
local notation "Zr" => Palette.ways ρ
local notation "VQ" => B
local notation "E0" => Q.mark L μ s
local notation "b0" => bold M H ρ 0
local notation "v" t:max u:max=> Palette.color M H χ U (Zr t u)
include χ he
open Refrain Letter Greenbelt
lemma amount : Summable (bold M H ρ 0) ∧ Summable (lace M H ρ 0):=by
  constructor
  · refine Charity.everyoneN H.library _ (fun i=>(aurs M ρ H χ he.pays i 0).rocket) (ern M ρ H he) ?_ he.value
    intro i hi; unfold bold at hi; split at hi
    next hn=> obtain ⟨j,hj⟩:=hn.2.1;exact Finset.Nonempty.mono (subset_biUnion_of_mem H.bookFoot hj) (chapter_ne H _)
    next=> exact (hi rfl).elim
  exact Charity.everyoneN (fun i=>H.bookFoot (.inr i)) _ (fun i=>(aur M ρ H χ he.pays i 0).rocket) (breva M ρ H he) (fun i _=> chapter_ne H _) (add_nonneg he.value he.dust.le)

lemma emergent (t : ℝ)(ht:t∈Set.Icc (0:ℝ) 1)(u:Finset ι) :
    let g:= color M H χ U (Palette.ways ρ t u); let LV:=H.homesteadMill g
    HasSum (fun p=> overhead (prism T s χ o.K U X') R Q.table * LV * H.canopyMill U g p) (S.push R.beta (buy M (Zr t u) S) U)∧
      0<LV ∧ Real.exp (logSum H.seam (H.entriesMill g))=LV:=by
   intro pF LV; have hx := he.slow; have hv := he.fix
   have hw : 0≤a+δ:= add_nonneg he.value he.dust.le
   have hp : Ready H.smallAt (radiusB s) (fun i=> ‖H.entriesMill pF i‖) (a+δ) A δ (1/2):=
     ⟨hx.1,hx.2.1,hx.2.2.1,hx.2.2.2.1,fun _=>norm_nonneg _,AbsoluteSums.Labels.raise_prices _ _ (fun _=> norm_nonneg _) hx.2.2.2.2.2 (fun i=>Paid.tasting (votes M H χ ρ he.pays _ 0 0 (Nat.zero_le _)) U t ht u)⟩
   have heZ:= H.threshold_logMill pF hp hw
   have hz: Summable (H.depositsMill pF) := Summable.of_norm_bounded (Charity.everyoneN H.largeAt _ (fun i=> Switch.Paid.rocket (votes M H χ ρ he.pays _ 1 0 (Cash.forced_cost i.val i.prop.2))) hv (fun i _=>i.2.1) hw) (fun i=> Paid.tasting (votes M H χ ρ he.pays _ 1 0 (Cash.forced_cost i.val i.prop.2)) U t ht u)
   exact ⟨H.convoyMill χ U pF X' (fun i hi=> ⟨(springs M H χ U i _ hi).1,(springs M H χ U i _ hi).2.2⟩) (pushed M H χ U (Zr t u) X') hp hz hw, (by unfold LV; rw [← heZ.2]; exact Real.exp_pos _), heZ.2⟩

variable (J:Cash W s μ L Q o C T R)(F:Match.Alliance J H 1 0)(V:BudgetPoint) (E:ℕ→RegularAddress c)(t':ℕ→ Config G c→ℝ)(hx: V.threshold=Pressure.temp s)
local notation "VB"=> Refrain.read J F χ E t'
open Mallow Ovens Progress.DirectedRecipe
lemma plenty (hZ:V.B=radiusB s) : ∃ u' : ℕ→ℝ,(∀ i, Paid (fun U t u=> shoot M H χ ρ J F t u i U) (u' i)) ∧ Ac.Hit (fun i=> ((VB).forced i).support) V.B u' a (Real.exp (-E0)*(2*VQ)):=by
   let i:= Refrain.visa J F; let u':= fun a: Refrain.Leaf H=> bold M H ρ 0 a.val
   refine ⟨stuff i u', fun z=> ?_,fun p=> ?_⟩
   · by_cases hy:z∈Set.range i
     · obtain ⟨t,rfl⟩:=hy; unfold i Palette.shoot Palette.shootK; simp_rw [stuffed]; exact aurs M ρ H χ he.pays t.val 0
     unfold Palette.shoot Palette.shootK; simp_rw [blank _ _ hy]; unfold i at hy; simp_rw [blank _ _ hy]; exact paidZero (U:=Config G c) (ι:=ι)
   refine transfer_budget i ?_ ?_ (budget_pull (fun i:Refrain.Leaf H=>Subtype.val i) Subtype.val_injective (ern M ρ H he p))
   · intro z; rw [stuffed,hZ]; dsimp only; simp_rw [show ((Refrain.read J F χ E t').forced (i z)).support=_ from (Refrain.admitted J F z).1]; rfl
   intro j hj; rw [blank _ _ hj]; split; rw [zero_mul]; rfl

include hx
lemma stamped (w:Finset ι)(t₀:ℝ)(ht:t₀∈Set.Icc (0:ℝ) 1) : HasSum (fun i : Finset ℕ => overhead (prism T s χ o.K U X') R Q.table * H.homesteadMill (Palette.color M H χ U (Palette.ways ρ t₀ w)) * (black (Refrain.read J F χ E t') (shoot M H χ ρ J F t₀ w)).gasOccurrence V i U) (S.push R.beta (buy M (Palette.ways ρ t₀ w) S) U):=by
  have hh := (emergent M ρ H χ he U X' t₀ ht w).1; let XX:= prism T s χ o.K U X'
  let t:= color M H χ U (Palette.ways ρ t₀ w); let c:= overhead XX R Q.table * H.homesteadMill t
  let B := black (Refrain.read J F χ E t') (shootK M H χ J F (Palette.ways ρ t₀ w))
  let f (j:Finset ℕ):= c*B.gasOccurrence V j U; let g (w:Finset H.Chainbook):= c* H.canopyMill U t w; let Fz(z:Finset (Refrain.Leaf H)):= z.map (Refrain.visa J F); let K(z:Finset (Refrain.Leaf H)):=z.map (Embedding.subtype _)
  have hc(y):=smiling M H χ (Palette.ways ρ t₀ w) U y
  have hz w(hw:w∉ Set.range K):g w=0:=by
    by_contra hn; have he:=right_ne_zero_of_mul hn
    unfold Cash.canopyMill at he; split at he
    next hv=>
      apply hw; let P:= w.subtype (fun i:H.Chainbook=> (H.inventory i.1.toLeft).Nonempty)
      refine ⟨P,?_⟩; unfold K; ext i; constructor
      · intro hi; obtain ⟨j,hj,rfl⟩:= mem_map.mp hi; exact mem_subtype.mp hj
      intro hi; let a:Refrain.Leaf H:=⟨i,(hc i|>.2.2.2 (fun h=> he (prod_eq_zero hi h))).1⟩; exact mem_map_of_mem (Embedding.subtype _) (show a∈P from mem_subtype.mpr hi)
    next h=> exact he rfl
  have hr := ((show Injective K from map_injective _).hasSum_iff hz).2 (show HasSum g _ from hh)
  apply ((show Injective Fz from map_injective _).hasSum_iff (f:=f) ?_).1
  · refine hr.congr_fun fun i=>congr_arg (c*·) ?_
    have ht' : B.admissible V U (Fz i) ↔ ((K i:Set _) ).PairwiseDisjoint H.library ∧ H.eruptedPool U (K i):= Refrain.present V J F χ E t' U i hx
    have hp (z:Refrain.Leaf H): B.K (Refrain.visa J F z) U= H.smilesMill U t z.val:=by unfold B black; dsimp only; unfold Palette.shootK; rw [stuffed]
    unfold Activities.gasOccurrence Cash.canopyMill; by_cases h' : B.admissible V U (Fz i)
    · rw [if_pos h',show ∏j∈Fz i,B.K j U=∏ j∈K i,H.smilesMill U t j from (by unfold Fz K; rw [prod_map, prod_map]; exact prod_congr rfl fun y _=>hp y)]
      split; · rfl
      next ht=> by_contra hm; obtain ⟨hx,hu⟩:=ht'.1 h'; exact ht ⟨⟨Refrain.parted H hx,fun i hi=> (hc i|>.2.2.2 (fun h=> hm (prod_eq_zero hi h))).2.2,hx⟩,hu⟩
    rw [if_neg h',if_neg (fun hj=> h' (ht'.2 ⟨hj.1.disjoint,hj.2⟩))]
  intro i hi; unfold f Activities.gasOccurrence; split
  next=>
    by_contra hh; apply hi
    let e:=Refrain.visa J F; refine ⟨Finset.preimage i e e.injective.injOn,?_⟩
    unfold Fz; ext a; constructor
    · intro ha; obtain ⟨j,hj,rfl⟩:= Finset.mem_map.mp ha; exact Finset.mem_preimage.mp hj
    intro ha; by_cases hp:a∈ Set.range e
    · obtain ⟨j,rfl⟩:=hp; exact mem_map_of_mem e (Finset.mem_preimage.mpr ha)
    exact False.elim (right_ne_zero_of_mul hh (prod_eq_zero ha (by change stuff e (fun (i:Refrain.Leaf H) U=>H.smilesMill U (Palette.color M H χ U (Palette.ways ρ t₀ w)) i.val) a U=0; rw [blank _ _ hp]; rfl)))
  next=> rw [mul_zero]
lemma practical (w:Finset ι)(t₀:ℝ)(ht:t₀∈Set.Icc (0:ℝ) 1) : overhead (prism T s χ o.K U X') R Q.table * H.homesteadMill (Palette.color M H χ U (Palette.ways ρ t₀ w)) * (black (Refrain.read J F χ E t') (shoot M H χ ρ J F t₀ w)).gas V U= S.push R.beta (buy M (Palette.ways ρ t₀ w) S) U:= by
   have hz:= stamped M ρ H χ he U X' J F V E t' hx w t₀ ht; have hf:= hz.tsum_eq; rw [tsum_mul_left] at hf; exact hf

end Resin
end YM.RGComparison01.Pledge
