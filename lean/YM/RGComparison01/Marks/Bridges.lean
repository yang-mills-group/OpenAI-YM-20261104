import YM.RGComparison01.Marks.Oceanic
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
open Extra.Iteration
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} {χ:Chi}
    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
namespace Bridges
open Foreman Checks Baked Palette Pillow Resin Season Ink Heron
open Switch Mallow Ovens OmitClusters Song Refrain Motion Luggage Oceanic
open Push.Uniform Sienna Fare Lapis Boulevard Next.Scheduling Further.LogJets Pencils Stowe
variable (M:ι→Lotus.Leaf R)(g:ι→ℝ)(H:Cash W s μ L Q o C T R) (P':BudgetPoint)
    (D' : Ribbon R n)
local notation "ZA"=> Cl M H
local notation "Zt"=> recordSet M H
local notation "Ft"=> origins M H
local notation "A₀"=> glass M g χ
local notation "K₀"=> pottery M g χ
local notation "Z"=> Drawing.cabinet H D'
-- E calendar pricing logs.Length ALL markers.Rooted supply. Want +3 Exp before threshold.
variable [Fintype ι] {m u:ℕ}
def balance (ℓ i : ℕ)(p:Finset ι): ZA→ Config G c→ℝ:= Checks.treat (ρ:=g) (χ:=χ) (fun z=> Yielding M H p z∧ z∉ ledger M H (Drawing.cabinet H D') ℓ i p)
variable (p:Finset ι)(hp:p.Nonempty)
lemma universal (i:ℕ)(z:ZA) (he:Yielding M H p z∧ z∉ ledger M H (Drawing.cabinet H D') ℓ i p) (hr:p.card ≤ m)(hq:p.Nonempty) : miss M H D' m ℓ i z:= ⟨⟨he.1.1.symm ▸ hq,he.1.2.trans_le hr,he.1.2.trans (congr_arg card he.1.1.symm)⟩,he.1.1.symm ▸ he.2⟩
variable (hh : P'.threshold=Pressure.temp s)(hP : P'.B=radiusB s)
  (hK : ∀ z:Cl M H,pottery M g χ z= masked P'.threshold (origins M H z) (glass M g χ z))
   (hB:Rooted (origins M H) (glass M g χ) P' a A)(hR:Ringlet H M g a δ r D)
-- exact value.Identity on all masks.
include hh hK hP hR hB hp
lemma alpine (j ℓ:ℕ)(y:Config G c): Reels.allotV M g H p y (χ:=χ)=Stowe.ship M g H (Drawing.cabinet H D') ℓ j p y (χ:=χ) + ∑' z:ZA,masked P'.threshold (Ft z) (balance M g H D' ℓ j p z (χ:=χ)) y := by
   obtain ⟨f,h,hb,hV⟩:= Heron.tally M g H P' hP hh hR hB hK; let B:= ledger M H Z ℓ j p
   let f' (z:ZA):= pottery M g χ z y; let F z:= yielded M g H (χ:=χ) z y; let g' z:=if z∈B then f' z else (0:ℝ)
   have hs:= (Switch.issue (fun z=> Paid.toPoint _ ((h z).2) y) hV).2 () p -- args check
   have he : HasSum (fun z=> Switch.jet (F z) p) (Reels.allotV M g H p y (χ:=χ)):= hs
   have hx z: masked P'.threshold (Ft z) (balance M g H D' ℓ j p z (χ:=χ)) y= jet (F z) p-g' z:= by
     unfold balance Checks.treat g' F; dsimp only; rw [Stowe.posted_jet]
     by_cases hK' : z∈ B
     · have hu : Yielding M H p z := (mem_filter.mp hK').2.1
       rw [if_neg (show ¬(Yielding M H p z ∧ z∉ledger M H Z ℓ j p) from fun hl=>hl.2 hK'),if_pos ⟨hu,hp⟩,if_pos hK']; simp [masked,f']
     rw [if_neg hK',sub_zero]; by_cases hp': Yielding M H p z
     · rw [if_pos ⟨hp',hK'⟩,if_pos ⟨hp',hp⟩]; exact congr_fun (hK z).symm _
     rw [if_neg (fun h=>hp' h.1), if_neg (fun h=>hp' h.1)]; simp [masked]
   have hG:HasSum g' (Stowe.ship M g H (Drawing.cabinet H D') ℓ j p y (χ:=χ)):= by
     have hb (z) (hp:z∈B):g' z=f' z:= if_pos hp
     unfold Stowe.ship; rw [Finset.sum_congr rfl (fun i (_:i∈B)=> (hb i (by assumption)).symm)]; exact hasSum_sum_of_ne_finset_zero (fun z hz=> if_neg hz)
   simp_rw [hx,(he.sub hG).tsum_eq]; ring
-- Need transfer to compiler slots in Shore. SMART.Catalog arbitrary count uses injection, not expensive.
omit hh hP hK hB hR hp
scoped instance possible : Countable (Cl M H):= by unfold Baked.Cl Cake; infer_instance -- Ledger inference
omit [Fintype ι] in
lemma notEmpty (z:Cl M H): (Ft z).Nonempty:= Finset.Nonempty.mono (subset_biUnion_of_mem (raised M H ∘ z.2) (Finset.mem_univ none)) (z.2 none).1.2.1
-- # Supply from high analysts. Not accounting Queue before scale.
variable (k' ℓ : ℕ)(V:Config G c→ℝ)(hM:P'.Regular Finset.univ V)(ht: preExponent P'≤a)(hn:P'.threshold≤2*Pressure.fiery G s L)
local notation "Ū"=> Stowe.tale M g H Z ℓ k' p (χ:=χ)
local notation "Xs"=> Positions (Uniform.Primary c G)
include hM ht hn hK hB hh hP hR hp
set_option maxHeartbeats 360000 in
lemma proven (hW:Sluice.Shore G L P'.order s v)
   (h:Rooted (origins M H) (Checks.treat (χ:=χ) (ρ:=g) (miss M H D' m ℓ k')) P' a w)
   (t : Positions (Uniform.Primary c G)) (hU:‖t‖+2*Sienna.furl G L s<v) (hF:flags P'.threshold (actual t)=∅)
   (he:p.card ≤ m)
   (hL:∀ W:Positions (Uniform.Primary c G), ‖W‖+2*Sienna.furl G L s<v → actual W∈sunny P' → Brush P'.order K v⁻¹ ((Reels.allotV M g H p (χ:=χ) - V)∘Boulevard.actual) W): ∀ l:List (Directions G c), l.length ≤ P'.order → (∀ i∈l, ‖i‖≤ P'.threshold) →
    ‖leftDerivs (Stowe.tale M g H (Drawing.cabinet H D') ℓ k' p (χ:=χ) - V) l (actual t)‖ ≤ (Boulevard.ticket P'.order (K+K)+2*((Fintype.card (Site c):ℝ)*w))+(K+(Fintype.card (Site c):ℝ)*w):= by
   let W:= balance M g H D' ℓ k' p (χ:=χ)
   have ht' : Rooted (Ft) W P' a w:= by
     refine h.fresh ?_; intro i; unfold W balance Checks.treat; split
     next hi=> rw [if_pos (universal M H D' _ _ i hi he hp)]; exact Or.inl rfl
     next hi=> exact Or.inr rfl
   choose o ho using fun z:ZA=> notEmpty M H z
   let C i:= (⟨o i,Ft i,ho i⟩: RegularAddress c)
   have htA:= ht'.tap o ho ht -- prior.Oath
   have ht₀ :P'.Regular univ (Ū - V):= CouplingShape.reg_sub (Meadow.regularA _ fun i _=> CouplingShape.reg_extend (hB.viable _) (subset_univ _)) hM
   -- reindex stage. add zero padding.
   let x:= numbering (ZA ⊕ ℕ); let A₀':=(Sum.elim C (fun _ : ℕ=> ((⟨0,{0},Finset.mem_singleton_self _⟩:RegularAddress c)))); let X : ZA ⊕ ℕ→ Config G c→ℝ:= Sum.elim W 0
   obtain ⟨b,hb,hR'⟩:= htA; let b':= Sum.elim b (fun _:ℕ=> (0:ℝ))
   have hg : Meadow.Budget P' (A₀' ∘ x) (X ∘ x) w:= by
     refine ⟨b'∘ x,fun o=> ?_,fun i=> ?_⟩
     · let g i:= if (A₀' i).site=o then b' i * Real.exp (preExponent P'*coverNumber P'.B (A₀' i).support) else 0
       refine Cost.equiv x (?_: SumBudget g w); rw [← add_zero w]; refine Cost.sum (hb o) ?_
       simp [g,b',SumBudget]
     change P'.Regular (A₀' (x i)).support (Sum.elim W 0 (x i)) ∧ P'.supBounds (A₀' (x i)).site (A₀' (x i)).support (X (x i)) (b' (x i)); cases hQ:x i with
     | inl v=>exact hR' v -- after change
     | inr k =>exact ⟨CouplingShape.reg_const _, VerifiedReset.sup_le (CouplingShape.sup_const _) (le_of_eq abs_zero)⟩
   refine Oceanic.clasp P' (A₀' ∘ x) (X ∘ x) _ _ rfl hh hn hW hg t hU hF ht₀ (fun V' hx=> ?_) hL
   have hY:∀ Y: Support c,Healthy P'.threshold Y V':=fun i=> (by unfold Healthy; rw [Boulevard.smoky hx]; simp)
   let f':= Reels.allotV M g H p (χ:=χ)
   have hh: Stowe.ship M g H (Drawing.cabinet H D') ℓ k' p V' (χ:=χ)= Ū V':= by unfold ship Stowe.tale; rw [Finset.sum_apply]; exact Finset.sum_congr rfl fun i _=> (congr_fun (hK i) V').trans (masked_eq _ _ _ _ (hY _))
   have hE:f' V'= _ := alpine M g H P' D' p hp (by assumption) hP hK hB hR k' ℓ V'
   have hz: Summable fun i=> X (x i) V':=by obtain ⟨h,hb,hk⟩:=hg; apply Summable.of_norm_bounded ((Boulevard.planetary hb (fun i=> (hk i).2.1)).2.1); exact fun i=>(hk i).2.2 V' (hY _) [] (by simp) (by simp)
   have hm: Summable fun i=> X i V':= x.summable_iff.mp hz; have hw:= (hm.comp_injective (Sum.inl_injective (β:=ℕ))); change Summable (fun i=> X (Sum.inl i) V') at hw
   have he' : ∑' z:ZA,masked P'.threshold (Ft z) (W z) V'= Boulevard.throng (X ∘ x) V':= by
      unfold Boulevard.throng Function.comp; rw [Equiv.tsum_eq x (f:=fun i=> X i V'), Summable.tsum_sum (f:=fun i=> X i V') hw (show Summable (fun i:ℕ=>X (.inr i) V') from summable_zero),show ∑' i:ℕ, X (Sum.inr i) V'=0 from tsum_zero, add_zero]
      exact tsum_congr fun k=> masked_eq _ _ _ _ (hY _)
   change (f' V' - V V')=(_-_)+ _; rw [hE,hh]; rw [he']; ring
end Bridges
end YM.RGComparison01.Pledge
