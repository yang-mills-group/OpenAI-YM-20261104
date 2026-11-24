import YM.LocalLTE.FieldPT.Pools
/-!
 DNA transfer through ordinary mass, not assuming order of hard attachments.
 Positivity `C>=0` from anchored. Full support; assemble before surrounding soft changes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open YM.LocalLTE YM.LocalLTE.Weft FrameBox FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side} {j z k M:ℕ} {W κ K U C V t H: ℝ}
attribute [local instance] Gauge.frobInner
open Residual Geo Animals Quotes Extra.Iteration Averaging
structure ForestQ (ι:Type) (A:ι→RegularAddress n) (p:BudgetPoint) (F:(i:ι)→Option (Σ z, Art (A i) z)) (f:ℝ→ι→ Pot G n) (C κ:ℝ) (K z j:ℕ) : Prop where
   payment : ∃ g:ι→ℝ, anchored p A g C ∧ ∀ i:ι, DNA (A i) (F i) p z (pie j+1) K κ (g i) (fun s=> f s i) ∧ ∀ s∈Weft.clip, Comic G (A i) p (f s i)
lemma ForestQ.raising {ι:Type}{A:ι→RegularAddress n}{p:BudgetPoint}{F:(i:ι)→Option (Σ z, Art (A i) z)}{f:ℝ→ι→ Pot G n}(h:ForestQ ι A p F f C κ k z j) (he:k ≤ M)(hh:C≤V):ForestQ ι A p F f V κ M z j:=by
   obtain ⟨c,hc,hF⟩:=h.payment; exact ⟨c,fun i=>budget_loosen (hc i) hh, fun i=> ⟨(hF i|>.1).larger le_rfl le_rfl he le_rfl,(hF i).2⟩⟩
section fits
variable (j:ℕ) (p:BudgetPoint) (R : PathData G) (c:Clip)(A:Listing G n)(D:Tour A z)(κ:ℝ) (θ:ℝ) (W:ℝ)
variable {q:ℝ}(h:Reliable G κ q)(hG:G.Simple)(ht:3≤ p.B)(he:32*z<n.val)(hm:2*p.B≤z)
variable {X₁ V₁ :ℝ} {t₁ H₁ Λ Λ':ℝ} (hP:R.Bounds c t₁ Λ Λ')(hC:Geo.Width p c t₁)(hg: WilsonStartup.Decent c p)
variable (Ψ:ℝ→ℕ→Pot G n)
set_option quotPrecheck false
local notation "U'"=> (tubeX R p A)
local notation "P'"=> (gallery R p A z D ht)
variable (hΨ:Genome A D p j k κ Ψ W)
local notation "Ξ"=> (fun s=>delta (A.read (Price.emp (Ψ s))))
-- parameter payload fresh Φ uses only head E cards (and δ thereof). Flag support masks retained for s=g.
def stageQ (s :ℝ) := Price.vane R c p A z D κ θ (delta (A.read (Price.emp (Ψ s)))) j (Ψ s)
local notation "f!"=> stageQ (z:=z) j p R c A D κ θ Ψ
include hG h hm he ht hΨ
-- myth costs.Sum uses anchored.Geometry expand.Act honors.
variable (B:ℝ)(hp:1 ≤ B)(hH:∀ (o:Site n)(X:Grove o)(i:ℕ), i< z→ Brush 2 B 1 ((X.crook i Chi.canonical κ (G:=G))∘ Grove.soloV) 0)(hV:∀ (o:Site n)(q:PlaqAxes→PlaqAxes→ℝ)(v:ℝ), (∀ i j,|q i j|≤v)→ Brush (pie j+1) (v*C) 1 (counter q o (G:=G) ∘ Grove.soloV) 0 ) (hc:0≤C)
-- EP no cost for redundant zeros.
local notation "P!"=> DNA.centered (pie j+1) B 2
local notation "Q!"=> DNA.centered (pie j+1) B 2 * (z:ℝ)^2
include h hp hH hV hc
lemma laurels : let V:=P'; ForestQ ℕ (U' ∘ Sum.inl) p (fun (i:ℕ)=> V (.inl i)) (fun s i=>f! s (.inl i)) ((1+P!+(Q! * C))*W) κ k z j:=by
    intro V; obtain ⟨x,hx,H⟩:=hΨ.bills; let C':=1+P! +Q!*C
    have hh:0≤P!:=by unfold DNA.centered Scene.scoreBp; positivity
    have hC:0≤C':=by unfold C'; positivity
    let Y:= fun i=> if (D i).isSome then x i else 0
    have he' (i):0≤Y i:= by unfold Y; split; exact (H _).sure; exact le_rfl
    refine ⟨fun i=>C' * Y i,anchored_scale hC (?_),fun i=> ?_⟩ -- edit
    · intro i; refine budget_mono (hx i) (fun j=> ?_) (fun j=> ?_)
      · split; exact mul_nonneg (Real.exp_nonneg _) (he' _); exact le_rfl
      let v:= A.reg j; change (if (U' (.inl j)).site=i then p.mass (U' (Sum.inl j) |>.support) (Y j) else 0) ≤ _; unfold Y; split
      next hv=>rw [if_pos (show (A.reg j).site=i from hv)]; split
               next hQ=>
                obtain ⟨u,hU⟩:=Option.isSome_iff_exists.mp hQ
                exact le_of_eq (congr_arg (fun g=>p.mass g _) (show expand (A.reg j)=v.support from u.crisp ▸ Price.extents u)) -- edit
               next=> unfold BudgetPoint.mass; rw [mul_zero]; exact mul_nonneg (Real.exp_nonneg _) (H _|>.sure)
      exact hx i|>.1 j
    cases hg: D i with
    | none=>
      have hz s: f! s (.inl i)=0:= by change Price.hail _ _ _ _ _ _ i=_; unfold Price.hail; rw [hg]; rfl
      have hN:V (Sum.inl i)= Option.none:= by unfold V gallery; simp [pruned,hg]
      exact ⟨⟨mul_nonneg hC (he' _),fun _ i _=> hz i,fun _ _ h=> by rw [show _ = none from hN] at h; cases h⟩,fun s _=> hz s ▸ Price.flick p⟩ -- edit
    | some B'=>
      have h' s:f! s (.inl i)=Price.myth B' (Ψ s i) κ j:=by change Price.hail _ _ _ _ _ _ i=_; unfold Price.hail; rw [hg]; rfl
      have hy:P' (.inl i)= Option.some ⟨z,( ⟨B'.grove,B'.radius,Price.extents B',B'.bonus,B'.hearth⟩:Art (U' (.inl i)) z)⟩:=by unfold gallery; simp [pruned,hg] -- edit
      obtain ⟨_,hy',ht'⟩:= (H i).arts z B' (by simp [hg])
      have hx': C'*Y i=(x i+x i*P!) + (x i*P! * ((z:ℝ)^2))*C:=by unfold C' Y; simp_rw [hg]; rw [if_pos (by simp)]; ring
      have hV₀ (s:ℝ)(hs:s∈Weft.clip): Comic G (U' (.inl i)) p (f! s (.inl i)):= by rw [h']; exact ⟨Price.forge B' _ (ht' _ hs) _ h, Price.crisp B' (Ψ s i) h p j, fun hz x y=> Price.kineticZero _ _ (ht' _ hs) hG hz (by omega) h j x y⟩
      refine ⟨⟨mul_nonneg hC (he' _),fun he=>False.elim (?_),fun z1 a hz=>?_⟩,hV₀⟩
      · rw [show V _ = _ from hy] at he; cases he
      obtain ⟨rfl,rfl⟩:=Sigma.mk.inj (Option.some.inj (hy.symm.trans hz)); refine ⟨le_rfl,?_,fun s hs=> hV₀ _ hs|>.1⟩
      have hc': Arp k 2 (x i*P!) (fun s=>Ψ s i ∘ Grove.soloV):= Hall.bare ▸ (H i).rooted 2 h hp hH
      simp only [h',hx']; exact Price.capBudget hG (A.reg i) _ j _ hy' ht' hc' (hV _)
local notation "Y'"=> W*Q!
include hP hC hg
lemma books (hL:0≤U)(he':|θ| ≤ V)(hv:∀ i:Low, Low.length R i< p.B→ Brush (pie j+1) (|i.mark R c| *U) 1 (i.fresh R c (0:Site n) factor ∘ soloV) 0)(hx: ∀ i:High,i.length R< p.B → Brush (pie j+1) (i.charge R*U) 1 (High.fresh R i (0:Site n) 0 factor ∘ soloV) 0) : ForestQ (EKey n) (U') p (P') f! (((1+P!+(Q! * C))*W) + ( (Y' *U)*(anchoredFee p lowCount * lowerSize c Λ) + ((Y'+V)*U) * (Price.tH p*(anchoredFee p highCount*(Λ+Λ))))) κ k z j:=by
    obtain ⟨f,h₁,h₂⟩:= (laurels j p R c A D κ θ W h hG ht he hm Ψ hΨ B hp hH hV hc).payment
    let Δ:=Ξ; obtain ⟨hd₁,hc'⟩:= Price.salaryZ hΨ h hG hH hp
    have h₁':0 ≤ Y' := (abs_nonneg _).trans (hc' 1 ⟨zero_lt_one,le_rfl⟩)
    have hV':0≤ V:=(abs_nonneg _).trans he'; let f'(i:Faces n):= |i.2.mark R c| * (Y'*U); let g'(i:Spikes n):= i.2.charge R * ((Y'+V)*U)
    refine ⟨Sum.elim f (Sum.elim f' g'),fun i=> ?_,fun i=>?_⟩
    · have hv:=(anchored_scale (mul_nonneg h₁' hL) (Price.lBase hP p hC)) i
      have he':= anchored_scale (mul_nonneg (add_nonneg h₁' hV') hL) (Price.heightL (p:=p) (R:=R) (fun i:Spikes n=> show 0 ≤ i.2.charge R from sum_nonneg fun _ _=> abs_nonneg _) (Price.hBase hP p hC)) i
      refine Cost.sum (h₁ i) (Cost.sum ?_ ?_)
      · convert hv using 1; ext b; dsimp only [tubeX, Sum.elim,f']; rw [mul_comm |Low.mark ..| (Y' * U)]; congr 1
      convert he' using 1; ext b; dsimp only [tubeX, Sum.elim,g']; rw [mul_comm (High.charge R b.2) ((Y'+V)*U)]; congr 1
    rcases i with i|⟨v,i⟩|⟨v,i⟩
    · exact h₂ _
    · exact Price.quartets j p R c A D κ θ Δ (Y') h hG ht he hm hd₁ hc' h₁' Ψ i v hL (hv i) hg
    exact Price.treble j p R c A D κ θ Δ (Y') h hG ht he hm hd₁ hc' h₁' hP Ψ i v he' hL (hx i)
end fits
end YM.AnalyticBridge.VerifiedReset.Collection.Price
