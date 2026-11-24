import YM.QuadraticLocal.Rough.Force
/-!
 # Publish Mark rational Kernel Π Yt estimates for ALL replicas

 Trick. Cl.Score Op already answers Non-tax Marker Log part at
 l*Y where Y a genuine post polynomial. Need ALL petitions in bound.
 Use larger l'=Υ*l so that ALL MARK-carrying outputs have at least
 one degree paid. Network theorem keeps *total* Brunch.Member values
 & Aff etc permits simultaneously.Estimate irrespective.Footprint.Actor.Asset.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Glit
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι α : Type}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
open Lyric Mosaic Muse Sleet
variable (Z:Set ι)(l:ι→ℝ) (δ:ℝ)


open Script
variable (U:Pad H j χ)
local notation "F'"=> U.S.N
local notation "L₁"=> Muse.song M H χ U.V (∅:Set ℕ) 0
local notation "P₀"=> tax G L x
local notation "up"=> (Lyric.mulScale (tax G L x) l)
variable {τ κ K Y γ V T0:ℝ}
variable (h:Roles H χ U k s J I a d e K σ Y γ V T0)(hw :Motto M (Lyric.mulScale (Lyric.tax G L x) l) 0 H τ K Y I)

variable {Ψ:ℝ}(hp:1 ≤ Ψ)(hΓ :Motto M (Lyric.mulScale (Y*Ψ) l) 0 H τ K Y I)
include h hp hΓ
local notation "st"=> ( Lyric.mulScale Ψ l )
local notation "Φ"=> Staff M H
local notation "Z"=> ( Set.univ : Set (Staff M H) ) -- conflict Z
local notation "billing" lv:max=> ( Muse.toll M H lv (Muse.song M H χ U.V ∅ 0) j J )
local notation "sℓ"=> ( Lyric.mulScale (Y*Ψ) l )
set_option quotPrecheck false
local notation "cW" i:max=> ( Lyric.notes M H ((i).fst) ((i).snd) )
omit h hp hΓ
lemma compact (i:Staff M H)(w:ℝ) : ( billing (Lyric.mulScale w l) ) i = w^(cW i)* (billing l) i := by unfold Muse.toll Lyric.Bill; rw [ Lyric.toll ]; ring
include h hp hΓ
lemma nonneg : ∀ i,0 ≤ l i:= by obtain ⟨V',hu,w',b,hv⟩:= hΓ.claim; exact fun i=> nonneg_of_mul_nonneg_right (hv.currency i) (mul_pos (zero_lt_one.trans_le h.allowed) (zero_lt_one.trans_le hp)) -- lemma order?
variable (F:BudgetPoint)(hx:F.B=radiusB x)(ht:F.threshold=Pressure.temp x)(hn:F.order≤ j)(hk:F.power≤J)
include hx ht hn hk
section fin
variable [Fintype ι]
lemma financially : Network M H χ l F (Set.univ) (billing l) a γ ∧ Network M H χ (st) F Set.univ (billing st) a γ:= by
  obtain ⟨X,hX,s',p0,hc⟩:= hΓ.claim; obtain ⟨hh,hT⟩:= h.answer _ M; have hp' := Glit.nonneg M H χ l U h hp hΓ
  have hW : Ac.Hit (Captain.reachability (H:=H)) (radiusB x) (fun z=>∑ i:Syllable M H z,Lyric.Bill M H L₁ z (st) j i J) a γ:= by
    have he: ( Lyric.mulScale Y⁻¹ sℓ )= (st):= by ext1 i; unfold Lyric.mulScale; field_simp [(zero_lt_one.trans_le h.allowed).ne'];
    exact he ▸ (hT X s' p0 _ τ hc hΓ.target)
  have hQ i: 0≤ (billing l) i:=by unfold Muse.toll Lyric.Bill; exact mul_nonneg (prod_nonneg fun i _=>prod_nonneg fun i _=>hp' _) (Lyric.dividend_nonneg M H χ hh _ _)
  constructor
  · apply Muse.reunion M H χ _ l F hx ht hn hk (L₁) hh ( Set.univ ) (fun z i=> True) (fun i _=>trivial) _ hp'; simp only [if_true]; intro i; refine budget_mono (hW i) ?_ ?_
    · intro z; dsimp only; split; next=> exact mul_nonneg (sum_nonneg fun s _=> hQ ⟨z,s⟩) (Real.exp_pos _).le
      next=> exact le_rfl
    intro j; dsimp only; split; next H'=>
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; apply sum_le_sum; intro i hV; change ((billing l) ⟨j,i⟩) ≤ _; exact ( le_mul_of_one_le_left (hQ ⟨j,i⟩) (one_le_pow₀ hp) ).trans_eq ( Glit.compact M H χ l U (J:=J) ⟨j,i⟩ Ψ ).symm -- expects trans_eq defeq
    next=>exact le_rfl
  refine Muse.reunion M H χ _ (st) F hx ht hn hk (L₁) hh ( Set.univ ) (fun _ _=>True) (fun _ _=> trivial) ?_ (fun i => mul_nonneg (zero_le_one.trans hp) (hp' _)); simpa only [if_true] using hW
end fin
lemma fℓ : Network M H χ l F (Set.univ) (billing l) a γ ∧ Network M H χ (st) F Set.univ (billing st) a γ:= by
 let P':= F; let q (p:Finset ι):= M ∘ Script.restrict p; have hE (p:Finset ι) := financially (q p) H χ (l ∘ Script.restrict p) U h hp ( Script.scaled M H _ (sℓ) 0 hΓ ) F hx ht hn hk
 constructor
 · apply Script.recover; refine Eventually.of_forall fun p=>?_ ; rw [Script.bone, Set.preimage_univ]; exact (hE p).1
 apply Script.recover; refine Eventually.of_forall fun p=>?_ ; rw [Script.bone, Set.preimage_univ]; exact (hE p).2

local notation "pub"=> ( {i:Staff M H| 1≤ cW i} )
lemma grout : Network M H χ l F ({i:Staff M H| 1≤ cW i}) (billing l) a (Ψ⁻¹ * γ):=by
 obtain ⟨ha,hb⟩:= fℓ M H χ l U h hp hΓ F hx ht hn hk; have he:= zero_lt_one.trans_le hp; refine ⟨fun i _=>ha.mark i (Set.mem_univ _),fun i=>budget_mono ( budget_scale (inv_nonneg.mpr he.le) (hb.costs i) ) ?_ ?_⟩
 · intro q; dsimp only; split
   · split
     · exact mul_nonneg (ha.mark q (Set.mem_univ _)|>.nneg) (Real.exp_pos _).le
     · rw [zero_mul]
   · exact le_rfl
 intro q; dsimp only; rw [if_pos (show q∈ Set.univ from Set.mem_univ _)]; split; split; next _ hh=>
    rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; rw [Glit.compact]; rw [← mul_assoc]; have hQ:= pow_le_pow_right₀ hp (show 1 ≤ cW q from hh); rw [pow_one] at hQ; exact le_mul_of_one_le_left (ha.mark q (Set.mem_univ _)|>.nneg) ((le_div_iff₀ he).mpr (show 1*Ψ ≤ Ψ^(cW q) from (by simpa only[one_mul] using hQ)) |>.trans_eq (div_eq_inv_mul ( Ψ^(cW q) ) _) ) -- one_mul orientation?
 next=> rw [zero_mul]; exact mul_nonneg ( inv_pos.mpr he ).le (mul_nonneg ( (hb.mark _ (Set.mem_univ _)).nneg ) (Real.exp_pos _).le)
 next=>rw [mul_zero]
end YM.RemainderComparison.Glit
