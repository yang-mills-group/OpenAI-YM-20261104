import YM.MSbar.Lease.Ticket
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath.Cottage
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums WilsonStartup Bulk
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge} {c f:Side} {S:StepData c f} {U:Config G f}{R: Rep G f}{R':Rep G c}{σ C T K B a b v r δ w β u:ℝ}{M k m:ℕ}
open ConnectedActivityE6 Finset RG.PathData Tree Push.Uniform Pressure SectorNext.Vacuum AnalyticBridge.VerifiedReset Next.Scheduling Precision Stock Metric Posture
variable (P:Patch)(D:KernelChoices)(p:Palisade)(J:Voice G) (L L' : Stage)
set_option quotPrecheck false
local notation "Ξ"=> tip G P.L
variable (F:Forest S.ratio)(i:S.Choices) (W : Positions (Primary c G)) (x s d : ℝ)
local notation "t!"=> courage G P.L x
local notation "Δ"=> (tip G P.L x)
local notation "R!"=> rot p Δ
local notation "B!"=> radiusB Δ
local notation "M!"=> voyageB Δ
local notation "X!"=> vest (priced F i R.clip R.path) W
local notation "V"=> represent (tint G (Exterior.Body 1 c) W)
local notation "m!"=> (stockMove G p Δ)
variable (Z Y:Support f) (g:Clear G J)(A : S.patch=P)(A':S.kernel=D)
       (h : Season J L L' x R R' S (courage G P.L x))
       (t: Grants i R F p m)
local notation "n!"=>Horizon P D G J L L' p m x d
variable (O:Horizon P D G J L L' p m x d) (H : Tinted L L' x P D p J R R' (courage G P.L x) (snow G P x) (courage G P.L x))
variable (ht: ‖W‖ ≤ skies (tip G P.L x))(hp:Posture p J F (pillow (tip G P.L x)) (room (tip G P.L x)) (base J (tip G P.L x)) (rot p (tip G P.L x)) (voyageB (tip G P.L x)) (radiusB (tip G P.L x)) Z Y W (vest (priced F i R.clip R.path) W) R.p)
local notation "yz!"=> pluma
local notation "a!"=> pillow Δ
local notation "b!"=> room Δ
local notation "J!"=> hotel F Z Y J V X! a! b!
local notation "e'"=> chance S R V
local notation "h!"=>Admitted (represent (tint G (Exterior.Body 1 c) W)) R S L'.width L'.paths (ability (tip G P.L x)) (lbt (tip G P.L x)) 1
private lemma chroma (j:F.Free)(l:G.ColorIndex)(r:ℝ) (g:Clear G J): MeasurableSet (pluma J R W i F (j,l) r):=by
    have he:Continuous fun U:Config G f=> flume F V U j:= Continuous.mul ((continuous_apply _).comp (canoe_cont F)) continuous_const
    exact measurableSet_lt measurable_const (((((EuclideanSpace.proj (𝕜:=ℝ) l).continuous.measurable.comp g.reads).comp he.measurable).sub measurable_const).abs)
include t g O ht H A A' h hp
lemma glows (hi:h!) :
   e' J!ᶜ ≤ (Y.card*4)* ((Lattice.box (macroR P)).card*t!+t!+(Fintype.card G.ColorIndex)*Δ^d) :=by
    let Jx:= e' ; let E:= board F Y; let T:= hotel F Z Y J V X! (pillow Δ) (room Δ); let z(j:F.Free):= basin F J V X! j (pillow Δ)
    have he(j:F.Free)(he:j∈E):MeasurableSet (z j):= portico F Y J V X! g _ j he|>.from_here; have hb :Seal S (youth F Y) T:= garden_main F Z Y J V X! g hp.extendsX
    have hζ : Tᶜ⊆ ⋃ i∈E,(z i)ᶜ:=by
        intro i hc; by_contra hh; apply hc; have ht(j)(hp:j∈ E): i∈z j:= by_contra fun h=> hh (Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hp,h⟩⟩)
        refine ⟨fun j hx=>?_, fun j hx=> ht j (mem_sdiff.mp hx).1⟩
        have he:= (ht j (mem_filter.mpr ⟨mem_univ _, hp.extendsX ((mem_filter.mp hx).2)⟩)); exact ⟨he.1,fun k=> (he.2 k).trans hp.goes⟩
    let z₀:=(Lattice.box (macroR P)).card*t!+t!; let q' :=(Fintype.card G.ColorIndex:ℝ)*Δ^d
    have hW:= h.case_; rw [A] at hW; have hyp:0 < Δ:= zero_lt_one.trans hW.enough; have hZ:0≤ t!:= (Real.exp_pos _).le
    let v₀:= base J Δ; let u:= brow S G v₀ R.p.threshold R.p.threshold
    have hG (j:F.Free):G.chord (replica S.ratio V j.val) ≤ v₀/4:=by unfold replica; split; rw [G.chord_one]; exact div_nonneg hp.lights.le (by norm_num); exact hp.folds _ (Set.mem_univ _)
    have hx : u+v₀/4 ≤ J.δ :=by
        have hi : u ≤ ceiling Δ :=by unfold u brow breeze; rw [A,A']; exact H.rung
        have hG:=H.hues (increments Δ) (abs_of_pos (Real.rpow_pos_of_pos hyp _)) -- typo let
        exact (add_le_add_left hi _).trans ((le_add_of_nonneg_left (mul_nonneg (zero_le_one.trans g.cost) hG.warmth)).trans hG.holds)
    have ht₀(j:F.Free)(he': j∈E): e' (z j)ᶜ ≤ z₀+q':=by
        let G₀:= {U:Config G f| u< G.chord (canoe (S:=S) F U j)}; have hG':MeasurableSet G₀:= (isOpen_lt continuous_const (G.continuous_chord.comp ((continuous_apply j.val).comp (canoe_cont F)))).measurableSet
        let Z(k:G.ColorIndex):= pluma J R W i F (j,k) (pillow Δ); let Yq:= ⋃ k∈(Finset.univ:Finset G.ColorIndex), Z k; have hM(k):MeasurableSet (Z k):=chroma J F i W _ k _ g -- order
        have hz':e' Yq ≤ q' := by
           refine (join hi _ (fun k _=>hM k)).trans ((sum_le_sum (g:=fun _=> Δ^d) ?_).trans_eq ?_); exact fun k _=> O.gains R R' A A' h F i (j,k) W t ht
           rw [sum_const,card_univ,nsmul_eq_mul]
        have h₁ : e' G₀ ≤ z₀:= by
           have h₀ := around hi F j.val h.hull.lawful hp.folds H.holm hp.lights h.hull.decent h.taskEval h.bends.2.1 h.bends.2.2 (show 0≤ R'.beta from le_trans (half_pos (zero_lt_one.trans h.hull.enough)|>.le) h.hull.beta) h.bends.1 R.p.threshold_pos.le ((half_pos hyp).le.trans hW.beta) h.storm hZ
           refine h₀.trans (add_le_add ?_ (H.update A A')); unfold gCost; rw [A,mul_one]
        have hP : (z j)ᶜ⊆ G₀ ∪ Yq:=by
           intro U hU; by_cases ht:U∈G₀; exact Or.inl ht
           have hi : G.chord (flume F V U j)≤ J.δ:= by unfold flume; refine (G.chord_triangle ..).trans ((add_le_add (le_of_not_gt ht) ?_).trans hx); rw [G.chord_inv]; exact hG j
           apply Or.inr; by_contra hh; apply hU; exact ⟨(g.near _ hi).2.1,fun l=> le_of_not_gt fun H=> hh (Set.mem_iUnion.mpr ⟨l,Set.mem_iUnion.mpr ⟨mem_univ _,H⟩⟩)⟩
        exact (c_mono V hi (he j he'|>.compl) (hG'.union (Finset.measurableSet_biUnion _ (fun i _=>hM i))) hP).trans ((union_bound hi hG' (Finset.measurableSet_biUnion _ (fun i _=>hM i))).trans (add_le_add h₁ hz'))
    have hM(j)(hx:j∈E): MeasurableSet (z j)ᶜ :=(he j hx).compl
    refine (c_mono V hi (hb.from_here.compl) (Finset.measurableSet_biUnion _ hM) hζ).trans ((join hi _ hM).trans ((sum_le_sum ht₀).trans ?_)); rw [sum_const, nsmul_eq_mul]; have hu :0 ≤ z₀+q':= by unfold z₀ q'; positivity
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast boardC F Y) hu
end YM.MSbar.Heath.Cottage
