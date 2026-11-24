import YM.LocalLTE.Ballot.Thief
import YM.LocalLTE.Ballot.Gain
import YM.LocalLTE.Quartz.Core
import YM.LocalLTE.Marked.Roots
/-! Root skeleton bill with independent coefficients, permits at true Path not homogeneous marker. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open FrameBox Pastel Merge Merge.Palette
-- m total credit mHeight.B.Y For analytic hats even when colliding
-- via previous heap. Supports all actual tagged siblings. No use of stencil
-- from output in this menu! Hull remedy at true Calendar T. Ink authorizes
-- predictors before bootstrapping.
set_option quotPrecheck false
structure ProductInk (M: Leaf R) (f:Config G _→ℝ)(κ:ℝ)(p n:ℕ):Prop where
   ink: ∃ i, M.turn = .logKey i
   reads: M.ingredient= RG.masked R.p.threshold M.crest f
   earn: Measurable f
   yields: ∃ (l:ℕ)(s:ℕ),l≤p∧s≤p ∧ l*s≤p ∧ ∃ (a:Fin l→Leaf R) (φ:Fin l→ Config G _→ℝ), (∏ i,(a i).weight)≤M.weight ∧ f=(fun v=>∏ i,φ i v) ∧ ∀ i, SoloInk (a i) (φ i) κ s n
variable {ι:Type}[Fintype ι](M:ι→Lotus.Leaf R)(φ:ι → Config G f → ℝ)(κ:ℝ)
local notation "mz"=> Merge.Palette.sign M S
local notation "E"=> Disk G c
variable (Q: YM.ConnectedActivityE6.Target G P)(D:Merge.Tickets (Merge.Palette.sign M S))(H:Cash W t μ L Q o a T R)(he: ∀ i∈D.val,ProductInk (M i) (φ i) κ j n)(X:Coat T F)(p:Disk G c)
local notation "X'"=> (timeΛ X p)
local notation "W'"=> team M D
variable (hX:X.x=t)(hK:X.width=o.K)(hp:(timeΛ X p).manifest)
include H hX hK hp he
omit [Fintype ι] in
lemma pridefulX (hT:Stamp T) (b:Air f G) (x: Directions G c)(hβ:p=(gStep R.beta,x)) (hf:∀ i: Tubular f G, |b i|≤ postponement L t o): payment (o:=o) M D X p b= oils M φ D X p b:=by
    obtain ⟨ht,h,hB⟩:= Fan.incomeA X H hX hK hT x p hβ hp b hf
    unfold payment Team.paidU team; rw [Finset.prod_image]; swap; · exact fun i hi j hj hz=> D.prop hi hj (congr_arg (fun i:Leaf R=> i.turn.badge S) hz)
    refine prod_congr rfl fun i hi=>?_ ; unfold Leaf.paidU Leaf.fond
    rw [h, ←ht, (he i hi).reads,mul_one,masked_eq _ _ _ _]; unfold Healthy; rw [hB]; simp
omit H hX hK hp he
variable (G)
lemma kettleX {P:Teller G}(L:Side)(D:Patch)(hd:D.Branches P.bind G){d p :ℝ→ℝ}{N : ℝ→ℕ}(Q:YM.ConnectedActivityE6.Target G P)(W:ℝ) (o:Target.Order G W)(j m:ℕ)(h₁:1≤j){v κ k:ℝ}(hW: -(1/2:ℝ) ≤ v)(h: v<0)(hp: Rate G L v p)(hp': ∀ᶠ x:ℝ in atTop,0≤p x)(hR:Reliable G κ k)(hk:Rate G L 0 d)(hN:Rate G L 0 fun t=>(N t:ℝ)):∃ V :ℝ→ℝ, Rate G L ((1/2:ℝ)*m) V ∧ ∀ᶠ t in atTop,
    ∀ (c f:Side)(S:StepData c f)(T:Tube G S), S.patch=D → ∀ μ α:ℝ, Target.GrantBodies W t μ L Q o α T → ∀ (F: Forest S.ratio) (X : Coat T F), X.x=t → X.width=o.K →∀ z: Air f G,(∀ i, |z i| ≤ |d t|)→∀ x: Disk G c,‖x‖<p t → ∀ (R:Rep G f)(M:PhysicalNext.Repeat.Lotus.Leaf R)(f: Config G f→ℝ), R.p.threshold=Pressure.fiery G t L → ProductInk M f κ m (N t) → Brush j (M.weight* |V t|) 1 (f ∘ inputΛ X z) x:=by
    let I:= Fin (m+1)
    choose f hf hF using fun i:I=> Fan.kettle L D hd Q o j i.val h₁ hW h hp hp' hR hk hN
    let a(i:I)(t):= |f i t|; let K:= {i: Fin (m+1) × Fin (m+1)// i.1.val*i.2.val ≤ m}; let b(i: K) t:= |f i.val.2 t|^i.val.1.val*(1+(i.val.1.val:ℝ))^j
    let Z t:=∑ i:K,b i t
    have hb (i:K): Rate G L ((1/2:ℝ)*m) (b i):=by
       have hs:Rate G L ((1/2:ℝ)*i.val.2.val*i.val.1.val) (b i):=((Rate.pow (w:=a i.val.2) ((hf _).compare (Eventually.of_forall fun x=>(abs_abs ..).le)) _).mul_right _)
       apply hs.weaken; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left; rw [mul_comm _ (i.val.1.val:ℝ)];exact_mod_cast i.property -- order
       positivity
    have hQ(s:Finset K):Rate G L ((1/2:ℝ)*m) (fun t=>∑ i∈s,b i t):=by
       induction s using Finset.induction with
       | empty=> simp only [sum_empty]; exact (Rate.const _).weaken (by positivity)
       | insert i s hi ih=> simp only [sum_insert hi];exact (hb i).add ih
    refine ⟨Z,hQ univ,?_⟩
    filter_upwards [eventually_all.mpr hF] with t ht c f S T hT μ α hA F X hX hK z hz x hh R M f0 hR hP
    obtain ⟨l,a,hL,hS,hY,u,φ,hw,hf,hV⟩:= hP.yields; let i:I:=⟨a,Nat.lt_succ_of_le hS⟩; let k:K:=⟨(⟨l,Nat.lt_succ_of_le hL⟩,i),hY⟩
    have h j:= ht i c f S T hT μ α hA F X hX hK z hz x hh R (u j) (φ j) hR (hV j)
    rw [hf]; have hz:=Brush.all_prod (Finset.univ) _ _ _ fun j (_:j∈ Finset.univ)=> h j
    apply (hz.trim).climb ?_ le_rfl; rw [Finset.prod_mul_distrib, Finset.prod_const] -- univ cardinal.
    have hU(k:K): 0≤ b k t:=by unfold b; positivity
    simp only [card_univ, Fintype.card_fin,Finset.sum_const, nsmul_eq_mul, mul_one,mul_assoc]; exact (mul_le_mul hw ((Finset.single_le_sum (f:=fun i:K=>b i t) (fun i _=> hU i) (mem_univ k)).trans (le_abs_self _)) (hU k) M.profit)
end YM.LocalLTE.Fan
