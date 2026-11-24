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
-- stencil continuation: exact canonical sparse basis component plus fitted
-- local polynomial on receipt radius. Uses slot scalar weight allocated to
-- each aspect. Raw regular bounds ALSO at actual support, not just the stance.
structure SoloInk (M:Leaf R)(v:Config G f→ℝ)(κ:ℝ)(p n:ℕ) : Prop where
   ink:∃ i:ℕ,M.turn=.logKey i
   reads: M.ingredient=RG.masked R.p.threshold M.crest v
   health: ∃ (i:ℕ),M.turn=.logKey i ∧ R.p.supBounds (R.activities.reg i|>.site) M.crest v M.weight ∧ R.p.Regular M.crest v ∧ ∃ d, d ≤ p ∧ ∃ (j: ((Labels.frames G).level d).Coeff)(e: Config G f→ℝ)(t:Bool),((Labels.frames G).level d).coeffSize j ≤ M.weight ∧ v=e+Port.scaleQ t ∘ (Push.Local.presented (Next.Foundations.localSection G d) (R.activities.reg i|>.site) (R.p.threshold) j) ∧ (R.p.supBounds (R.activities.reg i|>.site) M.crest e M.weight)∧∃ t≤n, FrameBox.Polynomial t κ (R.activities.reg i|>.site) p e
variable {ι:Type}[Fintype ι](M:ι→Lotus.Leaf R)(φ:ι → Config G f → ℝ)(κ:ℝ)
local notation "mz"=> Merge.Palette.sign M S
local notation "E"=> Disk G c
variable (Q: YM.ConnectedActivityE6.Target G P)(D:Merge.Tickets (Merge.Palette.sign M S))(H:Cash W t μ L Q o a T R)(he: ∀ i∈D.val,SoloInk (M i) (φ i) κ j n)(X:Coat T F)(p:Disk G c) -- issue Q rebind T.W lifts
local notation "X'"=> (timeΛ X p)
local notation "W'"=> team M D
variable (hX:X.x=t)(hK:X.width=o.K)(hp:(timeΛ X p).manifest)
include H hX hK hp he
omit [Fintype ι] in
lemma prideful (hT:Stamp T) (b:Air f G) (x: Directions G c)(hβ:p=(gStep R.beta,x)) (hf:∀ i: Tubular f G, |b i|≤ postponement L t o): payment (o:=o) M D X p b= oils M φ D X p b:=by
    obtain ⟨ht,h,hB⟩:= Fan.incomeA X H hX hK hT x p hβ hp b hf
    unfold payment Team.paidU team; rw [Finset.prod_image]; swap; · exact fun i hi j hj hz=> D.prop hi hj (congr_arg (fun i:Leaf R=> i.turn.badge S) hz)
    refine prod_congr rfl fun i hi=>?_ ; unfold Leaf.paidU Leaf.fond; rw [h, ←ht, (he i hi).reads,mul_one,masked_eq _ _ _ _]; unfold Healthy; rw [hB]; simp
end YM.LocalLTE.Fan
namespace YM.LocalLTE.Fan
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}
open Brush
lemma kettle {P:Teller G}(L:Side)(D:Patch)(hd:D.Branches P.bind G){d p :ℝ→ℝ}{N : ℝ→ℕ}(Q:YM.ConnectedActivityE6.Target G P){W:ℝ} (o:Target.Order G W)(j m:ℕ)(h₁:1≤j){v κ k:ℝ}(hW: -(1/2:ℝ) ≤ v)(h: v<0)(hp: Rate G L v p)(hp': ∀ᶠ x:ℝ in atTop,0≤p x)(hR:Reliable G κ k)(hk:Rate G L 0 d)(hN:Rate G L 0 fun t=>(N t:ℝ)):∃ V :ℝ→ℝ, Rate G L ((1/2:ℝ)*m) V ∧ ∀ᶠ t in atTop,
    ∀ (c f:Side)(S:StepData c f)(T:Tube G S), S.patch=D → ∀ μ α:ℝ, Target.GrantBodies W t μ L Q o α T → ∀ (F: Forest S.ratio) (X : Coat T F), X.x=t → X.width=o.K →∀ z: Air f G,(∀ i, |z i| ≤ |d t|)→∀ x: Disk G c,‖x‖<p t → ∀ (R:Rep G f)(M:PhysicalNext.Repeat.Lotus.Leaf R)(f: Config G f→ℝ), R.p.threshold=Pressure.fiery G t L → SoloInk M f κ m (N t) → Brush j (M.weight* |V t|) 1 (f ∘ inputΛ X z) x:=by
   obtain ⟨V,hV,H⟩:= Vine.field_fuel L D hd Q o j m h₁ hW h hp hp' hR hk hN
   obtain ⟨A,C,R,hA,hC,hX,hF⟩:=Vine.thistles L D hd Q W o j h₁ hW h hp hk hp' -- order
   let I:= Fin (m+1) × Bool; let U x:= |R x|; have hU: Rate G L 0 U:= hX.compare (Eventually.of_forall fun i=> (abs_abs _).le)
   choose f hf hx using fun i:I=> Port.Sect.kept G j i.fst.val L U hU m (Nat.le_of_lt_succ i.fst.isLt) (Port.scaleQ i.2)
   let u t:= ∑ i:I, |f i t|; let a t:= |V t|+u t; letI : Fintype I:= (inferInstanceAs (Fintype (Fin (m+1)×Bool))) -- maybe issue earlier.Infer.L via let reduce
   have hg {g:ℝ→ℝ} (h:Rate G L ((1/2:ℝ)*m) g): Rate G L ((1/2:ℝ)*m) (fun t=> |g t|):= h.compare (Eventually.of_forall fun _=> (abs_abs _).le)
   have he(s:Finset I): Rate G L ((1/2:ℝ)*m) (fun t=>∑ i∈s,|f i t|):=by
       induction s using Finset.induction_on with
       | empty=> simp only [sum_empty]; exact (Rate.const _).weaken (by positivity)
       | insert i s hi ih=> simp only [sum_insert hi]; exact (hg (hf i)).add ih
   refine ⟨a,(hg hV).add (he Finset.univ),?_⟩
   filter_upwards [H,hF] with t hv hY c f' S T hS μ α H F X ht hs z hz x hp R'ζ M k hT hf
   obtain ⟨l',h0,hB,hC,i,hi,p₀,c',u',hA,hM,hV,h,hZ,hE⟩:= hf.health
   let v':= f (⟨⟨i,Nat.lt_succ_of_le hi⟩,u'⟩:I) t; have hP' :1≤ (fiery G t L)⁻¹:=hT ▸ (one_le_inv₀ R'ζ.p.threshold_pos).mpr R'ζ.p.threshold_le
   have hv':Brush j (((Labels.frames G).level i).coeffSize p₀ * v') 1 (Port.scaleQ u' ∘ (Push.Local.presented (Next.Foundations.localSection G i) (R'ζ.activities.reg l'|>.site) (R'ζ.p.threshold) p₀) ∘ inputΛ X z) x:=by
       rw [hT]; exact hx (⟨⟨i,Nat.lt_succ_of_le hi⟩,u'⟩:I) _ hP' f' _ _ _ _ (hY c _ S T hS μ α H F X ht hs z hz x hp.le|>.2.2) _
   have hB':= hv c f' S T hS μ α H F X ht hs z hz x hp _ _ _ _ _ hZ hE hT ⟨_,hV⟩ -- order
   rw [hM]; refine (hB'.gathering hv').climb (?_) le_rfl
   have he1:|v'| ≤ u t:=by exact Finset.single_le_sum (f:=fun i:I=>|f i t|) (fun i _=>abs_nonneg _) (Finset.mem_univ _)
   have he:= (Work.G08.size_nonneg _ p₀); have hB'' :0 ≤ M.weight:= M.profit; rw [mul_comm M.weight |a t|]; unfold a
   have hG:0≤ u t:= (abs_nonneg _).trans he1
   rw [abs_of_nonneg (add_nonneg (abs_nonneg _) hG), add_mul]; calc
      _ ≤ M.weight * |V t| + (((Labels.frames G).level i).coeffSize p₀)*(u t):=add_le_add le_rfl (mul_le_mul_of_nonneg_left ((le_abs_self _).trans he1) he)
      _ ≤ _:= by rw [mul_comm (|V t|), mul_comm (u t)]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hA hG)
end YM.LocalLTE.Fan
