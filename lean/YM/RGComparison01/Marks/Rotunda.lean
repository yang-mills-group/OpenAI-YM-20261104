import YM.RGComparison01.Marks.Oceanic
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Slide.Mover
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Pledge
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas Ursell Trees Height Sail
open PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} {χ:Chi}
    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
namespace Rotunda
open Foreman Checks Baked Palette Pillow Resin Season Ink Heron
open Switch Mallow Ovens OmitClusters Song Refrain Motion
open Push.Uniform Sienna Fare Lapis Boulevard Next.Scheduling Further.LogJets
-- cert at sunny using true H display `f=H+W`. Need bound H(0)
variable (P':BudgetPoint) (A:ℕ→ RegularAddress c)(u:ℕ → Config G c→ℝ) (F H : Config G c→ℝ)
-- R remains before turnFee. both paths positive orientation.Mark LOG. Width.h rule allows zero bound separately.
variable {b : ℝ}
open Slide Gauge Work.E08 Push.Local
variable {m M:ℕ}(x:Site c)(y:Site f)(V:Config G c)
local notation "Aℓ"=> Slide.lev M
local notation "X"=> wrap c (Slide.lev M)
local notation "Y"=>wrap f (Slide.lev M)
local notation "Zc"=> (x-X)
variable (hc:2*(2*M)≤ f.val)
def bake (V:Config G c):Config G f:= Lattice.translate (wrap f (Slide.lev M)-y) (Slide.shape (Slide.cognac hc) (x-wrap c (Slide.lev M)) V)
local notation "ZZ"=> Slide.cognac hc
lemma aim : Agrees (Lattice.box M) (expandAt y (bake x y hc V)) (expandAt x V) := by
   rintro ⟨i,j⟩ hi hj
   have hp:(i+Aℓ)∈crystal (2*M):=(translate_crystal M i).1 hi
   have hf:i+Aℓ+step j∈crystal (2*M):=by rw [add_right_comm]; exact (translate_crystal M _).1 hj
   change shape ZZ Zc V ((wrap f i+y)+(Y-y),j) = V (_,j); have hx : wrap f i+y+(Y-y)=wrap f (i+Aℓ):= by rw [map_add]; abel
   rw [hx,vested hc (i+Aℓ) hp j hf]; exact congr_arg (fun x:Site c=> V (x,j)) (by rw [map_add]; abel)
lemma compass (i:Site f): separation Zc (Slide.sites ZZ Zc i) ≤ 2*M := Slide.village ..
lemma pole (x:Site c)(M:ℕ) : separation x (x-wrap c (lev M)) ≤ M:= by
   rw [show x-wrap c (lev M)=wrap c (-Slide.lev M)+x from (by rw [map_neg]; abel)]
   apply Slide.sep; rw [box_test]; constructor<;>intro i<;> simp [Slide.lev]
lemma post1 (hp:3*M≤n) : ∀ i:Site f,Slide.sites ZZ Zc i∈neighbors n x := fun i=>(neighbors_mem ..).2 ((separation_triangle _ Zc _).trans (by have ht:=pole x M; have he:=compass x hc i; omega))
lemma staffed (hp:3*M≤n) (hv:Healthy P'.threshold (neighbors n x) V) : RG.flags P'.threshold (bake x y hc V)=∅:= by
   unfold bake; rw [← pull_one]; exact Pane.tranquility _ (allFlag ZZ _ V _ (post1 x hc hp) P'.threshold P'.threshold_pos.le hv) _ _
variable (f': Config G f→ℝ) {X₀ : ℕ}
lemma walkG (U:Config G c) (Z: Site c→ G.El): translate x (gauge Z U)= gauge (fun t=> Z (t+x)) (translate x U):= by
  funext i; unfold Lattice.translate Lattice.gauge; dsimp only; rw [add_right_comm _ (Lattice.step _)]

def evolve (I:Directions G c) : Directions G c:=fun i=> I (i.1+x,i.2)
lemma journey (V:Config G c)(f:Config G c→ℝ)(l:List (Directions G c)):
  leftDerivs (f ∘ Lattice.translate x) l V=leftDerivs f (l.map (Rotunda.evolve x)) (Lattice.translate x V):= by
  induction l generalizing V with|nil=> rfl|cons p l ih=> simp only [leftDerivs,List.map_cons, ih]; rfl
lemma translationP (P' : BudgetPoint)(f':Config G c→ℝ)(he:P'.Regular Finset.univ f'):
    P'.Regular Finset.univ (f' ∘ Lattice.translate x):= by
  have hX : ∀ U:Config G c,Healthy P'.threshold univ U→Healthy P'.threshold univ (translate x U):=by
    intro U hU; unfold Healthy; rw [← pull_one,Pane.tranquility U _ ]; simp
    ext y; simp only [notMem_empty,iff_false]; intro hi; exact Finset.disjoint_left.mp hU (Finset.mem_univ _) hi
  let Z:Directions G c→L[ℝ] Directions G c:= {
          toFun := Rotunda.evolve x
          map_add' := fun _ _=>rfl
          map_smul' := fun _ _=>rfl
          cont := continuous_pi fun _=> continuous_apply _ }
  have hx (V) (hU: Healthy P'.threshold Finset.univ V): Push.Local.Chart P'.order (f' ∘ translate x) V:= by
     have he':=he.smooth _ (hX V hU); exact (show ContDiffAt ℝ (↑(↑P'.order:ℕ∞):WithTop ℕ∞) (fun z=> f' (increment (translate x V) z)) (Z 0) from (map_zero Z).symm ▸ he').comp _ Z.contDiff.contDiffAt
  refine ⟨fun i j h=> ?_, he.borel.comp (show Continuous (translate x (K:=G.El)) from (by unfold Lattice.translate; fun_prop)).measurable,fun q U=>?_,hx,fun U hu A l hl=>Next.Foundations.left_has _ hl (hx U hu)⟩
  · have ht:i=j:=funext fun k=> h k (mem_univ _) (mem_univ _); rw [ht]
  change f' (translate x (gauge q U)) = _; rw [walkG,he.symmetry]; rfl
lemma reel (hp:3*M≤ n)(ht:P'.Regular Finset.univ f'): P'.Regular (neighbors n x) (f' ∘ bake x y hc):= Slide.regular ZZ Zc (translationP _ _ _ ht) (post1 x hc hp) -- args order
-- need new positions under rotations. Uses TRUE Euclidean spaces, Lift sup norms hold in this exact config
local notation "Xs"=> Positions (Uniform.Primary f G)
def south (u:Xs) (i: Uniform.Primary f G):= u ((i.1.1+y,i.1.2),i.2)
lemma yanks (u:Xs)(Y₀:Site f) : translate Y₀ (Boulevard.actual u)=Boulevard.actual (Rotunda.south Y₀ u):=by
   funext p; change represent _ _= represent _ _; simp_rw [Work.F03.represent_link]; rfl
lemma ocean (u : Positions (Uniform.Primary f G)): ‖south y u‖ ≤ ‖u‖:= by exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i=> norm_le_pi_norm u ((i.1.1+y,i.1.2),i.2) -- need type
variable {i:Site c}{n:ℕ}
-- price recenter jets for Slide.stalled
lemma emits (i' : Site c) (hp:separation x i' ≤ n)(d:Directions G c)(hv:P'.dirBound i' d): P'.dirBound x (((1+(n:ℝ))^P'.power)⁻¹ • d):=by
   let q:ℝ:=1+n; have hQ : 1 ≤ q := le_add_of_nonneg_right (Nat.cast_nonneg _); let s:= q^P'.power; have hs:1 ≤ s:= one_le_pow₀ hQ
   intro i; change ‖s⁻¹ • (d i)‖≤ _; rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hs)),inv_mul_le_iff₀ (zero_lt_one.trans_le hs)]
   apply (hv i).trans; rw [mul_left_comm s P'.threshold, show s=q^_ from rfl,← mul_pow]; refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) P'.threshold_pos.le
   have he := (separation_triangle i.1 x i').trans (Nat.add_le_add_left hp _); have hv': (separation i.1 i':ℝ) ≤ (separation i.1 x:ℝ)+(n:ℝ):= by exact_mod_cast he
   unfold q; nlinarith only [hv',mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) (Nat.cast_nonneg (α:=ℝ) (separation i.1 x))]
-- Actual P moves budget. flags univ on W.Y.Frame.
lemma shift_bill (U:Config G c)(F:Config G c→ℝ)(_he: Healthy P'.threshold Finset.univ U)
    (hm : ∀ l:List (Directions G c),l.length ≤ P'.order → (∀ i∈l,‖i‖≤P'.threshold)→ ‖leftDerivs F l (Lattice.translate x U)‖ ≤ v) :
    ∀ l:List (Directions G c),l.length≤P'.order → (∀ i∈l,‖i‖≤P'.threshold)→ ‖leftDerivs (F ∘ translate x) l U‖ ≤ v := by
   intro l hl hp; rw [Rotunda.journey]; apply hm _ (by simpa using hl); intro i hi; obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hi
   exact (pi_norm_le_iff_of_nonneg P'.threshold_pos.le).2 fun i=> (norm_le_pi_norm j _).trans (hp j hj)

abbrev priceP (P:BudgetPoint) (z n:ℕ):=((1+(n:ℝ))^(P.power * P.order) * (2^P.order * (1+(z:ℝ))^(P.power * P.order)))
-- estimate cost for all directions at any point in the refined mask. do not infer from
-- stencil-local exp.Triangle. m' = Halo radius around shift.
lemma tickets (m':ℕ) (hf: 2*M +1 ≤ m') (hr: M + m' ≤ n)(hX: 2*n<c.val)
    (hp:P'.threshold≤2*Pressure.fiery G t L)(hx:Sluice.Health G L m' t r)
    (hK:P'.Regular Finset.univ f') (ha:0≤a)
    (he:∀ V:Positions (Uniform.Primary f G),‖V‖+2*Sienna.furl G L t<r→ RG.flags P'.threshold (actual V)=∅→ ∀ l:List (Directions G f),l.length ≤ P'.order → (∀ i∈l,‖i‖≤P'.threshold)→ ‖leftDerivs f' l (actual V)‖ ≤ a)
    (i':Site c) (hi:i'∈neighbors n x) : P'.supBounds i' (neighbors n x) (f' ∘ bake x y hc) (priceP P' (2*M) (n+M) * a):= by
  refine ⟨mul_nonneg (by unfold priceP; positivity) ha,fun U hU l hl hA=> ?_⟩
  have hy: neighbors m' (Zc)⊆ neighbors n x:= by
     intro i hi; apply (neighbors_mem ..).2; apply (separation_triangle x Zc i).trans; exact (Nat.add_le_add (pole x M) ((neighbors_mem ..).1 hi)).trans hr
  have hu := hU.mono_left hy
  obtain ⟨z,W,hW,hF⟩:= hx P' hp c f (by omega) (2*M) hf hc (Zc) U hu
  let V0:= shape ZZ Zc U; let W0:=translate (Y-y) V0; let f5:=f' ∘ translate (Y-y); let Xv := (1+((n+M:ℕ):ℝ))^P'.power; have hT:1 ≤ Xv:= one_le_pow₀ (le_add_of_nonneg_right (by positivity)); have he₀:Xv>0:= zero_lt_one.trans_le hT
  have hℓ: flags P'.threshold V0=∅:= Slide.allFlag ZZ Zc U _ (post1 x hc (by omega)) _ P'.threshold_pos.le hU
  have h₁: Healthy P'.threshold Finset.univ V0:= by unfold Healthy; rw [hℓ]; simp
  have h₂ : Push.Local.Chart P'.order f5 (shape ZZ Zc U):= (translationP _ _ _ hK).smooth V0 h₁
  let t:= Y - y
  let A':= Rotunda.south t W; have hv : Boulevard.actual A'=gauge (fun x=> z (x+t)) W0:= by
    unfold A'; rw [← yanks, hW, walkG]
  have h₂' := he A' (lt_of_le_of_lt (add_le_add (ocean t W) le_rfl) hF) (by rw [hv,gauge_flags]; exact staffed P' x y U hc (by omega) hU); rw [hv] at h₂'
  have hm: ∀ i:List (Directions G f),i.length ≤ P'.order → (∀ v∈i, ‖v‖ ≤ P'.threshold) → ‖leftDerivs f5 i (shape ZZ Zc U)‖ ≤ a:=by
    exact shift_bill P' _ V0 f' h₁ (bills _ hK.symmetry h₂')
  let p:=l.map fun i=> Xv⁻¹ • i
  have hl':p.length=l.length:= List.length_map _
  have hP':l=p.map (fun i=>Xv • i):= by simp [p,List.map_map,Function.comp_def,smul_smul,he₀.ne']
  have hS v (hv:v∈p) : P'.dirBound Zc v := by
     obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hv; apply Rotunda.emits _ _ _ (n:=n+M) ?_ _ (hA j hj); apply (separation_triangle _ x _).trans; rw [separation_comm _ x]; have ht:= Rotunda.pole x M; exact (Nat.add_le_add ht ((neighbors_mem ..).1 hi)).trans_eq (add_comm ..)
  have hz:= Slide.stalled ZZ Zc f5 (compass x hc) p U (hl'.trans_le hl) hS h₂ hm
  change ‖leftDerivs (f5 ∘ shape ZZ Zc) l U‖≤ _
  rw [hP',March.expands,norm_smul,Real.norm_of_nonneg (pow_nonneg he₀.le _),hl']
  refine (mul_le_mul (pow_le_pow_right₀ hT hl) hz (norm_nonneg _) (pow_nonneg he₀.le _)).trans_eq ?_; unfold priceP Xv; rw [← pow_mul]; ring
end Rotunda
end YM.RGComparison01.Pledge
