import YM.LocalLTE.Marked.Flint
import YM.LocalLTE.Marked.Interior
import YM.LocalLTE.Marked.Post
/-! # Regular script for second unforced log. Keeps repeats. No Hessian subtraction yet!

Anchor on UNION site; pays factor exp surplus at endpoint, doesn't move
 each genealogy to fresh center. Keep honest clustered labels.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.March
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained Gas Ursell
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {I : Finset (Tubular f G)} {η r q a Y W d C' A b s μ C v B: ℝ} {Ñ : ChartRatio G}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R} {Ξ : Utopia H j v d r C' χ}
open Next.Foundations

open PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt

namespace Captain
variable (N : Captain H j C' d v Y A b r B q k χ)
variable (p : Clusters H.ThinP)
open Greenbelt


open Merge Merge.Palette Height Daisy Lotus
-- every factor still selected independently.R.indices attached later. purposes geometry active.Down.
variable {ι:Type}[Fintype ι] (M:ι→Lotus.Leaf R)(rA:ι→ℝ)(he:∀ i, 0≤rA i)
set_option quotPrecheck false
local notation "χz"=> Merge.Palette.sign M S
local notation "τ"=> Merge.Tickets (Merge.Palette.sign M S)

-- bet costs on multiselects and draw routes. Prove zero off.R.
-- TERR Bayesian.


-- interior charge criteria.
variable (D:Oscars M p)
open LocalLTE.Fan Pastel YM.PhysicalNext.Repeat
local notation "d'"=> East.docket H p
noncomputable def quietR (l:H.ThinP)(u: Tickets χz):= East.lining S (l.val\u.reach)
local notation "r!"=> (fun i=> quietR M (p.2 i) (D i))
omit [Fintype ι] in
lemma arduous (j:ℕ) (w: Molecule S) (i : Tickets χz)(hp:elastic (Sum.inl j)∈ w\(i.reach))(hR : R.activities.E j=0) (X:Coat T F) (p:ℕ): (team M i).qlocal4a_picture X w W a Ñ p=0:=by
    let Q:=team M i
    have ht(U: Config G f): R.activities.regularOccurrence R.p j U=0:=by unfold Activities.regularOccurrence; by_cases h:Healthy R.p.threshold (R.activities.reg j).support U; rw [masked_eq _ _ _ _ h,hR];rfl; exact masked_ne _ _ _ _ h -- edit syntax
    have hu (X:Coat T F)(z):Q.qlocal4a_floret X w W a Ñ (own w) p z=0:=by
       unfold Team.qlocal4a_floret; split; swap; · rfl
       apply mul_eq_zero_of_right
       let y:= worldZ X R.beta z
       apply Finset.prod_eq_zero (i:= elastic (Sum.inl j)); swap
       · change Real.exp (-R.activities.regularOccurrence R.p j (X.input y)*_)-1=0
         rw [ht,neg_zero,zero_mul,Real.exp_zero,sub_self]
       rw [Palette.label M i]; exact hp
    have hF (X:Coat T F): Q.qlocal4a_grove X w W a Ñ p=0:=by
       unfold Team.qlocal4a_grove; split; swap; · rfl
       unfold likely Team.qlocal4a_cinema; simp_rw [hu,mul_zero,integral_zero,sum_const_zero,mul_zero]
    change Q.qlocal4a_picture _ _ _ _ _ _=_; unfold Team.qlocal4a_picture; simp_rw [hF,integral_zero]
omit [Fintype ι] in
lemma silenced (l:H.ThinP) (D:Tickets χz) (U:Config G c)(hn: waltz H χ M l D U ≠ 0): Ac.Spark H.supportP l.val ∧ troupe T R Q.halo (radiusB s) l.val ∧ D.reach ⊆ l.val ∧ ∀ (i:ℕ), Sum.inl i∈ quietR M l D→ R.activities.E i ≠ 0:=by
    let W':=team M D; let X i:=prism T s χ o.K U (Greenbelt.allot (S:=S) i); let u j:=W'.qlocal4a_picture (X j) l.val W o.a Q.table Q.halo
    obtain ⟨v,h⟩:∃ i: Greenbelt.Reserve S,u i ≠ 0:=by by_contra! hv; exact hn (by unfold waltz; change _*(∑ i,u i)=_; simp_rw [hv,sum_const_zero,mul_zero])
    let g(y:Site c→G.El):= W'.qlocal4a_grove ((X v).rinse y) l.val W o.a Q.table Q.halo
    have hh: Ac.Spark H.supportP l.val ∧ troupe T R Q.halo (radiusB s) l.val:=by by_contra hh; have he (p: Site c→G.El):g p=0:= if_neg hh; exact h (by unfold u; unfold Team.qlocal4a_picture; change (∫ i,g i ∂_)=_;simp_rw [he,integral_zero])
    refine ⟨hh.1,hh.2,?_ ,fun i hi hI=>?_⟩
    · by_contra hh; rw [← Palette.label M D] at hh; exact h (stalkQ W' _ hh)
    exact h (arduous M _ _ D ((show (Sum.inl i∈ quietR M l D)↔ LocalLTE.Fan.elastic (Sum.inl i)∈ l.val\D.reach from Finset.mem_preimage (hf:=LocalLTE.Fan.runOut (S:=S)|>.injOn)).mp hi) hI (X v) Q.halo)
-- packing: Core analytic admission under address judgments. If not symbolic admission but function NONZERO (even checked as all-domain heuristic), then some momentum-bearing input pays.
structure Candor (M:ι→Lotus.Leaf R) (p:H.fragrances)(u:Oscars M p) (n K:ℕ)(h:ℕ→ℕ)(X:ι→Prop) : Prop where
   can: East.Orchestra H p n
   lives j: (u j).reach ⊆ (p.2 j).val
   petals j i : i∈ (u j).val → X i
   loans (i:ℕ)(j): Sum.inl i ∈ quietR M (p.2 j) (u j) → h i ≤ K
-- show orientation facts.
local notation "bΛ"=> radiusB s
variable (n K:ℕ) (tag:ℕ→ℕ) (ξ:ι→Prop)
variable (hL:∀ i, tag i≤K→ R.activities.E i≠0→ (R.activities.reg i).support ⊆ Animals.neighbors (S.patch.L.val*radiusB s) (R.activities.reg i).site)
    (hT:∀ i,ξ i →∀ j,(M i).turn= Wing.logKey j→ (R.activities.reg j).support⊆Animals.neighbors (S.patch.L.val*radiusB s) (R.activities.reg j).site)
include H hL hT
-- Stella.Quorum funding.T pulse nonempty.Ash.
omit [Fintype ι] in
lemma canopy (U:Config G c)(hx: wingTerm (χ:=χ) p M D U ≠ 0)(hv:¬tiredN H n p)(hg:∃ i,(D i).val.Nonempty)(h:∀ j i,i∈(D j).val→ξ i)(hF:∀ j k, Sum.inl k∈ quietR M (p.2 j) (D j)→tag k ≤ K): Candor M p D n K tag ξ:=by
    let Z i:=waltz H χ M (p.2 i) (D i)
    have hp i:Z i U≠0:=fun h=>hx (by unfold wingTerm; rw [prod_eq_zero (i:=i) (mem_univ i) (by exact h),mul_zero,zero_div])
    have he i:= silenced M (p.2 i) (D i) U (hp i); have ht := Height.aged (H:=H) (fun i=> ⟨(he i).1,(he i).2.1⟩) hv
    refine ⟨East.arisesQ H p hv (fun hi=> hx (by unfold wingTerm; rw [hi,zero_mul,zero_div])) (fun i=>⟨(he i).1,(he i).2.1⟩) ?_ (fun i=> ?_),fun i=>(he i).2.2.1,h, fun i j hp=> hF j i hp⟩
    · obtain ⟨i,j,hp⟩:= hg
      have h': Palette.sign M S j∈ (p.2 i).val:=(he i).2.2.1 ((D i).reaches_of hp)
      cases hk:(M j).turn with
       | logKey k=>rw [Palette.sign,hk] at h'; exact ⟨i,k,h'⟩
       | gasKey k=>rw [Palette.sign,hk] at h'; have hv:k∈Matter.own (p.2 i).val:=mem_toLeft.mpr (mem_toRight.mpr h'); rw [(ht.1 i).noK] at hv; exact (notMem_empty _ hv).elim
    intro j hj
    by_cases hh: elastic (S:=S) (Sum.inl j) ∈ (D i).reach
    · obtain ⟨v,hp,hv⟩:= Finset.mem_image.mp hh
      have hv:(M v).turn= Wing.logKey j:= Team.badged S hv
      exact hT v (h _ _ hp) j hv
    have hp: Sum.inl j∈ quietR M (p.2 i) (D i):= (Finset.mem_preimage (hf:=LocalLTE.Fan.runOut (S:=S)|>.injOn)).2 (Finset.mem_sdiff.mpr ⟨((show Sum.inl j∈ East.docket H p i ↔ LocalLTE.Fan.elastic (Sum.inl j)∈ (p.2 i).val from Finset.mem_preimage (hf:=LocalLTE.Fan.runOut (S:=S)|>.injOn)).1 hj),hh⟩)
    exact hL j (hF _ j hp) ((he i).2.2.2 j hp)
end Captain
end YM.ConnectedActivityE6.Blaze.March
