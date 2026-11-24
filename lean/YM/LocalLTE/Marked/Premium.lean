import YM.LocalLTE.Marked.Pints
import YM.LocalLTE.Marked.Destiny
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cadre.Toll


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
variable (V:Config G c) (R': Merge.Tickets (Merge.Palette.sign M S))(i:H.ThinP)
local notation "M'"=> team M R'
def waltz (H:Cash W s μ L Q o C T R)(χ:Chi) (M:ι→Lotus.Leaf R)(i:H.ThinP) (R':Tickets (Merge.Palette.sign M S)) (U: Config G c):= likely fun r: Greenbelt.Reserve S=> (team M R').qlocal4a_picture (prism T s χ o.K U (allot r)) i.val W o.a Q.table Q.halo
local notation "g" => waltz H χ M i R'
def inlet (z:Molecule S)(R':Tickets (Merge.Palette.sign M S)) : ℝ:=
   if H.ticketsP 0 0 0 z∧ R'.reach ⊆ z then B*((team M R').weight * (∏ i∈z\R'.reach,N.conduit.fare i)*(1+H.shapeW z)^k) else 0
local notation "c₀"=>inlet N M i.val R'
include N
variable (h':Daisy.HostQ H N.conduit A B k)
omit [Fintype ι] in
lemma inlet_nn (i:Molecule S):0≤ inlet N M i R':=by
   unfold Captain.inlet; have ht : 0 ≤ (M').weight:=Team.profit _; have hh:= H.positive_volume i; have he:= N.balance; have hP:0≤ ∏ j∈i\R'.reach,N.conduit.fare j:=prod_nonneg fun _ _=> N.conduit.fares _
   split_ifs <;> positivity
include h'
omit [Fintype ι] in
lemma vivid : act M H χ V i.val R'= RG.masked (Pressure.temp s) (H.smallAt i) (waltz H χ M i R') V ∧ LocalOn (H.smallAt i) g∧GaugeInvariant g ∧Measurable g ∧(Healthy (Pressure.temp s) (H.smallAt i) V →Ore V (waltz H χ M i R') v c₀ j):=by
  let W':=team M R'; let X(z:Greenbelt.Reserve S):= prism T s χ o.K 1 (allot z); let f z V:= W'.qlocal4a_picture (vary (X z) V) i.val W o.a Q.table Q.halo
  have hs z V:= Daisy.luminosQ W' (vary (X z) V) N h' rfl rfl rfl i.2.2
  letI:Nonempty (Tree.Forest S.ratio):=Tree.select S.ratio S.patch.odd_side
  have hP (z) : W'.bloom (vary (X z) V) W o.a Q.table Q.halo i.val= masked (Pressure.temp s) (H.smallAt i) (f z) V:= (hs z V).1
  have hv(z): LocalOn (H.smallAt i) (f z) ∧ GaugeInvariant (f z) ∧ Measurable (f z):=by
     obtain ⟨hx,hF,hT⟩:= W'.qlocal4a_tailSpin (a:=o.a) (X z) (i.val) H.laws.intake H.laws.data.room H.laws.data.access Q.table_exists Q.buys
     exact ⟨hF,hT,hx⟩
  let K:=H.smallAt i
  refine ⟨?_,fun U V hu=>congr_arg likely (funext fun j=> (hv j|>.1 U V hu)),fun k U=>congr_arg likely (funext fun j=>(hv j|>.2.1 k U)),measurable_const.mul (Finset.measurable_fun_sum _ fun i _=>(hv i).2.2),?_⟩
  · change likely (fun j=> W'.bloom (vary (X j) V) W o.a Q.table Q.halo i.val)=_
    simp_rw [hP]; by_cases h:Healthy (Pressure.temp s) K V
    · exact (congr_arg likely (funext fun i=>masked_eq _ _ (f i) V h)).trans (masked_eq _ _ g V h).symm
    exact (congr_arg likely (funext fun i=>masked_ne _ _ (f i) V h)).trans ((likely_constant (A:=Greenbelt.Reserve S) _).trans (masked_ne _ _ _ _ h).symm)
  · intro hv E _ _ _ U u ht hS
    unfold Function.comp waltz; apply avgBrush (V:=fun z x=> f z (U x)); intro z
    by_cases hF: H.ticketsP 0 0 0 i.val ∧ R'.reach ⊆ i.val
    · have hc (p:Molecule S): blaze (p\(team M R'|>.signs S))=blaze p := by
         ext j; simp only [blaze,mem_toRight]; rw [Finset.mem_sdiff]; constructor; · exact And.left
         intro h; refine ⟨h,?_⟩; intro hx; obtain ⟨i,hk,hv⟩:= mem_image.mp hx; cases he:i.turn <;> simp [he,Wing.badge] at hv
      have hx' : blaze (i.val\R'.reach)= blaze i.val:=by rw [← label M R']; exact hc _
      have hP:= (hs z (U u)).2 ((show U u=V from ht).symm ▸ hv : Healthy (Pressure.temp s) _ _)
      unfold inlet; rw [if_pos hF, N.conduit.remixes,hx',← label M R']
      -- C=head.Magnet
      rw [← mul_assoc (team M R').weight]; exact hP E U u rfl hS
    · apply Brush.zi _ (inlet_nn N M R' _) zero_le_one
      filter_upwards with x; by_cases h: R'.reach ⊆ i.val
      · let X':=vary (X z) (U x); have he (q: Site c→ G.El): (W').qlocal4a_grove (X'.rinse q) i.val W o.a Q.table Q.halo=0:= if_neg (fun he=>hF ⟨(H.attends _).2 he.1,h⟩)
        change (W').qlocal4a_picture X' i.val W o.a Q.table Q.halo=0
        unfold Team.qlocal4a_picture; simp_rw [he,integral_zero]
      exact Daisy.stalkQ _ _ (fun he=> h (Merge.Palette.label M R' ▸ he))
-- Total BILL on REAL products. weight multiplier.Angles due. Anchor arbitrary.
include he
omit he h' in
lemma points (i: H.ThinP): (∑ t:Merge.Tickets (Merge.Palette.sign M S), (∏ j∈t.val,rA j)* inlet N M i.val t)= B*bought N M rA i.val:=by
   unfold Height.bought; split
   next h =>
      unfold chatter; rw [Tickets.expanded, Finset.sum_mul, Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _
      unfold inlet; by_cases hv:l.reach ⊆ i.val
      · rw [if_pos ⟨h,hv⟩,if_pos hv, Palette.worth M]; unfold Palette.wages; rw [prod_mul_distrib]; ring
      rw [if_neg hv,if_neg (fun he=>hv he.2)]; ring
   next h =>
      rw [mul_zero]; refine sum_eq_zero fun i _=>?_ ; unfold inlet; rw [if_neg (fun he=>h he.1),mul_zero]
end Captain
end YM.ConnectedActivityE6.Blaze.March
