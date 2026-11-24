import YM.LocalLTE.Motion.Flame
/-! Budget handoff, oxidizing pre+post affines. No receptive assumptions on stencil prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
open Extra.Iteration RG.Shoot
variable {G:Gauge}{c:Side}{p:BudgetPoint}{o:Site c}{X:Support c}
-- basis.Apt ONLY members actual provision.Member if sap + SOME cost. This is subspace. Normalize by fixed lex arbitrary.
section basis
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι:Type*} {φ:Filter ι} {L:E→ₗ[ℝ] (Config G c→ℝ)}
variable (p X o L)
def Fair : Submodule ℝ E := {
    carrier:= {v|p.Regular X (L v) ∧ ∃ C,p.supBounds o X (L v) C}
    zero_mem':=by change p.Regular X _ ∧ _; rw [map_zero]; exact ⟨VerifiedReset.reg_const _,_,VerifiedReset.sup_const _⟩
    smul_mem':=by intro c x h; obtain ⟨hp,b,hb⟩:=h; change p.Regular X _ ∧ _; rw [map_smul]; exact ⟨CouplingShape.reg_scale _ hp,_, CouplingShape.sup_scale _ hb⟩
    add_mem':=by
       intro x y hx hy; obtain ⟨h,C,hx⟩:=hx; obtain ⟨hh,c',hy⟩:= hy; change p.Regular X _∧ _; rw [map_add]; have hg : -L y=(-1:ℝ)• L y :=by simp
       rw [← sub_neg_eq_add, hg]; let u:= CouplingShape.reg_scale (-1) hh; exact ⟨reg_sub h u,_,VerifiedReset.sup_sub h u hx (CouplingShape.sup_scale _ hy)⟩
}
-- Budget span.Work with epsilon strips
variable {p X o L}
omit [FiniteDimensional ℝ E] in
lemma boundFair (P: Finset ι)(f:ι→E)(g:ι→ℝ)(h:∀ i∈P,f i∈ Price.Fair p o X L) (he:∀ i∈P,p.supBounds o X (L (f i)) (g i)): p.supBounds o X (L (∑ i∈P, f i)) (∑ i∈P,g i):=by
   induction P using Finset.induction with
   | empty=>simp only [Finset.sum_empty,map_zero]; exact VerifiedReset.sup_le (VerifiedReset.sup_const 0) abs_zero.le
   | insert i T hT ih=>
      rw [Finset.sum_insert hT,Finset.sum_insert hT,map_add,← sub_neg_eq_add]; have hv j (hj:j∈T):= h j (Finset.mem_insert_of_mem hj); have hp:= ih hv (fun j hj=> he j (Finset.mem_insert_of_mem hj)); let X':= Price.Fair p o X L
      have hz:∑i∈T,f i∈ X':= Submodule.sum_mem _ hv; rw [← neg_one_smul ℝ]; apply VerifiedReset.sup_sub (h i (mem_insert_self ..)|>.1) (CouplingShape.reg_scale _ hz.1) (he i (mem_insert_self ..)); simpa only [abs_neg,abs_one,one_mul] using! CouplingShape.sup_scale (-1) hp
-- approach.Tend difference.
lemma fairC {g: ι→ E} {u:E} (he:Tendsto g φ (𝓝 u))(h:∀ᶠ i in φ,g i∈ Price.Fair p o X L)(hv:u ∈ Price.Fair p o X L)(w:ℝ)(hw:0<w):
    ∀ᶠ i in φ,p.supBounds o X (L u-L (g i)) w:=by
    let Y:= Price.Fair p o X L; let f(i):Y:= if hp:g i∈Y then ⟨g i,hp⟩ else 0; let v:Y:=⟨u,hv⟩
    have hV : Tendsto f φ (𝓝 v):= tendsto_subtype_rng.mpr (he.congr' (h.mono (fun i (hi:g i∈Y)=>by simp only [f,dif_pos hi])))
    let ι':= Fin (Module.finrank ℝ Y); let P:=Module.finBasis ℝ Y
    choose C hC using fun i:ι'=> P i|>.property.2
    let F(v:Y):= ∑ i:ι',|(P.repr v) i| * C i
    have ht: Continuous F:= by
       let g(i:ι'):Y→ₗ[ℝ]ℝ:= P.coord i; have hg (i:ι'):= (g i).continuous_of_finiteDimensional
       exact continuous_finsetSum _ (fun i _=> (hg i|>.abs).mul continuous_const)
    have hh:= ht.continuousAt.tendsto.comp ((tendsto_const_nhds (x:=v)).sub hV)
    have hz:F (v-v)<w:=by simp [F,hw]
    filter_upwards [h, hh.eventually (gt_mem_nhds hz)] with i hi hp
    let u':=v-f i; have he:i∈Set.univ:=trivial
    have hr: u'.val=u-g i:= by change u-(f i).val=u-g i; rw [show g i = _ from (show g i=(f i).val from (by unfold f; rw [dif_pos hi]))] -- edit
    have hy : ∑ i, ((P.repr u') i) • (P i).val=u'.val:= by simpa only [Submodule.coe_sum,SetLike.val_smul] using congr_arg (fun v:Y=>v.val) (P.sum_repr u')
    rw [← map_sub,←hr,← hy]; refine VerifiedReset.sup_le (Price.boundFair Finset.univ _ _ (fun i hi=> Y.smul_mem ((P.repr u') i) (P i).property) (fun i hi=> ?_)) (show F (u') < w from hp).le; rw [map_smul]; exact CouplingShape.sup_scale _ (hC i)
end basis
-- build gaussian lens linear symbol.Color real sym.
open LocalLTE.Cabana
lemma tintC {f:Type*}{φ:Filter f}{Z:Grove o}{κ:ℝ}{i m:ℕ} (P:f→ Pkt (Directions G c) i) (Q:Pkt (Directions G c) i) (h:Tendsto P φ (𝓝 Q)) (hp: ∀ᶠ z in φ,p.Regular X (LocalLTE.FrameBox.realise Z m κ (LocalLTE.FrameBox.colorP (P z))) ∧ ∃ c, p.supBounds o X (LocalLTE.FrameBox.realise Z m κ (LocalLTE.FrameBox.colorP (P z))) c) (hv:p.Regular X (LocalLTE.FrameBox.realise Z m κ (LocalLTE.FrameBox.colorP Q))∧∃ c,p.supBounds o X (LocalLTE.FrameBox.realise Z m κ (LocalLTE.FrameBox.colorP Q)) c)(w:ℝ)(hw:0<w) : ∀ᶠ z in φ,p.supBounds o X (LocalLTE.FrameBox.realise Z m κ (LocalLTE.FrameBox.colorP Q)-LocalLTE.FrameBox.realise Z m κ (LocalLTE.FrameBox.colorP (P z))) w:= by
    let L : Pkt (Directions G c) i →ₗ[ℝ] (Config G c→ℝ):= {
       toFun s:= LocalLTE.FrameBox.realise Z m κ (LocalLTE.FrameBox.colorP s)
       map_add' f g:= by
          funext u; unfold LocalLTE.FrameBox.realise; rw [Pi.add_apply]; simp_rw [LocalLTE.FrameBox.sunwheel]; let w:= Z.crook m Chi.canonical κ u; have ht (P:Pkt (Directions G c) i): MeasureTheory.Integrable (fun v:G.El=>LocalLTE.Cabana.actual P (LocalLTE.FrameBox.wheel v w)) G.probHaar:= ((LocalLTE.Cabana.moves P ω).continuous.comp (LocalLTE.FrameBox.wheel_moves _)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _); rw [LocalLTE.Cabana.actual_add]; exact MeasureTheory.integral_add (ht f) (ht g)
       map_smul' c P:=by funext u; unfold LocalLTE.FrameBox.realise; rw [Pi.smul_apply]; simp_rw [LocalLTE.FrameBox.sunwheel]; rw [LocalLTE.Cabana.actual_smul]; exact MeasureTheory.integral_const_mul .. }
    exact Price.fairC (L:=L) h hp hv w hw
end YM.AnalyticBridge.VerifiedReset.Collection.Price
