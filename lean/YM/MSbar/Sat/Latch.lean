import YM.MSbar.Sat.World
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{c f:Side}{S:StepData c f} {U W:Config G f}{V:Config G c}{R:Rep G f}{σ C T a v y δ w D b u t:ℝ}
open Finset YM.MSbar.Bulk SectorNext.Vacuum Precision Tree Pressure Pressure.Stores Push.Uniform
variable (F : Forest S.ratio) {Y X:Support f}(J: Voice G) (V:Config G c)
local notation "N"=> Config G f
def board (Y: Support f):= univ.filter (fun i: F.Free=>i.val.1∈Y)
def flume (U:N)(i:F.Free):= canoe (S:=S) F U i.val * (Precision.replica S.ratio V i.val)⁻¹
def fareX (U:N)(i:F.Free):= J.decode (flume F V U i)
def chink (U:N) (Y:Support f) : Positions (Key F G) := (tint G _).symm (fun i:F.Free=> if i∈board F Y then fareX F J V U i else 0)
def exterior (U:N)(Y: Support f): Config G f:=lifting F V (tint G _ (chink F J V U Y))
lemma boardC (Y : Support f) : (board F Y).card ≤ Y.card*4:= le_trans (Finset.card_le_card_of_injOn (t:=Y×ˢ(Finset.univ:Finset Axis)) (fun i:F.Free=> i.val) (fun i (hi:i∈board F Y)=>Finset.mem_product.mpr ⟨(mem_filter.mp hi).2,mem_univ _⟩) (Subtype.val_injective.injOn)) (by simp [Axis])
variable (s: F.Slice G)
lemma winding (h:∀ i:F.Free,s i≠1→ i.val.1∈Y) (Z:Support f)(U:N) : Spine Y (canoe (S:=S) F U) (canoe (S:=S) F (pedal F s U)) ∧ Spine Y (exterior F J V U Z) (exterior F J V (pedal F s U) Z) := by
   have hh i (hi:i.1∉Y): canoe (S:=S) F U i=canoe (S:=S) F (pedal F s U) i := by
       by_cases he:i∈ F.trunks; exact (F.compress U i he).trans (F.compress _ i he).symm
       let j:F.Free:=⟨i,he⟩; rw [show canoe (S:=S) F _ i=_ from stationary F s U j,show s j=1 from by_contra (fun hg=> hi (h j hg)),one_mul]
   refine ⟨spine_in hh,spine_in (fun i ht=> ?_)⟩
   unfold exterior lifting; by_cases hv:i∈F.trunks
   · exact (F.on_tree _ ⟨i,hv⟩).trans (F.on_tree _ ⟨i,hv⟩).symm
   let j:F.Free:=⟨i,hv⟩; change F.drape _ j.val= F.drape _ j.val; simp_rw [F.off_tree, chink,ContinuousLinearEquiv.apply_symm_apply]; have ht : fareX F J V U j=fareX F J V (pedal F s U) j:=by unfold fareX flume; rw [hh _ ht]
   rw [ht]
variable (hv:V∈calm G c v)(hv':0<v)(hC:Clear G J)
def pays (b:ℝ)(Y:Support f)(U:N):Prop:= ∀ i∈board F Y, G.chord (flume F V U i)≤ b
include hv hv'
lemma clears (U: N) (h: U∈excavation F Y t b): pays F V (b+v/4) Y U:=by
    intro i hi; let u := Precision.replica S.ratio V i.val
    have ht:G.chord u ≤v/4:=by unfold u Precision.replica;split; rw [G.chord_one]; positivity; exact hv _ (Set.mem_univ _)
    unfold flume; exact (G.chord_triangle ..).trans (add_le_add (h.2 i ((mem_filter.mp hi).2)) ((G.chord_inv ..).trans_le ht))
omit hv hv'
lemma dune (U : N) (hU: pays F V b Y U) (t : F.Free→ G.Color)(hf: ∀ i,G.chord (G.lieExp (t i)) ≤ a): pays F V (a+b) Y (pedal F (G.lieExp ∘ t) U):=by
   intro i hi; unfold flume; rw [stationary,mul_assoc]; exact (G.chord_triangle ..).trans (add_le_add (hf _) (hU i hi))
include hC
lemma apt (Y:Support f)(V₀:N)(hy:pays F V b Y V₀)(hb:b ≤ J.δ): Agrees Y (canoe (S:=S) F V₀) (exterior F J V V₀ Y) :=by
    intro e he hp; unfold exterior lifting; by_cases hh:e∈F.trunks; exact (F.compress _ e hh).trans (F.on_tree _ ⟨e,hh⟩).symm
    let i:F.Free:=⟨e,hh⟩; have h : i∈ board F Y:= mem_filter.mpr ⟨mem_univ _,he⟩
    change _=F.drape _ i.val; simp_rw [F.off_tree,chink,ContinuousLinearEquiv.apply_symm_apply,if_pos h]; rw [fareX, (hC.near _ ((hy i h).trans hb)).2.1]; unfold flume; simp [i]
lemma sizing (Y:Support f)(U:N)(hy: pays F V b Y U)(hb:b ≤ J.δ)(hx:0≤ b): ‖chink F J V U Y‖ ≤ J.C*b := by
   let f(i:F.Free):= if i∈board F Y then fareX F J V U i else 0; apply (tint_inv_le (G:=G) f).trans; refine (pi_norm_le_iff_of_nonneg (show 0 ≤ J.C*b from mul_nonneg (zero_le_one.trans hC.cost) hx)).mpr fun i=> ?_
   unfold f; split
   next hp => exact ((hC.near _ ((hy i hp).trans hb)).2.2).trans (mul_le_mul_of_nonneg_left (hy i hp) (zero_le_one.trans hC.cost))
   rw [norm_zero]; exact mul_nonneg (zero_le_one.trans hC.cost) hx
-- supported events keep near & masks
lemma seals (p : F.Free)(i:G.ColorIndex) {μ γ h₀:ℝ}(hx:p∈board F Y) : Seal S (youth F Y) {U:N | γ < h₀*(fareX F J V U p i-μ)}:=by
   have hf : Continuous (fun U:N=> flume F V U p):=Continuous.mul ((continuous_apply p.val).comp (canoe_cont F)) continuous_const
   refine ⟨measurableSet_lt measurable_const (measurable_const.mul ((((show Continuous (fun x:G.Color=> x i) from (EuclideanSpace.proj (𝕜:=ℝ) i).continuous).measurable.comp (hC.reads.comp hf.measurable)).sub measurable_const))),fun g ht W=>?_,fun A B h=>?_⟩
   · have h:F=F:=rfl; simp only [fareX,flume,Set.mem_setOf_eq,grove F _ _ ht]
   simp only [Set.mem_setOf_eq, fareX,flume, turnbook F h p.val ((mem_filter.mp hx).2)]
-- orientation relation during shift local cost earned
lemma hears {R u b:ℝ}(hu: pays F V b Y U)(hx:b≤J.δ)(hδ:J.C*b ≤ R) (p : F.Free → G.Color) (hr:R ≤ J.r)(hh:∀ i∈ board F Y,‖p i‖≤ u)(hU:u≤R) (i:F.Free)(hi:i∈board F Y):
   ‖fareX F J V (pedal F (G.lieExp ∘ p) U) i -p i -fareX F J V U i‖ ≤ J.C*R*‖p i‖ :=by
    let X:= fareX F J V U i; have hw:= hC.near (flume F V U i) ((hu i hi).trans hx)
    have hT: ‖X‖ ≤ R := hw.2.2.trans ((mul_le_mul_of_nonneg_left (hu i hi) (zero_le_one.trans hC.cost)).trans hδ)
    change ‖_-(p i)-X‖≤ _; rw [fareX, show flume F V (pedal _ _ _) i=(G.lieExp (p i))*G.lieExp X from ?_]; exact hC.turns _ _ R hr ((hh i hi).trans hU) hT
    unfold X fareX; rw [hw.2.1]; unfold flume; rw [stationary,mul_assoc];rfl
end YM.MSbar.Heath
