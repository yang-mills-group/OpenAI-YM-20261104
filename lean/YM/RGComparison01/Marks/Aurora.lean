import YM.MergeProof.TeamFlow
import YM.RGComparison01.Marks.Stage
import YM.MergeProof.TeamParts
import YM.MergeProof.TeamCells
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Pane

/-!
# Valuation and Receipt for an entire Team

 Generalize the single-Leaf calculation in Lotus.Pane. Windows and tree calls
 use the same expenses, share angular continuation. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lotus
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
namespace Team
variable (M : Team R) (X : Coat T F) (k:Finset ℕ)
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Shield Eider Flux Hues Rotation
open Packets Art Silica Poll Pond
open Blaze Stained March
variable (H:Cash W x μ L Q o C T R) {q A B b e a χ' v d:ℝ}{j n:ℕ}{χ:Chi}
variable {Z : ℕ→Prop} {F' : ℕ→ℝ} {Ξ:Utopia H j v d r q χ}(he : Range Ξ e B A b n) (ht' : Casing R F' Z)
    (hx:X.x=x) (hF:X.χ=χ) (hk:X.width=o.K) (ht:Healthy (Pressure.temp x) (H.unionP p) X.V)(hm: (roster p).flags=∅)
local notation "s" => M.signs S
local notation "P'" => M.whole Ξ n B (maskRaise Ξ Z F' e) p
section
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E][FiniteDimensional ℝ E]{U:E → Config G c} {y:E} (h: Mode U y j v)(hs:U y=X.V)
lemma qlocalFbb_stalk (ha:¬ M.signs S⊆p) : M.album X p W a Ñ m=0:=by
  unfold Team.album Team.aquifer; apply integral_eq_zero_of_ae; filter_upwards with x; split
  next _ => unfold likely Team.common Team.floral; simp_rw [if_neg ha,mul_zero, integral_zero,Finset.sum_const_zero,mul_zero]; rfl
  next => rfl
include he hx hF hk ht hm h hs ht'
lemma qlocalFbb_pistes : Brush j P' 1 (fun z=> M.album (vary X (U z)) p W o.a Q.table Q.halo) y:=by
  apply Brush.shimmy _ (M.qlocalFbb_arc X p H he.unmarked hx hk hF hm ht h hs)
  have hP :0 ≤ P':= M.whole_nn he.paidB (raises _ he.paidE ht'.nonneg) _
  by_cases ha:M.signs S⊆p
  swap; · apply Brush.zi _ hP zero_le_one; filter_upwards [M.qlocalFbb_arc X p H he.unmarked hx hk hF hm ht h hs] with z hz; rw [← hz]; exact M.qlocalFbb_stalk _ ha
  have hR := H.laws.data
  unfold Team.aquifer; simp_rw [show ∀ z: E, (vary X (U z)).B=radiusB x from fun z=> congr_arg radiusB hx]
  split_ifs with hX
  swap; · exact Brush.zi EventuallyEq.rfl hP zero_le_one
  let A' i:=(planted X p).taggedL i; let K:=H.unionP p; let I:=podium S G K (radiusB x); let f i z:= M.common ((preps (vary X (U z)) (roster p)).taggedL i) p W o.a Q.table Q.halo I
  have hY i : Brush j P' 1 (f i) y:=by
    have hv:(A' i).manifest:=planted_valid X p
    have hh:=he.unmarked.flow F (A' i) hx hF hk hv E U y hs h
    have hz:X.B=radiusB x:=congr_arg radiusB hx
    obtain ⟨g,hg,Hf,hQ⟩:= he.stall M F' Z ht' E F (A' i) U y p hF hv hx hk (hx.symm ▸ ht) hX.2 hX.1 ha h hs
    let Z:= A' i; have hℓ:8*o.a*Pressure.fiery G Z.x S.patch.L≤A/2:=by rw [show Z.x=x from hx,hR.funds.length_eq]; exact he.unmarked.mode
    let I':=edgesM S K (radiusB x)
    have H': Cash W Z.x μ L Q o C T R:= (show x=Z.x from hx.symm) ▸ H
    have hK : (edgesM S (H'.unionP p) (Z.B))= I':=by unfold I'; change edgesM S (ground _ T Q.halo X.B p) X.B= _; rw [hz]; rfl
    apply Brush.shimmy ((M.qlocalFbb_boosts Z p H' hk hv I' hh he.unmarked.conduit hℓ|>.1).buds g hg zero_le_one Hf (Filter.Eventually.of_forall hQ))
    filter_upwards [M.qlocalFbb_chutes Z p H' hk hv hh he.unmarked.conduit hℓ] with z hz'
    unfold f; rw [← M.qlocalFbb_casin X p H hx hm ht i (U z) (U z) (fun _ _ _=>rfl), show (podium S G (H.unionP p) (radiusB x))=podium S G (H'.unionP p) Z.B from ?_]
    · rw [hK] at hz'; exact hz'
    change _=podium S G (ground _ T Q.halo X.B p) X.B; rw [hz]; rfl
  let l:ℝ:=Fintype.card S.Choices; have hp:0<l:=by unfold l; positivity
  apply ((Brush.spree _ f _ zero_le_one (fun i (_:i∈univ)=> hY i)).smul l⁻¹).climb _ le_rfl
  rw [sum_const,nsmul_eq_mul,card_univ,Real.norm_of_nonneg (inv_nonneg.mpr hp.le),inv_mul_cancel_left₀ hp.ne']
end
variable (hp:0≤v)
include hx ht' hk hF hm he hp
lemma litmus : M.bloom X W o.a Q.table Q.halo p=masked (Pressure.temp x) (H.unionP p) (fun y=> M.album (vary X y) p W o.a Q.table Q.halo) X.V ∧
    (Healthy (Pressure.temp x) (H.unionP p) X.V→ Ore X.V (fun y=> M.album (vary X y) p W o.a Q.table Q.halo) v P' j):=by
  rw [M.albumd X p H hx hk hm]; constructor
  · by_cases h: Healthy (Pressure.temp x) (H.unionP p) X.V
    · have hx:= (M.qlocalFbb_arc X p H he.unmarked hx hk hF hm h (y:=(0:ℝ)) (show Mode (fun _:ℝ=> X.V) _ j v from ⟨hp,fun i=> a_oneB G _ hp⟩) rfl).self_of_nhds
      rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ h]; exact hx.symm
    rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ h]
  intro h' E _ _ _ U y hy hw; exact M.qlocalFbb_pistes X H he ht' hx hF hk h' hm hw hy
omit hx hk hF

open Greenbelt Next.Foundations
def driver (M:Lotus.Team R) (χ:Chi) (Q:ChartRatio G) (p:Molecule S)(l: ℕ) (T : Tube G S) (W x K a:ℝ) (V:Config G c):=likely fun r:Greenbelt.Reserve S=> M.album (prism T x χ K V (allot r)) p W a Q l
local notation "U'" => fun V=> driver M χ Q.table p Q.halo T W x o.K o.a V
local notation "l₀" => M.lotus T x χ o.K W o.a Q.table Q.halo
include H hm hp
lemma qlocalFbb_debtor : LocalOn (H.unionP p) U' ∧ Measurable U' ∧ GaugeInvariant U' ∧
    (fun V=> M.lotus T x χ o.K W o.a Q.table Q.halo V p)=masked (Pressure.temp x) (H.unionP p) U' ∧
    ∀ Y:Config G c,Healthy (Pressure.temp x) (H.unionP p) Y→ Ore Y U' v P' j:=by
  let X (r:Greenbelt.Reserve S):=prism T x χ o.K 1 (allot r); let f i V:=M.album (vary (X i) V) p W o.a Q.table Q.halo
  have h' i:= M.qlocalFbb_tailSpin (a:=o.a) (X i) p (show Intake P T (X i).x R from H.laws.intake) (show Room P S T (X i).x from H.laws.data.room) (show ShellAccess S G _ _ ((X i).width) o.γ from H.laws.data.access) Q.table_exists Q.buys
  have hf i (V:Config G c): M.bloom (prism T x χ o.K V (allot i)) W o.a Q.table Q.halo p=masked (Pressure.temp x) (H.unionP p) (f i) V∧
      (Healthy (Pressure.temp x) (H.unionP p) V→ Ore V (f i) v  P'  j):= M.litmus (prism _ _ _ _ _ _) H he ht' rfl rfl rfl hm hp
  let c:= (Fintype.card (Greenbelt.Reserve S):ℝ)
  letI : Nonempty (Forest S.ratio) := Tree.select _ S.patch.odd_side
  have hP:0<c:=by unfold c; positivity
  refine ⟨fun U V h=> congr_arg likely (funext fun i=> (h' i).2.1 U V h),measurable_const.mul (Finset.measurable_fun_sum _ (fun i _=> show Measurable (f i) from (h' i).1)), fun t U=> congr_arg likely (funext fun i=>(h' i).2.2 t U),?_, fun V hU E _ _ _ Z x hx hz=>?_⟩
  · funext V; unfold Team.lotus; simp_rw [fun i=> (hf i V).1]; by_cases hv: Healthy (Pressure.temp x) (H.unionP p) V
    · simp_rw [masked_eq _ _ _ _ hv]; rfl
    simp_rw [masked_ne _ _ _ _ hv]; exact Greenbelt.likely_constant _
  apply ((Brush.spree _ (fun i=> f i ∘ Z) _ zero_le_one (fun i (_:i∈univ)=> (hf i V).2 hU _ Z x hx hz)).smul c⁻¹).climb _ le_rfl
  rw [Real.norm_of_nonneg (inv_nonneg.mpr hP.le),sum_const,nsmul_eq_mul,card_univ, inv_mul_cancel_left₀ (show c≠0 from hP.ne')]


end Team
end YM.PhysicalNext.Repeat.Lotus
