import YM.LocalLTE.Marked.Pane
import YM.LocalLTE.Marked.Strength
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Pint
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Team R)(X:Coat T F)(H:Cash W x μ L Q o C T R) (a' : ℝ) (u:ConnectedActivityE6.Alphabet c f→ℝ)
    {q A B b e a χ' v d:ℝ}{j n:ℕ}{χ:Chi} (Ξ : Utopia H j v d r q χ)
open Itinerary Animals
open Stained March
variable {Ξ:Utopia H j v d r q χ}(he : HostQ H Ξ A B n)
    (Θ:Oboe H j v B n A b Ξ) (hx:X.x=x) (hF:X.χ=χ) (hk:X.width=o.K) (ht:Healthy (Pressure.temp x) (H.unionP p) X.V)(hm: (roster p).flags=∅)
section
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E][FiniteDimensional ℝ E]{U:E→ Config G c} {y:E} (h: Mode U y j v)(hs:U y=X.V) (hB:0≤B)

local notation "P" => B*(M.weight*(∏i∈p\ M.signs S, Ξ.tag i)*Ξ.rad^(blaze p).card*(1+H.shapeW p)^n)
omit Θ he hx hF hk ht hm in
lemma stalkQ (ha:¬M.signs S⊆p) : M.qlocal4a_picture X p W a Ñ m=0:=by
  unfold Team.qlocal4a_picture Team.qlocal4a_grove; apply integral_eq_zero_of_ae; filter_upwards with x; split
  next _ => unfold likely Team.qlocal4a_cinema Team.qlocal4a_floret; simp_rw [if_neg ha,mul_zero, integral_zero,Finset.sum_const_zero,mul_zero]; rfl
  next => rfl
include Θ he hx hF hk ht hm h hs hB
lemma pistesQ : Brush j P 1 (fun z=> M.qlocal4a_picture (vary X (U z)) p W o.a Q.table Q.halo) y:=by
  apply Brush.shimmy _ (M.qlocal4a_arc X p H Θ hx hk hF hm ht h hs)
  have hP:0≤P:= mul_nonneg hB (mul_nonneg (mul_nonneg (mul_nonneg M.profit (prod_nonneg fun _ _=>Ξ.tagged _)) (pow_nonneg Ξ.awake _)) (pow_nonneg (add_nonneg zero_le_one (H.positive_volume p)) _))
  by_cases ha:M.signs S⊆p
  swap
  · apply Brush.zi _ hP zero_le_one; filter_upwards [M.qlocal4a_arc X p H Θ hx hk hF hm ht h hs] with z hz; rw [← hz]; exact stalkQ M _ ha
  have hR:= H.laws.data
  unfold Team.qlocal4a_grove; simp_rw [show ∀ z: E, (vary X (U z)).B=radiusB x from fun z=> congr_arg radiusB hx]
  split_ifs with hX
  swap; · exact Brush.zi EventuallyEq.rfl hP zero_le_one
  let A' i:=(planted X p).taggedL i; let K:=H.unionP p; let I:=podium S G K (radiusB x); let f i z:= M.qlocal4a_cinema ((preps (vary X (U z)) (roster p)).taggedL i) p W o.a Q.table Q.halo I
  have hY i : Brush j P 1 (f i) y:=by
    have hv:(A' i).manifest:=planted_valid X p
    have hh:=Θ.flow F (A' i) hx hF hk hv E U y hs h
    have hz:X.B=radiusB x:=congr_arg radiusB hx
    obtain ⟨g,hg,Hf,hQ⟩:= he.nil M E F (A' i) U y p hF hv hx hk (hx.symm ▸ ht) hX.2 hX.1 ha h hs
    let Z:= A' i; have hℓ:8*o.a*Pressure.fiery G Z.x S.patch.L≤A/2:=by rw [show Z.x=x from hx,hR.funds.length_eq]; exact Θ.mode
    let I':=edgesM S K (radiusB x)
    have H': Cash W Z.x μ L Q o C T R:= (show x=Z.x from hx.symm) ▸ H
    have hK : (edgesM S (H'.unionP p) (Z.B))= I':=by unfold I'; change edgesM S (ground _ T Q.halo X.B p) X.B= _; rw [hz]; rfl
    apply Brush.shimmy ((M.qlocal4a_boosts Z p H' hk hv I' hh Θ.conduit hℓ|>.1).buds g hg zero_le_one Hf (Filter.Eventually.of_forall hQ))
    filter_upwards [M.qlocal4a_chutes Z p H' hk hv hh Θ.conduit hℓ] with z hz'
    unfold f; rw [← M.qlocal4a_casin X p H hx hm ht i (U z) (U z) (fun _ _ _=>rfl), show (podium S G (H.unionP p) (radiusB x))=podium S G (H'.unionP p) Z.B from ?_]
    · rw [hK] at hz'; exact hz'
    change _=podium S G (ground _ T Q.halo X.B p) X.B; rw [hz]; rfl
  let l:ℝ:=Fintype.card S.Choices; have hp:0<l:=by unfold l; positivity
  apply ((Brush.spree _ f _ zero_le_one (fun i (_:i∈univ)=> hY i)).smul l⁻¹).climb _ le_rfl
  rw [sum_const,nsmul_eq_mul,card_univ,Real.norm_of_nonneg (inv_nonneg.mpr hp.le),inv_mul_cancel_left₀ hp.ne']
end
section
variable {Y C':ℝ}{H:Cash W x μ L Q o C T R}(N: Captain H j q d v Y A b r B C' n χ)
    (hh:HostQ H N.conduit A B n) (hX:X.x=x)(hZ:X.width=o.K)(hf:X.χ=χ)(hp:(roster p).flags=∅)
local notation "VP" => B*(M.weight*(∏i∈p\ M.signs S, N.conduit.tag i)*N.conduit.rad^(blaze p).card*(1+H.shapeW p)^n)
include hX hZ hf hp hh N
lemma luminosQ : M.bloom X W o.a Q.table Q.halo p=masked (Pressure.temp x) (H.unionP p) (fun y=> M.qlocal4a_picture (vary X y) p W o.a Q.table Q.halo) X.V ∧
    (Healthy (Pressure.temp x) (H.unionP p) X.V→ Ore X.V (fun y=> M.qlocal4a_picture (vary X y) p W o.a Q.table Q.halo) v VP j):=by
  rw [M.qlocal4a_pictured X p H hX hZ hp]; constructor
  · by_cases h: Healthy (Pressure.temp x) (H.unionP p) X.V
    · have hx:= (M.qlocal4a_arc X p H N.oboe hX hZ hf hp h (y:=(0:ℝ)) (show Mode (fun _:ℝ=> X.V) _ j v from ⟨N.position.le,fun i=> a_oneB G _ N.position.le⟩) rfl).self_of_nhds
      rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ h]; exact hx.symm
    rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ h]
  intro h E _ _ _ U y hy hw; exact pistesQ M X H hh N.oboe hX hf hZ h hp hw hy N.balance
end
end YM.PhysicalNext.Repeat.Daisy
