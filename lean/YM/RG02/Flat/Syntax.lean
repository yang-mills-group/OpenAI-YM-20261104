import YM.RG02.Flat.Ion

/-!
# One-step full formal recursion, incoming charts

Numbers computed solely from the prescribed primitives (on this regulator;
cover tails not estimated here), unmasked germs and explicit Wick rule. Not
the iterates of `History.rep`, nor a calibration-derived comparator slope.
Use with incoming g until budget of reset is paid. Signs explicitly as in
`script` and `ion`. Tag independence below is indivisible for repeats.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Fk
open Filter Function MeasureTheory Lattice Wilson RG Precision Tree Supply Bid Marker Extra.Trajectories
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Therm Asym Tangent Grade PowerSeries
open scoped ContDiff Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}{I : Type}[DecidableEq I][Fintype I]{B : Census I}{c f : Side}{S : StepData c f}

namespace Draw
variable (T : Forest S.ratio) {p : Clip}{R : PathData G}{A : Space G f→ℝ}{m : ℕ}{W : Space G f→ Poly B}
    {η : ChartRatio G}

/-- Coupling order before reset; relative charts. Arguments `T.ρ`
by Kin or other verified same-bed stationary solution. -/
def pre (t : S.Choices)(η : ChartRatio G)(p : Clip)(R : PathData G)(x : Dir G c)(A : Space G f→ℝ)
    (m : ℕ)(W : Space G f→ Poly B)(ρ : Dir G c→AxisChart G T) :=
   Therm.board (track T t η p R x A) m (Pins.ink T x W) (crest T ρ x)

omit [Fintype I] in
lemma ready (i : S.Choices)(x : Dir G c)(ρ : Dir G c→AxisChart G T) {p R η A m}{W : Space G f→Poly B}(G : Ink m W) :
    Wick.Edged (pre T i η p R x A m W ρ) ∧ ∀ u,basepoint (pre T i η p R x A m W ρ u)=0 :=
    ⟨board_ready _ _ _ _,fun _=> board_quiet _ (Pins.jobs _ _ G) ..⟩

omit [Fintype I] in
lemma pre_tag_const (i t : S.Choices)(x : Dir G c)(ρ : Dir G c→AxisChart G T)
    (h : S.patch.Branches S.kernel G)(m : ℕ)(η:ChartRatio G)(p:Clip)(R:PathData G)(A)(W:Space G f→Poly B) :
    pre T t η p R x A m W ρ = pre T i η p R x A m W ρ := by
   have hu := Work.F04.tested_germ h T p R t i
   have hv : ray T t p R x =ᶠ[𝓝 0] ray T i p R x := hu.comp_tendsto (show Tendsto (shift T x) (𝓝 0) (𝓝 0) by simpa only [map_zero] using (shift T x).continuous.tendsto 0)
   let X := track T t η p R x A
   let Y := track T i η p R x A
   have he : X =ᶠ[𝓝 0] Y := by rw [show X=_ from enact .., show Y=_ from enact ..]; exact (hv.add (EventuallyEq.refl ..)).add (EventuallyEq.refl ..)
   have hz (u) : driven X u= driven Y u := by
      ext1 i; simp only [driven,PowerSeries.coeff_mk,Radial.layers,Radial.jet]; rw [(he.iteratedFDeriv ℝ (i+2)).self_of_nhds,(he.iteratedFDeriv ℝ 2).self_of_nhds]
   funext v; unfold pre Therm.board; rw [hz]

variable {w : ℝ}{ρ : Dir G c → AxisChart G T}(i : S.Choices)(hp : 0<w)(hr:PriceGap T p R w)(h : Critical T p R ρ)

def formal (η : ChartRatio G)(x : Dir G c)(A : Space G f→ℝ)(m : ℕ)(W : Space G f→ Poly B) :=
   Wick.made (Γ i hp hr h) fun u=> Grade.exponential (pre T i η p R x A m W ρ u)

def multiplier (η : ChartRatio G)(x : Dir G c) := weight T η * Therm.leading (Γ i hp hr h) (Chart.tangent G T.Free)
   (due T i p R x (crest T ρ x))
include h
lemma multiplier_pos (η : ChartRatio G)(x : Dir G c)(hv : LocalRatio η) : 0< multiplier T i hp hr h η x :=
   mul_pos (pow_pos hv.scale _) (Therm.leading_pos (Chart.tangent G T.Free) (Γ i hp hr h) _)

lemma multiplier_constant (t : S.Choices)(hs : S.patch.Branches S.kernel G) :
    multiplier T t hp hr h η = multiplier T i hp hr h η := by
   funext x
   have hu := Work.F04.tested_germ hs T p R t i
   have hv : ray T t p R x =ᶠ[𝓝 0] ray T i p R x := hu.comp_tendsto (show Tendsto (shift T x) (𝓝 0) (𝓝 0) by simpa only [map_zero] using (shift T x).continuous.tendsto 0)
   unfold multiplier; rw [tag_constant i hp hr h hs t]; simp only [due, Radial.jet,(hv.iteratedFDeriv ℝ 2).self_of_nhds]

lemma formal_constant (t : S.Choices)(η)(x : Dir G c)(hs : S.patch.Branches S.kernel G) :
    formal T t hp hr h η x A m W=formal T i hp hr h η x A m W := by
   unfold formal; rw [tag_constant i hp hr h hs t,pre_tag_const T i t x ρ hs]

lemma configured (η)(x : Dir G c)(G' : Ink m W) : basepoint (formal T i hp hr h η x A m W) = 1 := by
   obtain ⟨_,ht⟩ := ready T i x ρ (A:=A) (η:=η) (p:=p) (R:=R) G'
   rw [basepoint_read, formal,Wick.made_part];
   apply Wick.fixed (Γ i hp hr h) (Chart.tangent G T.Free) _ 1
   funext v; simp_rw [← basepoint_read, base_exponential (ht v)]

lemma common (hs : S.patch.Branches S.kernel G)(η)(x : Dir G c) : formal T i hp hr h η x A m W=
    Wick.script (YM.RG02.Branch.publicLaw S)
      (E:=fun _=>AxisChart G T)
      (fun u => Γ (YM.RG02.Branch.representActors S u) hp hr h) (fun u => pre T (YM.RG02.Branch.representActors S u) η p R x A m W ρ) := by
   symm; apply PowerSeries.ext; intro k; ext s
   rw [Wick.script,Wick.mix_part]
   let M := formal T i hp hr h η x A m W
   have hG j : ∀ k, coeff k (formal T j hp hr h η x A m W)=coeff k M := by intro k; rw [formal_constant T i hp hr h j η x hs]
   let a := (coeff k M).part s
   change YM.RG02.Branch.publicLaw S (fun j => (coeff k (formal T (YM.RG02.Branch.representActors S j) hp hr h η x A m W)).part s)=a
   rw [show (fun j => (_ : Poly B).part _)= a • (1 : Wick.Actor.Draw (YM.RG02.Branch.Picks S) → ℂ) from ?_,map_smul,(YM.RG02.Branch.public_independent S).1]; simp
   funext j; rw [hG]; simp [a]

/-- Coefficient test with both the source marks and vacuum terms, inclusive
through r. Use Drivers.lean to decompose this into line contributions with
any indicated finite dependencies. `publicLaw` always used in the branch
interior. Costs of assemblages are NOT uniform by this theorem. -/
theorem assembled (hs : S.patch.Branches S.kernel G) (x : Dir G c) (G' : Ink m W)(r : ℕ) {V : Type}
    (ℓ : Wick.Actor.Draw (YM.RG02.Branch.Picks S) → V → Module.Dual ℝ (AxisChart G T))
    (l : YM.Multi.Hot (mixed r B)→ Wick.Actor.Draw (YM.RG02.Branch.Picks S)→ MvPolynomial V ℂ)
    (H : Wick.models (E:=fun _=>AxisChart G T) r ℓ (fun u => pre T (YM.RG02.Branch.representActors S u) η p R x A m W ρ) l) :
    encode r (Grade.logarithm (formal T i hp hr h η x A m W)) = Multi.substitute (mixed r B)
      (connected (Wick.stellar (YM.RG02.Branch.publicLaw S)
         (fun u=> Wick.coloring (Γ (YM.RG02.Branch.representActors S u) hp hr h) (ℓ u)) l)) := by
   rw [common T i hp hr h hs η x]
   exact Wick.program_log (fun _=> Chart.tangent G T.Free) (YM.RG02.Branch.public_independent S).1 (fun u=> (ready T _ _ _ G').1) (fun u => (ready T _ _ _ G').2) r ℓ H
end Draw
end YM.RG02.Fk
