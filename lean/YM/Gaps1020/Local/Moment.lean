import YM.Gaps1020.Local.Assign
/-!
# Power cost semantics.

One-step local, thermal perturbation of the exponent vertices. These are
relative to the supplied fine interactions (profiles, Gaussian mean &
covariance and kernels at the actual beta and parameter history). Expressed as
genuine tilted Taylor coefficients of the *vertices*, integrated on the full
F.Slice with its same Air and the normalized forest/tag averages. Not RG
matching coefficients (no coupling reset, coordinate change or removal of
cutoffs in these powers).
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Thermal1020
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open March Next.Foundations YM.GapsLocal.ExpShares
open PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {j n k M : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {X : Coat T F} {I : Finset (Bond f)} {η r q Y W A B A' a β b p v d t γ C s C' μ g ρ ℓ : ℝ} {l:ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi} {Ñ : ChartRatio G}
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {z : Air f G} {V:E→ Config G c}{x:E}

variable {H : Cash W s μ L Q o C T R}
-- tilting parameter 1 is the true vertex

def pole (X:Coat T F)(R:Rep G f)(a:ℝ)(Ñ: ChartRatio G)(z:Air f G) (i:Head S):ℝ :=
  let u:=worldZ X R.beta z
  match i with
    | Sum.inr (.inr (.inl l)) => logMoment X a R Ñ u (X.input u) z l
    | _ => 0

def momentV (n:ℕ)(y:ℝ) := if n=0 then 0 else y^n/n.factorial

lemma tilted (n:ℕ)(y:ℝ) : iteratedDeriv n (fun z:ℝ=> Real.exp (y*z)-1) 0 / (n.factorial:ℝ) = momentV n y := by
  unfold momentV; split
  next h=> subst n; simp
  next h=>
    rw [iteratedDeriv_fun_sub (f:=fun x=>Real.exp (y*x)) (g:=fun _=>1) (by fun_prop) contDiffAt_const, iteratedDeriv_const,if_neg h,iteratedDeriv_exp_const_mul n y]
    simp

def moment (X:Coat T F) (p:Molecule S) (π:Assign p M) (R:Rep G f)(a:ℝ)(Ñ:ChartRatio G) (x:F.Slice G × Air f G):=
  ∏ i:↥p,momentV (π i).val (pole (X.wrapY x.1) R a Ñ x.2 i.val)

def simplexBars (X:Coat T F) (p:Molecule S)(π:Assign p M)(R:Rep G f)(a:ℝ)(Ñ:ChartRatio G):=
   ∫ y,moment X p π R a Ñ y ∂(F.order G).prod X.dice

-- as in Aurora
private lemma scalp_one {x C :ℝ} (I : Finset (Bond f)) (h:Canary G A C) (z:Air f G) (hv:0<x) : scalp I X X.V x A z=1 := by
  have hh i : steerJ X A (worldZ X x z) X.V i=1 := by unfold steerJ Silica.action; rw [mul_inv_cancel,G.mat_one]; exact Eider.leaves h ..
  unfold Flux.scalp Flux.jacL; dsimp only; rw [prod_eq_one (fun i _=> hh i), Silica.home X h z hv,one_mul]; apply div_self (fullFuel _ _|>.ne')

variable (p:Molecule S){Ξ:Utopia H j v d r C' χ} (h:HasClutch Ξ A) (hΘ:Oboe H j v B k A b Ξ)
variable (hlog : HeadsAreLog p)(ht:troupe T R Q.halo (radiusB s) p)
    (hX:X.x=s) (hk:X.width=o.K) (he:X.χ=χ) (hP:Healthy (Pressure.temp s) (H.unionP p) X.V)
    (hm:H.shapeW p ≤ ℓ) (hρ: charge Q L s r j ℓ ≤ ρ⁻¹) (hp:2 ≤ ρ) (hV: 0 ≤ v) (π:Assign p M)
include h hΘ hX hk he hP hm hρ hp hV hlog ht
lemma centerPower (hT:degree p π ≤ M)(hM:X.manifest) :
    weightedRhythm (edgesM S (H.unionP p) (radiusB s)) X X.V A Q.table p (assignment p π) R W o.a Q.halo=moment X p π R o.a Q.table:= by
  funext y
  let Z:=X.wrapY y.1; let q:=y.2; let V:=X.V; let I:=edgesM S (H.unionP p) (radiusB s)
  have hβ:= H.laws.intake.positive
  unfold weightedRhythm weightedRecoil
  change scalp I Z Z.V R.beta A q*weighted p _ R _ W _ _ (vary Z Z.V) (course Z A R.beta q Z.V) = _
  rw [scalp_one (X:=Z) I hΘ.conduit q hβ,home Z hΘ.conduit q hβ, show vary Z Z.V= Z from rfl,one_mul]
  unfold weighted Polar.floating; rw [← prod_attach]; change (∏ i:↥p,row p R Q.table W o.a Q.halo Z y.2 i) * (∏ i:↥p,YM.GapsLocal.ExpShares.share M (π i) (row p R Q.table W o.a Q.halo Z y.2 i))= _
  rw [← Finset.prod_mul_distrib]; apply prod_congr rfl; intro i hpX
  have hv': (π i).val < M+1:= Nat.lt_succ_of_le ((single_le_sum (f:=fun i=> (π i).val) (fun i _=> Nat.zero_le _) hpX).trans hT)
  obtain ⟨i,hi⟩:= i; obtain ⟨t,rfl⟩:=hlog i hi; let i:↥p:=⟨_,hi⟩
  change _* YM.GapsLocal.ExpShares.share M (π i).val _= momentV (π i).val _
  rw [YM.GapsLocal.ExpShares.share,if_neg hv'.ne]; unfold momentV
  cases hz:(π i).val with
  | zero=>rw [if_pos rfl]; exact mul_zero _
  | succ m=> rw [if_neg (by omega)]; exact (vertex_value (Ξ:=Ξ) (X:=Z) h hΘ p hlog ht hm hρ hX hk he hM hP hV hp t hi q m).2.2
lemma barsPower (hT:degree p π ≤ M)(hM:X.manifest): Integrable (moment X p π R o.a Q.table) ((F.order G).prod X.dice) ∧
    weightedBars p (assignment p π) (podium S G (H.unionP p) (radiusB s)) X R Q.table W o.a Q.halo = simplexBars X p π R o.a Q.table := by
  let f (_:ℝ):=X.V
  have hv : Mode f 0 j v := ⟨hV,fun i=>a_oneB G _ hV⟩
  have hh:= hΘ.flow F X hX he hk hM ℝ f 0 rfl hv
  have hb:= (unfoldBars (X:=X) H hX hM hk hh hΘ.conduit hΘ.mode p (assignment p π) (fun i=> share_contDiff ..)).self_of_nhds
  let I:=edgesM S (H.unionP p) (radiusB s); let V:=moment X p π R o.a Q.table
  have hP':= ((multiplied (X:=X) H hX hM hk hh hΘ.conduit hΘ.mode p (assignment p π) (fun i=> share_contDiff ..) I).2).self_of_nhds
  unfold simplexBars; rw [← centerPower p h hΘ hlog ht hX hk he hP hm hρ hp hV π hT hM]; exact ⟨hP',hb⟩

-- no assertion about unconstrained regrouping of the weighted leaves
lemma powerSlice (hD:Ac.Spark H.supportP p) (hF:(roster p).flags=∅) (hT:degree p π ≤ M) :
    let Z i := (planted X p).taggedL i
    weightedFringe X p (assignment p π) R Q.table W o.a Q.halo=Pond.likely (fun i => simplexBars (Z i) p π R o.a Q.table) ∧
      ∀ i:S.Choices, Integrable (moment (Z i) p π R o.a Q.table) ((F.order G).prod (Z i).dice) := by
  let f (_:ℝ):=X.V
  have hv : Mode f 0 j v := ⟨hV,fun i=>a_oneB G _ hV⟩
  intro Z
  have hh i := barsPower (X:=Z i) p h hΘ hlog ht hX hk he hP hm hρ hp hV π hT (planted_valid X p)
  rw [show weightedFringe X p _ _ _ _ _ _= _ from (weightedRainbow p (assignment p π) hΘ hX hk he hF hP hv rfl).self_of_nhds] -- defeq?
  refine ⟨?_,fun i=> (hh i).1⟩
  change weightedShelter X p _ R Q.table W o.a _ = _
  unfold weightedShelter; rw [show X.B=radiusB s from congr_arg _ hX,if_pos ⟨hD,ht⟩]
  apply congr_arg likely; funext i; exact (weightedSpices p _ H X hX X.V X.V (fun _ _ _=>rfl) hP hF i).symm.trans (hh i).2
end YM.ConnectedActivityE6.Blaze.Thermal1020
