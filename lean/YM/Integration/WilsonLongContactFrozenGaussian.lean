import YM.QCDVacuum.Stall.Cote
import YM.Integration.WilsonLongContactTown
import YM.Integration.WilsonLongContactProtectedAddress

/-! The native finite Gaussian marginal for one registered physical activity.
The finite-block calculation is inherited from QCDVacuum/Cleft/Pelt. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.PhysicalNext.Repeat.WilsonLongContactFrozenGaussian
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Gaussian Tablet Quill Baffle Polar Prism Brim
open WardBin.Lies Push.PriceCompiler Foramen Gate Lotus Township Finset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {B B' : BudgetPoint} {Y : Support c} {U : Config G c} {j n : ℕ} {L : Side}
variable {d A t C' w M N Q v δ K b' ζ β W k ε y₀ J' L₀ X' : ℝ}
variable (X : Coat T F)
    {I:Type} [Fintype I] [DecidableEq I] (i : ℕ) (R : Rep G f) (a : Museum F X.x (bareStores S) (R.activities.reg i).support Y I)
    (O:Finset I)(q κ : Chi)(b:ℝ)(D:Record)
variable {ι : Type}[Fintype ι]{τ : ι ↪ Wing}(N': Township τ R T)

open Next.Foundations
variable (s:Finset ι)
abbrev purse6 (X:Coat T F)(I:Type) [Fintype I] (O:Finset I)(ζ:ℝ) (u:I→G.Color):= creates X ζ u * ∏ i∈O,X.χ.innerShare (2*ζ*X.t) ‖u i‖
def deal (O : Finset I) (ζ :ℝ) (V:Config G c)(H:Config G f→ℝ):=
    ∫ s, purse6 X I O ζ (peanuts X a V R.beta s)* H (strip6 X a V (peanuts X a V R.beta s)) ∂Gaussian.cloud (lamp6 X a V)
def scans (N':Township τ R T)(s:Finset ι)(V:Config G c): Config G f → ℝ:= ∏ j∈ s,((N'.tune V).has j).ingredient
variable (u:Finset ι)
def pays₆(k:Finset (Bond f)): Finset I := univ.filter fun j=> a.address j ∈ k
abbrev wires₃ (j:ι) := X.plaza (baseRead ((τ j).support R) X.x S)
structure Lick (O:Finset I) :Prop where
   healthy (m:ι) (h:m∈u) : inspected ((τ m).support R)⊆ inspected (R.activities.reg i).support -- missing N'
   unionM (V:Config G c)(z:Directions G f) : let W:=vary X V
      (∏ j ∈ u, W.enforce (2*ζ) z (wires₃ (τ:=τ) X R j)) = WilsonLongContactFrozenGaussian.purse6 X I O ζ (fun j=> z (a.address j))
variable (hp : Scrim X a)
include hp
omit [DecidableEq I] [Fintype ι] in
lemma singleton (j:ι)(h: (τ j).support R=(R.activities.reg i).support): Lick (ζ:=ζ) (τ:=τ) X i R a {j} ∅:= by
   refine ⟨fun k hk=> (by rw [Finset.mem_singleton.mp hk,h]),fun V z=>?_⟩; unfold wires₃ purse6 creates enforce; dsimp only; rw [prod_empty,mul_one, prod_singleton,h,plaza_cal X a hp,prod_map]; rfl
omit hp
variable (hA:Lick (ζ:=ζ) (τ:=τ) X i R a u O)
include hA
omit [DecidableEq I] [Fintype ι] in
lemma scanned (V:Config G c): Measurable (scans R N' u V) ∧ LocalOn (inspected (R.activities.reg i).support) (scans R N' u V):= by
    let f j := (N'.tune V).has j; unfold scans
    refine ⟨?_, fun U U' hh=>?_⟩
    · change Measurable (∏ j∈u,(f j).ingredient); rw [show (∏ j∈u,(f j).ingredient)=(fun U=>∏ j∈u,(f j).ingredient U) from (by funext U; rw [Finset.prod_apply])]; exact Finset.measurable_fun_prod _ fun i hi=> (f i).borel
    rw [Finset.prod_apply, Finset.prod_apply]; exact prod_congr rfl fun i hi=> (f i).specific U U' (agrees_mono hh (by unfold Blade.crest f; rw [Quartet.reserves]; exact hA.healthy i hi))
include hp
open Matter
variable (hP: Room P S T X.x)
include hP
omit [DecidableEq I] in
lemma currant (V:Config G c)(p:Molecule S)(hx:tick τ p=u)(hb:u.map (registry S τ)=p)(z:Air f G)(Y:F.Slice G)(Ñ:ChartRatio G)(l:ℕ):
    let w:=peanuts X a V R.beta (WithLp.ofLp z ∘ scoop X a)
    N'.floret ((vary X V).wrapY Y) p W ζ Ñ (own p) l z= purse6 X I O ζ w *scans R N' u V (strip6 X a V w):=by
    intro w; let P':=(vary X V).wrapY Y; let u':= worldZ P' R.beta z
    unfold Township.floret Township.hire; rw [hx,hb,Finset.sdiff_self, Polar.floating,prod_empty, mul_one,N'.quota_any]
    have ht (j:ι)(h:j∈u): ((N'.tune V).has j).paidU P' ζ u' = ((N'.tune V).has j).ingredient (P'.input u') * (vary X V).enforce (2*ζ) u' (wires₃ X R j (τ:=τ)):= by unfold Blade.paidU Blade.fond; rw [Quartet.reserves, Wing.badge_area]; rfl -- edit
    have hw j : u' (a.address j)=w j:= shuttle X a hp hP Y R.beta z j V
    change (∏ j∈u,((N'.tune V).has j).paidU P' ζ u')=_; rw [prod_congr rfl ht, prod_mul_distrib, hA.unionM V u', mul_comm]
    rw [funext hw,(scanned X i R a O N' u hA V).2 (P'.input u') (strip6 X a V w) (entered X a hp Y u' hw)|>.symm]; unfold scans; rw [Finset.prod_apply]
omit hP hp hA in
private def berth : I×G.ColorIndex ↪ ↥(podium S G Y X.B) := {
  toFun j := ⟨scoop X a j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun x hx=> a.stores j.1 (halo_spec.mpr
    ⟨_,Finset.mem_singleton_self _,le_trans hx (show 25*radiusB X.x≤ Heir.reach X.x+4 by unfold Heir.reach; omega)⟩)⟩⟩
  inj' p q h := (scoop X a).injective (congr_arg Subtype.val h) }
lemma freezes (V:Config G c)(p:Molecule S)(hx:tick τ p=u)(hb:u.map (registry S τ)=p)(Ñ:ChartRatio G)(l:ℕ)(hV : (Pond.circuit (podium S G Y X.B) (vary X V).relating).PosDef):
    N'.cinema (vary X V) p W ζ Ñ l (podium S G Y X.B)= WilsonLongContactFrozenGaussian.deal X i R a O ζ V (scans R N' u V):= by
    unfold Township.cinema; let S':= podium S G Y X.B; let B:=Pond.circuit S' (vary X V).relating
    let b:= peanuts X a V R.beta; let f z:=purse6 X I O ζ (b z)*scans R N' u V (strip6 X a V (b z)); let μ:=Gaussian.cloud (Malachite.lamp6 X a V); let e:=berth X i R a; let f' (x:Poll.Body (↥S')):= WithLp.ofLp x ∘ e
    have hh : MeasurePreserving f' (Poll.sweep B) μ := registering X V i R a S' hV.posSemidef e (fun _=> rfl)
    have he (d:F.Slice G): (∫ z:Poll.Body (↥S'),Shield.lens₀ B z*N'.floret ((vary X V).wrapY d) p W ζ Ñ (own p) l (Pond.spill S' z))=∫ z,f z ∂μ:=by
      let F z:= N'.floret ((vary X V).wrapY d) p W ζ Ñ (own p) l (Pond.spill S' z); change (∫ z,Shield.lens₀ B z*F z)=_
      rw [←Shield.recommends B hV F]
      have hx z:F z=f (f' z):= by
         have hv: WithLp.ofLp (Pond.spill S' z) ∘ scoop X a= f' z:= funext fun j=> congr_arg (fun v:Poll.Body (↥S')=> v (e j)) (Pond.settled S' z)
         unfold F; rw [currant X i R a O N' u hp hA hP V p hx hb, hv]
      simp_rw [hx]; have hx':Measurable f:= by
         have hk : Measurable b:= measurable_pi_lambda _ fun j=> measurable_const.add (Measurable.const_smul (g:=fun p:Prices G I=>tape p j) ((measurable_pi_apply j).comp tape.measurable) (gStep R.beta))
         have hz:∀ O:Finset I,Measurable fun p=> ∏ i∈O,X.χ.innerShare (2*ζ*X.t) ‖b p i‖:= fun O=>Finset.measurable_fun_prod _ fun j _=> (X.χ.smooth.continuous.measurable).comp (((((measurable_pi_apply j).comp hk).norm).div_const _).pow_const _)
         exact ((hz _).mul (hz _)).mul ((scanned X i R a O N' u hA V).1.comp (Art.entering X (V:=fun _:Prices G I=> V) (Y:=fun _=>X.Y) measurable_const measurable_const ((measure_tap X a).comp hk))) -- syntax?
      have hv:=hx'.aestronglyMeasurable (μ:=μ); rw [← hh.map_eq] at hv ⊢; exact (integral_map hh.aemeasurable (show AEStronglyMeasurable f _ from hv)).symm
    change (∫ d:F.Slice G, (∫ z, Shield.lens₀ B z*N'.floret ((vary X V).wrapY d) p W ζ Ñ (own p) l (Pond.spill S' z)) ∂F.order G)=_
    simp_rw [he]; rw [integral_const,MeasureTheory.probReal_univ,one_smul]; rfl

end YM.PhysicalNext.Repeat.WilsonLongContactFrozenGaussian
