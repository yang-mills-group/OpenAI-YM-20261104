import YM.FVA2.Generator.Gyre
import YM.FVA2.Lambda.AtLast
/-!
# Generator supplier for verified field flow

βcheck, check-b estimates through first occurrences and compatible primitive scale
reads on the fields ALSO in MS-frame. Conjugation through the true converter (both differential and via $Laws$).
Infinite horizons simultaneous. No actual perturbation hypothesis. The generator bounds can be reused for field-flow certification and perturbative matching.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Generator.Drive
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Reg.Point Reg.Token Reg.Unique Reg.Choice _root_.YM.FVA2.Scale
open YM.FVA2.Scale.Facets Scale.Level Scale.Equator Scale.Measure Scale.Jury
open Scale.Meter Scale.GroupS Scale.Beta Der
variable {G:Gauge}{d:ℕ}
section Algebra
variable {F P:ℝ→ Guard G d}{A B:Guard G d} {u:ℝ}
def pairing (v:Module.Dual ℂ (FieldEnd G d))(F: Guard G d): Cn:= mk (fun i=> v (coeff i F))
-- central action of scalar series and formal derivative ∂_g
-- intentionally specialized to our formal g; respects truncation.
def central (q:Cn)(A:Guard G d): Guard G d:= mk (fun n=> ∑ i∈ Finset.antidiagonal n, coeff i.1 q • coeff i.2 A)
def D (F:Guard G d): Guard G d:= mk (fun i=> ( (i:ℂ)+1) • coeff (i+1) F)
lemma cap (v:Module.Dual ℂ (FieldEnd G d))(F:Guard G d) (p:Cn)(hp:Rooted p): pairing v (stepV p F)=(pairing v F).subst p:= by
    apply PowerSeries.ext; intro i; simp only [pairing, ← Constants.actual_subst _ _ hp, stepV,coeff_mk,rules,map_sum, _root_.map_smul,smul_eq_mul]
lemma descend (v:Module.Dual ℂ (FieldEnd G d))(A: Guard G d)(q:Cn): pairing v (central q ( D A ))= PowerSeries.derivative ℂ (pairing v A) * q:= by
    rw [mul_comm]; apply PowerSeries.ext; intro i; simp only [ pairing, D, central, coeff_mul, coeff_derivative,coeff_mk,map_sum, _root_.map_smul,smul_eq_mul ]; apply Finset.sum_congr rfl; intro i _; rw [mul_comm ((i.2:ℂ)+1)]
lemma chart {p:ℝ→Cn}{q:Cn}(h:Roll p u q)(H:∀ t,Rooted (p t))(he:p u=X): Instant (fun t=> stepV (p t) A) (central q (D A)) u:= by
    intro i v; let c:=pairing v A; have hp(F: Guard G d): v (coeff i F)=coeff i (pairing v F):=by rw [pairing,coeff_mk]
    obtain h':= h.main c H he i; -- as in q*. orient η
    simp_rw [hp,cap _ _ _ (H _),descend]; exact h'
lemma combine (hf:Instant F A u) (hg:Instant P B u): Instant (fun t=> F t * P t) ( A * P u + F u * B ) u:= by
    intro i v; let b:=Module.finBasis ℂ (FieldEnd G d); have he(k j: FieldEnd G d) : v (k*j)=∑ l, b.coord l k * v (b l * j):= by
         conv_lhs=>rw [← b.sum_repr k,Finset.sum_mul]; skip
         rw [map_sum]; apply Finset.sum_congr rfl; intro i _; rw [smul_mul_assoc,map_smul v]; rfl
    simp_rw [map_add, coeff_mul,map_sum,show ∀ (H:Guard G d) i j,v (coeff i H*j)=_ from fun H i j=>he _ _]; rw [← Finset.sum_add_distrib]; apply HasDerivAt.fun_sum; intro i _; rw [← Finset.sum_add_distrib]; apply HasDerivAt.fun_sum; intro j _; exact (hf i.1 (b.coord j)).mul ( hg i.2 (v ∘ₗ LinearMap.mulLeft ℂ ( b j )) )
end Algebra
-- scale laws imply differential transformation. `central` and $\ms'` orientations.
section commuted
variable {Y:XSpace.Initialize G}{V:Store G}{K:XSpace.Rose.Pick V}{A:Set ℝ}{T:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
variable {ν:ℝ}{p q:ℝ→Cn}{B W:ℝ→ Frames G} (h: Scale.System.Laws Y K T ν p q B W)
local notation "Z"=> Scale.Measure.Z Y K ν T d
local notation "f"=> Scale.Measure.f K ν T
include h
theorem converted : stepV f (engine (fun t=> W t d))*Z + central (beta p) (D Z) = Z * engine (fun t=> B t d):= by
    obtain hm := (combine ( (Der.walks h.minimal d).shift f ) ( chart ( A:=Z ) ( origin p h.check.smooth ) (fun t=> (h.check.led t).start) (h.check.toTouched.ground.1) )); let a:= engine (fun t=> B t d); let b:= engine (fun t=> W t d); rw [h.check.toTouched.ground.1, Scale.Frame.step_identity, h.minimal.toTouched.ground.2 d, Scale.Frame.step_one,one_mul,show (fun t=> stepV f (W t d) * stepV (p t) Z)= (fun t=> Z * B t d) from funext fun t=>h.fields t d] at hm; exact hm.once ((Der.walks h.check d).stamp Z)
end commuted

variable (Y:XSpace.Initialize G){V:XSpace.Normalize.Store G}(K:XSpace.Rose.Pick V)
variable (T:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
variable (S:Prescription (Press.portDeck G)) (h:G.Simple)(H:Scale.System.Contract Y K T S)
def engraving (p:ℝ→Frames G): Frames G:= fun d=> engine (fun t=>p t d)
structure Slopes (X:Arenas G) (p:ℝ→Cn)(B:ℝ→Frames G)(Γ: Frames G) : Prop where
    laws : Law X p B
    expose d: Instant (fun t=>B t d) (Γ d) 0
    flow t d: Instant (fun t=>B t d) (B t d * stepV (p t) (Γ d)) t
    coupling t: Roll p t ( (beta p).subst (p t) )
    startℓ {d k}(h:k<2) : coeff k (Γ d)=0
    startg {k}(hk:k<3) : coeff k (beta p)=0
    beta0 : coeff 3 (beta p)= -(↑(Lambda.VertexSlope.b G):ℂ)
    span {d e} (h:d≤e): Walk h (Γ d) (Γ e)
    native d: Native (Γ d) ∧ ∀ i, coeff i (Γ d)∈ Normalize.Change G d
namespace Slopes
variable {X:Arenas G}{p:ℝ→Cn}{B:ℝ→Frames G}
lemma ingrain (H:Law X p B)(h:∀ d t, coeff 1 (B t d)=0)(hp:∀ k<3,coeff k (beta p)=0)(hv:coeff 3 (beta p)= -(↑(Lambda.VertexSlope.b G):ℂ)): Slopes X p B (engraving B):= by
    refine ⟨ H, Der.walks H, fun t d=> Der.step H d t, running p X B H.toTouched H.smooth, fun {d k'} hk=>?_, fun {k}=>hp k,hv, fun {_} {_} h=> Der.grace H h,Der.stays H ⟩; interval_cases k'; exact Der.heel H d; exact ( Der.walks H d ).zero_col _ (fun t=> h d t)
lemma unique (Γ₁ Γ₂: Frames G) (h₁: Slopes X p B Γ₁)(h₂:Slopes X p B Γ₂): Γ₁=Γ₂:= funext fun d=> (h₁.expose d).once (h₂.expose d)
end Slopes
include h H
theorem clocks_run (ν:ℝ):
    let p:= gaugeN Y K T ν;
    let q:= gaugeM Y K T ν;
    let u:= Scale.GroupS.ψ K T ν;
    let v:= GroupS.Ψ K T ν;
    let f:= Scale.Measure.f K ν T;
    let Z:= Scale.Measure.Z Y K ν T;
    Slopes (Scale.Measure.outlook Y K) u p (engraving p) ∧
    Slopes (wave ν T) v q (engraving q) ∧
    ∀ d, (stepV f (engraving q d)* Z d)+ central (beta u) ( D (Z d) )= Z d * engraving p d := by
    intro p q u v f Z; obtain ⟨hℓ,hr,hu⟩ := H.toMission.toSchemeV.born; obtain he := Lambda.Crest.ms_to_position_slope ν Y K T S (0:ℝ) h hℓ hr hu 0; exact ⟨ Slopes.ingrain ( H.scales ν|>.check ) (fun d t=> Q.lifted ν Y K T S t h hℓ hr hu ) (fun i v=> (he.1 i v).1) he.2.1.1, Slopes.ingrain ( H.scales ν|>.minimal ) (fun d t=> Q.liftedM ν Y K T S t h hℓ hr hu ) (fun i v=> ( he.1 i v ).2) he.2.1.2.1, fun d=> converted (d:=d) ( H.scales ν ) ⟩
end YM.FVA2.Generator.Drive
