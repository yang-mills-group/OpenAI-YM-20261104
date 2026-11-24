import YM.GradedFar.Sail
/-!
# Evaluate coordinate derivative of ordinary physical packet

in true continuum & use exactly that rotation/field data for derivatives. Conjugate:
real linear here (use the hierarchy rights for the push).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Window
open Function Filter Set MeasureTheory Metric
open Extraction Table Spec OPE OPE.Orbits OPE.Nesting Orbits.Reader PhysMS
open Tariff
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} (F : Final C f S)(R: Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) {n:ℕ} (d:ℕ) (o:E4) (r:ℝ) (v:Fin n→S.Tag)
local notation "θ"=> F.sector.derivatives
local notation "X" => F.sector.turns
local notation "Ω"=> Reader.port R
local notation "K₁"=> target F R d o r
local notation "ρ"=> F.room.kernel.spin
private def tone (p:S.Tag):S.Tag:= ⟨p.1,S.conj (ρ) p.1 p.2⟩
lemma seasoned (x:Fin n)(a:Axis): tone F ∘ elevate F v x a=elevate F (tone F ∘ v) x a:=by
 funext i; by_cases hh:i=x
 · subst i; dsimp only [Function.comp_apply,elevate]; rw [update_self,update_self]; unfold tone; rw [F.phase.transport.rights.realDer]; rfl
 simp_rw [Function.comp_apply,elevate,update_of_ne hh]; rfl
local notation "u₁"=> averageV (Ω) (X) d
private def castL (x:Points n)(v:Fin n→S.Tag):= checkReal (Ω) R.law R.continuum d (sites o r x) o (voices v)
private lemma tilted (x:Points n)(v: Fin n→ S.Tag): castL F R d o r x v=(2:ℝ)⁻¹ • (u₁ (sites o r x) o (voices v) + conjugateR (ρ) d
    (u₁ (sites o r x) o (voices (tone F ∘ v)))):=checkValue ..
local notation "Z₀"=> castL F R d o r
lemma year (x:Points n)(i:Fin n×Axis)(b:ℝ)(hx:K₁ (slopePath x (Points.direction i.1 i.2) b)): HasDerivAt
    (fun s=> Z₀ (slopePath x (Points.direction i.1 i.2) s) v)
    (r • Z₀ (slopePath x (Points.direction i.1 i.2) b) (elevate F v i.1 i.2)) b:=by
 obtain ht:=purifier F R d o r v x i b hx; obtain hp:= purifier F R d o r (tone F∘v) x i b hx; let C:= (conjugateR (ρ) d).toContinuousLinearMap
 let f(v:Fin n→S.Tag)(s:ℝ):= u₁ (sites o r (slopePath x (Points.direction i.1 i.2) s)) o (voices v)
 obtain he:= ht.add (C.hasFDerivAt.comp_hasDerivAt b (show HasDerivAt (f (tone F ∘ v)) _ b from hp)); apply HasDerivAt.congr_of_eventuallyEq ((he.const_smul ((2:ℝ)⁻¹)).congr_deriv ?_)
 · exact Eventually.of_forall (fun s=> tilted F R d o r (slopePath x _ s) v)
 rw [map_smul,← smul_add, tilted,seasoned]; exact smul_comm ..
lemma each_fresh (x:Points n)(i:Fin n×Axis)(b:ℝ)(hx: K₁ (slopePath x (Points.direction i.1 i.2) b)): HasDerivAt
    (fun u=> R.fresh d (sites o r (slopePath x (Points.direction i.1 i.2) u)) o (voices v))
    (r • R.fresh d (sites o r (slopePath x (Points.direction i.1 i.2) b)) o (voices (elevate F v i.1 i.2))) b:= by
 let L:= ((R.knife d).restrictScalars ℝ).toContinuousLinearMap
 obtain hf:= L.hasFDerivAt.comp_hasDerivAt b (year F R d o r v x i b hx); rw [map_smul L] at hf; exact hf
-- through horizon
local notation "Y*"=> sites o r
abbrev arena (x:Points n):Prop:= ∀ i≤d,target F R i o r x
lemma season_open (n:ℕ) : IsOpen {x:Points n| arena F R d o r x}:= by
 apply isOpen_iff_mem_nhds.mpr; intro x hx; refine Eventually.mono ((eventually_all_finset (Finset.Iic d)).mpr (fun i hi=> ?_)) (p:=fun x:Points n=> ∀ i∈ Finset.Iic d,target F R i o r x) ?_
 · exact (target_open F R o r i n).mem_nhds (hx i (Finset.mem_Iic.mp hi))
 exact fun i hi j hj=> hi j (Finset.mem_Iic.mpr hj)
lemma packet_year (x:Points n)(i:Fin n×Axis)(b:ℝ)(hx: arena F R d o r (slopePath x (Points.direction i.1 i.2) b)): HasDerivAt
    (fun u=>R.packet d (Y* (slopePath x (Points.direction i.1 i.2) u)) (voices v) o)
    (r • R.packet d (Y* (slopePath x (Points.direction i.1 i.2) b)) (voices (elevate F v i.1 i.2)) o) b:= by
 unfold Reader.packet; rw [Finset.smul_sum]; apply HasDerivAt.fun_sum; intro i _
 obtain hu:= Nat.le_of_lt_succ i.isLt; let L:= (((θ).rise hu).restrictScalars ℝ).toContinuousLinearMap
 obtain he:= L.hasFDerivAt.comp_hasDerivAt b (each_fresh F R _ o r v x _ b (hx i.val hu)); rw [map_smul L] at he; exact he
lemma packet_shine {x:Points n}(hx:arena F R d o r x): ContDiffAt ℝ ∞ (fun y=>R.packet d (Y* y) (voices v) o) x:= by
 unfold Reader.packet; refine ContDiffAt.sum (fun i _=>?_); obtain h:= Nat.le_of_lt_succ i.isLt; let L:= (((θ).rise h).restrictScalars ℝ).toContinuousLinearMap
 exact L.contDiff.contDiffAt.comp x ((fresh_smooth R i.val (Y* x) o (voices v) (hx i.val h)).comp (f:=fun y:Points n=> (Y* y,o)) x (((physics_sites o r (n:=n)).prodMk contDiff_const).contDiffAt))
end YM.Integration.GradedFar.Window
