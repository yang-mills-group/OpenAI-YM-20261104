import YM.FVA2.O.Read.Charts
/-!
# Reflected full-horizon Gram rank

Realize the pairing at one point on the positive time axis with reflected field
on the right (`bond`, right label reflected anti-conjugately). Index convention for
this `GramP` matrix: test at left index, unreflected central label at right index.
Prove strictly positive definite and unit criterion (for later smeared tests).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Read
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh O.Bind O.Project
variable { G:Gauge }{I:Type}{n d k:ℕ}{V:Arenas G}{A:Album G}
abbrev bar0 (p:WickPol G):= mirrorBar ( Signed.reflect timeAxis ) p
/-- Reflected orientation on EXTERIOR, at this horizon. -/
abbrev prism (p:Sec G d): Sec G d:= ⟨ bar0 p.val,( closed_sector (closed_sector ( p.property ) (Signed.reflect timeAxis)).2 (Signed.reflect timeAxis)).1 ⟩
lemma prism_now (p:WickPol G): bar0 ( bar0 p )=p:= by unfold bar0 mirrorBar; simp only [LinearMap.coe_mk,AddHom.coe_mk,real_orient,← pol_mul]; rw [show Signed.reflect timeAxis * Signed.reflect timeAxis=1 by nth_rw 1 [← mirrored_inv timeAxis]; exact inv_mul_cancel _, pol_one ]; apply equalPol; intro A; rw [real_eval,real_eval,star_star]
abbrev halfR:E4:=((1/2):ℝ) • basis timeAxis
abbrev RProfile:= points fun _ : Fin 1=> halfR
lemma rooted_half : 0<halfR timeAxis:= by simp [halfR]
lemma doubleR : halfR+halfR=nail:= by unfold halfR; rw [← add_smul]; norm_num
lemma profileHalf : Table.Pairing.closedUp timeAxis RProfile RProfile=pairPoints (-halfR) halfR:= by
    ext1 i; refine Fin.addCases ?_ ?_ i; · intro i; fin_cases i; apply PiLp.ext; intro k; rw [Table.Pairing.enter]; change through timeAxis halfR k=(-halfR) k; by_cases ht:k=timeAxis <;> simp_all [through,halfR]
    intro i; fin_cases i; rw [Table.Pairing.leave]; rfl
lemma reflect_p (p:WickPol G)(h:p≠0): 0< Maxwell.Free.bond G 0 nail p ( bar0 p ):= by
    let P: Fin 1→ WickPol G:= fun _=>bar0 p; let U:= Signed.reflect timeAxis; have hp: bar0 p≠0:=by intro w; apply h; rw [ ← prism_now p,w ]; exact map_zero ( mirrorBar _ )
    have hq: Fin.append ( mirrorBar U ∘ P ) P = Fin.cons p fun _=> bar0 p:= by ext1 i; fin_cases i; exact prism_now p; rfl
    have hv:= detects timeAxis halfR rooted_half ( bar0 p ) hp; unfold Maxwell.Free.score Maxwell.Free.cabinet at hv; rw [ profileHalf,hq,← Maxwell.Free.bond_eval, ← Maxwell.Free.pair_flow (-halfR) halfR halfR,neg_add_cancel,doubleR ] at hv; exact hv
abbrev GramP (G:Gauge)(d:ℕ): Matrix (Toon G d) (Toon G d) ℂ:= fun b a=> Maxwell.Free.bond G 0 nail ( theory a ).val ( bar0 ( theory b ).val )
abbrev H_pos {I:Type}[Fintype I] (M: Matrix I I ℂ): Prop:=∀ x:I→ℂ,x≠0→ 0 < star x ⬝ᵥ (M*ᵥ x) -- parentheses
lemma costs_Gram (x:Toon G d→ ℂ) : let v:= ∑ i:Toon G d, x i • ( theory i : Sec G d ); star x ⬝ᵥ (GramP G d *ᵥ x) = Maxwell.Free.bond G 0 nail v.val ( bar0 v.val ):= by
    intro v; unfold v; rw [AddSubmonoidClass.coe_finsetSum]; unfold bar0; simp_rw [ SetLike.val_smul,map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, map_smulₛₗ ]; simp only [smul_eq_mul, Matrix.mulVec,dotProduct, Finset.mul_sum, GramP, Pi.star_apply,starRingEnd_apply ]; -- double sum order
    exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> by unfold bar0; simp only [RingHom.id_apply]; ring
lemma GramP_pos : H_pos ( GramP G d ):= by
    intro v ht; rw [ costs_Gram ]; apply reflect_p; intro h; apply ht; funext i; obtain hp:=congr_arg (Score.coord i) (show (∑ j:Toon G d, v j • theory j)=0 from Subtype.ext h); simp only [map_sum,map_smul,Score.pivotδ,map_zero,smul_eq_mul,mul_ite,mul_one,mul_zero, Finset.sum_ite_eq'] at hp; simpa using hp
lemma positive_unit {I:Type}[Fintype I] [DecidableEq I]{M:Matrix I I ℂ}(h:H_pos M): IsUnit M:= by
    apply Matrix.mulVec_injective_iff_isUnit.mp; intro i j hv; by_contra ht; obtain H:= h ( i-j ) (sub_ne_zero.mpr ht); rw [ Matrix.mulVec_sub,hv,sub_self, dotProduct_zero ] at H; exact lt_irrefl _ H
end YM.FVA2.O.Read
