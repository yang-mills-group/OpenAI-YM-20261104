import YM.SignedWilsonExpansion.Museum.Arm
import YM.SignedWilsonExpansion.Museum.Stacks
import YM.SignedWilsonExpansion.Kane.Curb
/-! # Public comp & pre-comp fields realized by `gala`, a fixed label throughout measuring campaigns. Even the reflected and unit fields have their literal versions. Weak reporter representatives are approximation tools paired on an additional fuse (connect later), NOT used to define the actual ordered comparisons here. Tests keep joint weights even for products. -/
set_option autoImplicit false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.SignedWilsonExpansion.Museum
open FullVolume Function Filter Set MeasureTheory Lattice Wilson RG Extraction Extraction.Lease Difference Gaps Cells Asymptotics Finset
open PhysicalNext.Repeat.Legato Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Scale.Level Spec PhysMS PhysMS.Frame
open Next.UVStress Kane.Tilted Scale Rose
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}(R:Run G){n d:ℕ}{o:Extraction.Order}{S:Table R.family.book}(F:Final R.family o S)(A:Museum.Portfolio S F.room.kernel.spin)(W:ℝ→tower S)(r:ℝ)

abbrev gala (z:ℕ): Sec G z →ₗ[ℂ] R.family.book.Ref z:=( A z ).desk.comp (walk W r z).toLinearMap
abbrev costumes (d:ℕ)(v:Tags G d n)(i:Fin n): R.family.book.Token:= ⟨d,gala R F A W r d ( v i )⟩
lemma gentry (v: Tags G d n)(x:Points n)(t:r • x∈ conf n):
    S.read (r • x) (costumes R F A W r d v)= PlotW F W none r d n x v:=by
   rw [← S.at_project S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) t]
   change S.classMoment S _ (r • x) (fun i=> S.project d ((A d).desk (walk W r d (v i)))) = _; simp_rw [Arm.era]; rfl
variable (m:Finset (Fin n)) (v:Tags G d n)
abbrev tableaux (N p:ℕ)(u:Ps N p R.family n):ℂ:= R.family.numeric N p (costumes R F A W r d ( missing v m )) u
lemma literalP (t: walk W r d ( Normalize.leaf G d )=S.unit d) {N:ℕ} (h:R.family.ref d ≤ N) (p:ℕ) (u:Ps N p R.family n): tableaux R F A W r m v N p u= ∫ U,( ∏ i∈ m, R.family.O N p (gala R F A W r d (v i)) (u i) U ) ∂(law G (R.family.side N p) (R.family.beta N p)):=by
   unfold tableaux; rw [ R.family.num ]; apply integral_congr_ae; apply Eventually.of_forall; intro U; generalize_proofs
   let C:= R.family; change ( ∏ i:Fin n, C.O N p (gala R F A W r d (Rose.missing v m i)) (u i) U ) = _
   symm; refine Eq.trans ( Finset.prod_congr (g:=fun i=> C.O N p (gala R F A W r d (Rose.missing v m i)) ( u i ) U ) rfl (fun i hi=> ?_)) ( Finset.prod_subset m.subset_univ ?_ )
   · simp only [Rose.missing,hi,if_true]; rfl
   intro i hi hj
   have he:gala R F A W r d (Normalize.leaf G d)= C.refUnit d:=by
       rw [gala, LinearMap.comp_apply,LinearEquiv.coe_coe,t,(A d).dry];rfl
   simp only [Rose.missing,hj,if_false,he]
   exact congr_fun (C.constant R.makes d h (u i)) U

lemma barQ (t:∀ x:Sec G d, walk W r d ( reel d x )= S.conj F.room.kernel.spin d (walk W r d x))(v:Sec G d) : gala R F A W r d ( reel d v ) = star (gala R F A W r d v):=by
   unfold gala; rw [LinearMap.comp_apply,LinearEquiv.coe_coe,t,(A d).adj]; rfl
lemma turnsQ (t:∀ (s:Signed) (x:Sec G d), walk W r d ( ori s.ortho d x )= S.mirror F.room.kernel.spin d s (walk W r d x)) (a:Signed)(v:Sec G d) : gala R F A W r d ( ori a.ortho d v )= R.family.book.mirrorGroup d a (gala R F A W r d v):=by rw [gala,LinearMap.comp_apply, LinearEquiv.coe_coe,t,(A d).spiral]; rfl -- check scoped

variable (f:Test n)(φ:(Finset (Fin n)→ℂ)→ℂ)(h:G.Simple) (hv:PositionsUV R.family Extraction.Sequence.full)(hX:(Homes.track o).PointLimits R.family S) (hr:0 < r) (ht:Continuous φ)
include h hv hX hr ht
abbrev Sales (x:Points n):ℂ:=φ fun m=> PlotW F W none r d n x ( missing v m )
lemma counterP : (Homes.track o).limits (fun p=>Prism R.family.S ( tsupport f ) p r) (fun N p=>∑ u:Ps N p R.family n,mass R.family f r N p u*φ fun m=> tableaux R F A W r m v N p u ) ( f.applyTo (Sales R F W r v φ) ):=by
    let q: Finset (Fin n)→Fin n→ R.family.book.Token:= fun m=> costumes R F A W r d (Rose.missing v m)
    have ht': f.applyTo (fun x=> φ fun j=> S.read (r • x) (q j)) = _:= Test.apply_eq f (P:= Sales R F W r v φ ) (fun x hx=> congr_arg φ (funext fun i=> gentry R F A W r _ x ( Work.A05.smul_conf hr hx )))
    rw [← ht']; exact sequenceP f r φ ht R h hv F.room.kernel.smooth hX q hr
end YM.SignedWilsonExpansion.Museum
