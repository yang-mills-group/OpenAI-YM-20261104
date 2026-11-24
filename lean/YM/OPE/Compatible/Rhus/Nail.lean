import YM.OPE.Compatible.Seeds.Pump
import YM.Planned.PRIMARY_INTEGRAL_295.Bigrade
/-!
# Grades, Snap funding for continuous read on off-shell vectors. Bridge to complex physical labels before the EOM projection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Maxwell Labels Tensor WithLp Source Drops WardBin Planned.PrimaryIntegral295.Parts
open scoped Topology BigOperators Classical
variable {r d m n j:ℕ}{c:ℝ}{W:Type*}{G:Gauge}
namespace Script
open Page
-- continuous lifting any normed finite-dim real
lemma wiredLift {E F:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][NormedAddCommGroup F][NormedSpace ℝ F] (A: MultilinearMap ℝ (fun _:Fin r=>E) F):∃ B: Tensor.T E F r,B.toMultilinearMap=A:=by
    let e:=Module.finBasis ℝ E; let p:= ∑ i: Fin r→Fin (Module.finrank ℝ E), ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap fun j=>(e.coord (i j)).toContinuousLinearMap).smulRight (A (e∘i))
    refine ⟨p,(MultilinearMap.ext (fun x=>?_))⟩; let v(i: Fin r)(a):=e.repr (x i) a • e a
    change p x=A x; rw [show A x=A (fun i=>∑ a,v i a) from congr_arg A (funext fun i=> (e.sum_repr (x i)).symm),A.map_sum_finset]; unfold p; rw [_root_.sum_apply]; simp only [Fintype.piFinset_univ]; apply sum_congr rfl; intro i _; exact (A.map_smul_univ (fun j=>e.repr (x j) (i j)) (e∘i)).symm
abbrev SpineX (G:Gauge)(r d:ℕ):=Tensor.T (Snap G d) ℂ r
abbrev MixX (G:Gauge)(r n d:ℕ):= (↥(partX G r n (d-1))) × (↥(partX G r n (d-1))) -- Type? partX submodule
lemma costOff (x:Fin r→Fin (d-1)): rate x=rankX x+r:=by
   unfold rate rankX; rw [show (fun i=> (x i).val+2)=(fun i=> ((x i).val+1)+1) from rfl]; rw [sum_add_distrib]; simp
-- Sym release
lemma liftingEng (x: Fin r→Snap G d)(t:ℝ) (Y:Chord G (d-1) r)(h:Off G r n (d-1) Y): Y (fun i=>engineered t (x i))= t^(n+r) * Y x:=by
       rw [deckSum Y,deckSum Y x,mul_sum]; apply sum_congr rfl; intro i _; by_cases hp:rankX i=n
       · let z:= fun j=> x j (i j); let a:=fun j=> (t^( (i j).val+2)); have hg :(∏ j,a j)=t^(n+r):=by unfold a; rw [prod_pow_eq_pow_sum]; rw [← hp]; exact congr_arg (t^ ·) (costOff i)
         rw [← hg, ← show Y (fun j=> (a j) • (monoX (i j) (z j)))=(∏ j,a j)* Y (fun j=> monoX (i j) (z j)) from Y.map_smul_univ _ _]; apply congr_arg; ext1 j; simp [monoX,z,a,engineered_at,Pi.single_smul] -- need dsimp
       rw [h.Grades i _ hp,h.Grades i _ hp,mul_zero]
lemma coloredLift (p:MixX G r n d): ∃ B:SpineX G r d,
    (∀ x:Fin r→Snap G d,B x=(↑(p.1.val x):ℂ)+Complex.I*(p.2.val x:ℂ)) ∧
    (∀ t:ℝ,∀ x:Fin r→Snap G d, B (fun i=>engineered t (x i))=t^(n+r) • B x)∧ (∀ u:G.El,∀ x:Fin r→Snap G d, B (fun i=>Cast u (x i))= B x)∧Tensor.Sym B:=by
   obtain ⟨A,ha⟩:= wiredLift (E:=Snap G d) p.1.val; obtain ⟨C,hc⟩:=wiredLift (E:=Snap G d) p.2.val; let B:=Complex.ofRealCLM.compContinuousMultilinearMap A + Complex.I • Complex.ofRealCLM.compContinuousMultilinearMap C
   have he (x:Fin r→Snap G d):B x=(p.1.val x:ℂ)+Complex.I*(p.2.val x:ℂ):=by rw [← ha,← hc];rfl
   have hP : Off G r n (d-1) p.1.val:= p.1.property; have hQ: Off G r n (d-1) p.2.val:=p.2.property
   refine ⟨B,he,fun t x=>?_,fun u x=>by erw [he,he,hP.Colors u x,hQ.Colors u x],fun x i=>by rw [he,he,hP.Perms x i,hQ.Perms x i]⟩
   have ht (Y) (hp: Off G r n (d-1) Y) := liftingEng x t Y hp
   rw [he,he,ht _ hP,ht _ hQ]; simp only [Complex.ofReal_mul, Complex.real_smul]; ring
lemma liftedTile (t: MixX G r n d) (h:n+r≤j): ∃ p:Labels.Label G j, p∈ Grade (n+r,r) ∧ ∀ x: Jet G,
    read x p.val = (t.1.val (fun _=>trunk d x):ℂ) + Complex.I * (t.2.val (fun _=>trunk d x):ℂ):=by
   obtain ⟨B,hB,ht,hs,hP⟩:=coloredLift t; let f:=tile B (n+r)
   have hh(x:Jet G): read x f=B (fun _=>trunk d x):=by
       rw [show read x _= _ from (tile_reads B (n+r) x).symm]; unfold Tensor.diagonal; simp_rw [show ∀ y:ℝ,B (fun _=> engineered y (trunk d x))=y^(n+r) • B (fun _=>trunk d x) from fun y=>ht y _]; rw [lead_monomial,if_pos rfl]
   have hf:Labels.pureDegree f (n+r) r:= tile_grade ..
   refine ⟨⟨f,?_,?_⟩,hf,fun i=> (hh i).trans (hB _)⟩
   · apply (MvPolynomial.mem_restrictSupport_iff _).mpr; intro i hi; have hu:= hf (MvPolynomial.mem_support_iff.mp (show _ from hi)); rw [weight_slot] at hu; exact (congr_arg Prod.fst hu).trans_le h
   intro J u; rw [hh,hh]; exact hs u _
end Script
end YM.OPE.Flume
