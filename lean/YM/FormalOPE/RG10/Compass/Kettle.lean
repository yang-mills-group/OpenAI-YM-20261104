import YM.FormalOPE.RG10.Spiral.Spun
import YM.FormalOPE.RG10.Profile.Press
import YM.Extra.SOURCE_HISTORIES.Motion
/-! Finite mixture law. This uses the H motion on the OFF shell labeled positions before any
H-lifts and conjugations, original stamps including the inverse degree coupling factor. Then pull
through the *same* Wick/cross-cost top correction in WilsonX. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Compass
open Function Wilson Lattice Gauge Precision Source PertExtension Filter RG PertExtension.LatticePT
  Finset RG10.Position InversionTop Orb LatticePT PowerSeries Chart
open YM.PertExtension.Series.Radial (jet) -- namespace
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{n:Side}
local notation "K" => Kernel (Unit × Dir G n)
local notation "E" => Dir G n
variable {J:Type*}

/-- linearity just on those admitted same-slot representatives. -/
lemma different {A:Stamp G n} {S:Finset J} {B:J→Stamp G n}{f:J→ℝ}
 (h:A.stencil=∑j∈S,f j • (B j).stencil) (ht:∀j∈S,(B j).slots=A.slots) :
 A.couplingMark=∑j∈S,(f j:ℂ) • (B j).couplingMark:= by
 funext x; apply PowerSeries.ext; intro k; simp only [Stamp.couplingMark,Finset.sum_apply,map_sum,lower,Pi.smul_apply,map_smul,smul_eq_mul,coeff_mk]
 let b (B:Stamp G n):= (restrictedO B.stencil ∘ expLinks G (Cotree n))
 have he : b A=∑ j∈S,f j • b (B j):= by funext U; unfold b; simp only [Finset.sum_apply, Pi.smul_apply, h, restrictedO, comp_apply]
 unfold raw InversionTop.lift; simp_rw [into_coeff, coeff_mk]
 have hb (j:J) (k:ℕ) : ContDiffAt ℝ k (b (B j)) 0 := (B j).test.curved.germ.of_le (by exact WithTop.coe_le_coe.mpr le_top)
 change ↑(jet (b A) _ x.2) = ∑ j∈S,(f j:ℂ)* ↑(jet (b (B j)) ((B j).slots+k) x.2)
 rw [he]
 unfold jet
 rw [iteratedFDeriv_sum_apply (u:=S) (f:=fun j=> f j • b (B j)) (fun j _=> (hb j (A.slots+k)).const_smul (f j)),_root_.sum_apply,mul_sum,Complex.ofReal_sum]
 apply sum_congr rfl; intro i hi; rw [ht i hi, iteratedFDeriv_const_smul_apply (hb i _),_root_.smul_apply]; change ↑(_ * (f i * _):ℝ) = (f i:ℂ)*_; push_cast; ring

lemma exteriorD {X:Type*}(v:Kernel X)(c:ℂ) : c • v= outside (PowerSeries.C c) * v:= by funext x; exact smul_eq_C_mul ..

variable (A:F.Index→ Stamp G n)
def well : F.Coeff →ₗ[ℂ] K where
 toFun x:=∑ i,x i • (A i).couplingMark
 map_add' x y:= by simp only [Pi.add_apply,add_smul,sum_add_distrib]
 map_smul' x y:= by simp only [Finset.smul_sum,Pi.smul_apply,smul_smul,smul_eq_mul,RingHom.id_apply]
lemma essence (i:F.Index) : well A (Pi.single i 1)= (A i).couplingMark := by classical exact sum_eq_single_of_mem _ (mem_univ i) (fun j _ hj=> by simp [Pi.single_eq_of_ne hj]) |>.trans (by simp)

open InversionWard Labels
variable {S:SectionData F}{H:Hol G}(p : Bid.pop S)(h:S.Sound H)(ε:ℝ)
local notation "D" => topMatrix S H h p
abbrev ordered (v : F.Coeff) : F.Coeff := (↑(ε^4/ε^d:ℝ):ℂ) • (D).inverse (covarianceSymbol G) v
def bowl : Label G d→ₗ[ℂ] K := (↑(ε^4/ε^d:ℝ):ℂ) • (well A).comp (((D).inverse (covarianceSymbol G)).comp F.coords.toLinearMap)

lemma stirring (x : Label G d) : bowl A p h ε x = ∑ i:F.Index, outside (C ((ordered p h ε (F.coords x)) i))* (A i).couplingMark := by
 change (↑(ε^4/ε^d:ℝ):ℂ) • well A ((D).inverse (covarianceSymbol G) (F.coords x))=_
 rw [← map_smul]; change (∑ i:F.Index,(ordered p h ε (F.coords x)) i • (A i).couplingMark)=_; simp_rw [exteriorD]

variable (s:Signed)(u q:Site n)
abbrev pullMarks (i:F.Index) := Rotation.asStamp s u p h i q
private abbrev os (i:F.Index):F.Coeff:= Pi.single i 1
lemma essence_rot (i:F.Index) : (pullMarks p h s u q i).couplingMark = well (Stamp.native (affine s u q) h p) (F.act s.ortho (os i)) := by
 let w:=F.act s.ortho (os i); let J:=univ.filter (fun j=>F.grades i=F.grades j)
 let M:=Stamp.native (affine s u q) h p; let P:=pullMarks p h s u q i
 have hr (j) : ↑((w j).re) = w j := by
   apply Complex.conj_eq_iff_re.mp
   have hz:= congr_fun (Extra.Histories.Motion.act_conj F (os i) s.ortho) j
   rw [show star (os i)=os i by classical funext j; by_cases h:j=i <;> simp [os, h]] at hz
   exact hz.symm
 rw [different (A:=pullMarks p h s u q i) (S:=J) (f:=fun j=>(w j).re) (B:=M) (Rotation.reorders (u:=u) s h i q) (fun j hj=> (congr_arg Prod.snd ((mem_filter.mp hj).2)).symm)]
 simp_rw [hr]; apply Finset.sum_subset (subset_univ _); intro j _ hj; rw [show w j=0 from InversionWard.Rotation.compare s (by simpa only [J,mem_filter,mem_univ,true_and] using hj)]; exact zero_smul ..

lemma catkin (v:F.Coeff): well (pullMarks p h s u q) v = well (Stamp.native (affine s u q) h p) (F.act s.ortho v) := by
 nth_rw 1 2 [show v=∑ i,v i • os i from Eq.symm (by funext j; simp [Finset.sum_apply,os,Pi.single_apply,mul_ite])]; simp_rw [map_sum,map_smul, show ∀ i:F.Index, well (pullMarks p h s u q) (os i)=_ from fun i=> (essence (pullMarks p h s u q) i).trans (essence_rot p h s u q i)]

lemma swing (x:Label G d): bowl (pullMarks p h s u q) p h ε x = bowl (Stamp.native (affine s u q) h p) p h ε (tensor s.ortho x) := by
 unfold bowl; simp only [LinearMap.smul_apply,LinearMap.comp_apply,LinearEquiv.coe_coe,catkin,← F.act_coords, Spiral.ordered]
end YM.FormalOPE.RG10.Compass
