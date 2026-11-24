import YM.PertExtension.CutoffFree
import YM.PertExtension.PositionPrescription
import YM.PertExtension.MomentFrame

/-! Identifying the degree-zero rows at bare Wick normalization with the
same reference Wick fields used in the curve weak-limit comparison. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
namespace YM.PertExtension.MaxwellReading
open Function Filter Set Wilson Lattice RG MeasureTheory Orb Gauge MvPolynomial Finset Next.Rank Next.Rank.Normal Maxwell Wick Extra.FD
open LatticePT Source Labels Configuration Position Physical Climb Table Extraction
open LatticePT.Mixed LatticePT.Leading
open scoped ContDiff Topology BigOperators Classical
variable {G:Gauge}(F : Frames G)(H:Hol G) (S:∀ d, SectionData (F.level d))(hS:∀d,(S d).Sound H)(hP:∀ d,Bid.pop (S d))
local notation "J" d => PositionPrescription.Index F d
abbrev choice (d:ℕ):(J d) → LatticePT.Word G := PositionPrescription.labels F d H S hS hP
abbrev base (d:ℕ):Mark (J d) Profile.n→ℝ := PositionPrescription.free F d
-- Data and names independent of actual T_ℓ
variable (d)(q:ℕ+)(hq:1<q.val)


open Horizon
lemma pureMatch (c:J d) : writes F d ((recorded F d).b c)=Maxwell.observable G _ ((F.level (weight d F c)).basis (sourceAxis d F c)):=by
   let he := (F.level d).bound (reference d F c)
   rw [(show (recorded F d).b c=Extra.FD.pack F (reference (F:=F) d c) from (recorded F d).corners c|>.choose_spec)]
   unfold Extra.FD.pack sourceAt; rw [LinearMap.comp_apply,writes_project,← source_match]
   change observable G d ((F.level d).coords.symm ((F.level d).coords _))= _
   rw [LinearEquiv.symm_apply_apply];rfl
lemma pure_e (u:LatticePT.Word G) : barPol (electrical u) = electrical u := by rw [show electrical u=Maxwell.observable G _ _ from rfl,← observe_bar,u.F.realForm] -- fix
lemma class_electric {P:Physical.Profile}(i:Fin P.n → PositionPrescription.Index F d) (x:Points P.n) :
     (Bel (standard F)).useAt (Bel (standard F)) x (fun t:Fin P.n=> (⟨d, (recorded F d).b (i t)⟩)) = electricity (choice F H S hS hP d ∘ i) x:=by
   change (freeTable F).useAt (freeTable F) _ _ = _
   rw [writes_eval]; dsimp only
   simp_rw [pureMatch F];rfl
lemma is_real {P:Physical.Profile}(i:Fin P.n → PositionPrescription.Index F d){x:Points P.n}(h : x∈conf P.n) : star (electricity (choice F H S hS hP d ∘ i) x)=electricity (choice F H S hS hP d ∘ i) x:=by
    rw [← wick_bar h];congr; funext a;exact pure_e ((choice F H S hS hP d ∘ i) a)

lemma reading_zero_data (D:TestSystem (J d) Profile Profile.n) (j:ℕ)(z:Mark (J d) Profile.n) : PowerSeries.constantCoeff (PositionPrescription.systemData F d H S hS hP D q j z)=
      polynomialTop (choice F H S hS hP d∘ z.2) q j ((Complex.re ∘ z.fst.test) ∘ YM.points) 0:=by rw [PositionPrescription.systemData, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,PowerSeries.coeff_mk];rfl -- coeff_mk
include hq
lemma tends_raw (D:TestSystem (PositionPrescription.Index F d) Profile Profile.n) (z:Mark (J d) Profile.n):
      Tendsto (fun j=> PowerSeries.constantCoeff (PositionPrescription.systemData F d H S hS hP D q j z)) atTop (𝓝 (PositionPrescription.free F d z)):=by
   rcases z with ⟨t,i⟩
   let p:=t.test
   have hz:tsupport p⊆ conf t.n:=p.tsupport_subset
   have hts:Function.support (Complex.re ∘ p) ⊆ tsupport p:=fun y hy=> subset_closure (fun h=>hy (by simp_rw [Function.comp_apply,h];rfl))
   let vs:=choice F H S hS hP d ∘ i
   have ht:= CutoffFree.profile_limit vs _ hq _ p.hasCompactSupport hz hts (Complex.continuous_re.comp p.continuous)
   simp_rw [reading_zero_data]
   apply ht.2.mono_right (le_of_eq ?_)
   congr 1
   unfold PositionPrescription.free Physical.free Physical.reading Physical.readingC -- baseline real part
   simp only [p,Test.applyTo]
   calc
    _ = ∫ x:Points t.n,CutoffFree.realTyped vs (Complex.re ∘ p) x:= rfl
    _ = (∫ x:Points t.n,p x * electricity vs x).re := by
      refine Eq.trans ?_ (integral_re (p.smearing (K:=electricity vs) (fun x hx=>(moment_smooth (G:=G) _ hx).continuousAt.continuousWithinAt))) -- notation re mismatch
      exact integral_congr_ae <| Eventually.of_forall fun x=>by
         unfold CutoffFree.realTyped; dsimp only;by_cases hx:x∈conf t.n
         · have he:= Complex.conj_eq_iff_im.mp (show (starRingEnd ℂ) (electricity vs x)= _ from is_real F H S hS hP d i hx)
           simp only [RCLike.re, Complex.mul_re]; change _ = (p x).re*_ - _*(electricity vs x).im;rw [he,mul_zero,sub_zero];rfl
         rw [show p x=0 from t.test.vanishes hx];simp [Function.comp_apply, show p x= t.test x from rfl,t.test.vanishes hx]

    _ = _ :=by
       refine congr_arg Complex.re (integral_congr_ae <| Eventually.of_forall fun (x:Points t.n)=> ?_)
       refine congr_arg (p x*·) ?_ -- orientation symm
       simpa only [show (1:ℝ) • x=x from one_smul ℝ x] using! (class_electric F H S hS hP d i x).symm
end YM.PertExtension.MaxwellReading
