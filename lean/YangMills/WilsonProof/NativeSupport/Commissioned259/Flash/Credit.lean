import YangMills.WilsonProof.NativeSupport.Commissioned259.Flash.Net
/-! # Necessary use of Cash calibration BACK on moving prices, including at arbitrary
    sampled poses. Undo Cash then re-consume \(g\) using earned t. Fold H adjustment
    before budgeting the already-adjusted Far estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Flash
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open FVA2.Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score O.Enh Comparing Pose Original Matrix Quotes Sparks
open Flash259HorizonFork Facets Reg.Point
open scoped Topology ContDiff Classical BigOperators Matrix
variable {n m d :ℕ}{I:Type}{F:Filter I}{A:Set (Points n)}{B:Set (Points m)}
variable {W c δ a b:ℝ} {x x':I→Points n}{y y':I→Points m}{r T:I→ℝ}
local notation "late" => 𝓝[>] (0:ℝ)
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (U:Final C f S)(J:ℝ→tower S)(N:WilsonPrescription G)
    (hJ : Leading U J) (hp: normal U J N.store) {sim:G.Simple}{dial:Bool}
    (M: MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))){σ : MS.Land.Prescription (Press.portDeck G)} (H: Main.Match N sim M σ dial)

private lemma powers {w t g:I→ℝ} (hf:(fun i=> w i - t i)=O[F] g)(hw: w=O[F] Pose.home)(ht:t=O[F] Pose.home)(p:ℕ) :
   (fun i=> (w i:ℂ)^p-(t i:ℂ)^p)=O[F] g := by
    have Ht : (fun i=>(w i:ℂ)-(t i:ℂ))=O[F] g:= by simp_rw [← Complex.ofReal_sub]; exact (Complex.ofRealCLM.isBigO_comp ..).trans hf
    have hu := (Complex.ofRealCLM.isBigO_comp ..).trans hw; have hy:= (Complex.ofRealCLM.isBigO_comp ..).trans ht
    induction p with | zero=> simp_rw [pow_zero, sub_self]; exact isBigO_zero ..| succ p ih=> simp_rw [pow_succ]; exact Pose.crossed ih Ht ((hu.pow _).congr_right fun _=> one_pow _) hy
variable {w p :ℕ} {X:I→Change G d}{s:I→ℝ}
    (L: Flash.Mesh U J N F w p r T s X x x' y y')
local notation "V" => Scale.Measure.start N.scheme N.criterion
local notation "g" => (fun i=>g0 G (r i))
local notation "V'" => Scale.Measure.outlook N.scheme N.criterion
local notation "t" => Paper.meter U J N.criterion
local notation "Jx" => (fun i=>joins (x' i) (y' i) (T i))
local notation "hard" => (fun i:I=>g i^(w+1))
variable (h : Aim F G W a b r T) (R:Room W c δ A B)(hx:∀ᶠ i in F,x' i∈A)(hy:∀ᶠ i in F,y' i∈B) (v:Tags G d (n+m))(hd:6≤d)
    (Z:Shop U J N) (ν : ℝ)
include h R hp L hx hy H ν
lemma cost_insert : Fare T F hard (fun i=>array (V d) (Jx i) p (s i) (stand (X i) ∘ v)-array (V d) (Jx i) p (s i) v):=by
  let Y i:= stand (X i); let u (i:I):= (Y i) ∘ v; let D i := array (V d) (Jx i) p (s i)
  have he : ∀ᶠ i in F,|s i|≤1 := ( L.stamps.mono_right nhdsWithin_le_nhds).abs.eventually (ge_mem_nhds (by simp))
  have h0 := aspirant R h
  have hv : hard =O[F] Pose.home := isBigO_const_of_tendsto (((g0_zero sim).pow (w+1)).comp h.reach) one_ne_zero
  have hl(i:Toon G d)(j:Fin (n+m)) : (fun k=> coord i (u k j)-coord i (v j))=O[F] hard := insertCoord _ (amount U J N L.toCash h.reach hp H) _ _
  have hf (q:BasisSlots G (fun _: Fin (n+m)=>d)) : Fare T F Pose.home (fun i=> D i (word q)) := by
    simp_rw [D,array_eq]; exact Tunes.cuts h0 he p (pre_value R ν H h hx hy _)
  have hg (q: BasisSlots G (fun _: Fin (n+m)=>d)) : Fare T F hard (fun i=> coordinates q (u i)-coordinates q v) := by
    let H (i : Fin (n+m)) : Fare T F Pose.home (fun _=>coord (q i) (v i)) := Fare.constant _
    have L (i: Fin (n+m)) : Fare T F Pose.home (fun k=> coord (q i) (u k i)) := Fare.bare (((hl (q i) i).trans hv|>.add (Pose.cpoint _)).congr_left fun _=> sub_add_cancel ..)
    exact ( Fare.overall h0 (s:=Finset.univ) (fun i _=>L i) (fun i _=>H i) («g»:=hard) (fun i _=> (Fare.bare (hl (q i) i)).extend (Eventually.of_forall fun i=>(mul_one _).symm))).extend (Eventually.of_forall fun i=>by unfold Pose.home; simp)
  simp_rw [word_sigma (stand _ ∘ v), word_sigma v, ← Finset.sum_sub_distrib, smul_eq_mul, ← sub_mul]; exact Fare.sum h0 fun j _=> (Fare.mul (hg j) (hf j)).extend (Eventually.of_forall fun i=> mul_one _)
include Z hd hJ
lemma calibrated_grid (q:ℕ) (hq:q≤w) : Coin F T (t∘r) g q Pose.home (fun i=> Paper.point U J (r i) d (n+m) (Jx i) v) (fun i=>Reg.Point.story (fxt (V d) (Jx i)) v) := by
  have h0 := aspirant R h; let B i:=Reg.Point.story (fxt (V d) (Jx i)) v
  have V'': Tunes T F Pose.home B:= pre_value R ν H h hx hy v
  let g0' (i:I) := δ
  have he:= Pose.guaranteed U J hJ N hp M H Z
  have hτ : (t ∘ r)=O[F] g := (candidate_fee N t M H he).comp_tendsto h.reach
  have h' : ∀ᶠ i in F,|t (r i)|≤1 := h.reach.eventually ((coupling_payment sim he).mono fun i hi=>hi.2.1)
  have fund:= Fare.bare (T:=T) (L.charges v); have Vc : Fare T F hard (fun i=> array (V d) (Jx i) p (t (r i)) v-array (V d) (Jx i) p (s i) v) := by
    simp_rw [array_eq,crop_apply, ← Finset.sum_sub_distrib, ← sub_mul]
    have V0:= isBigO_const_of_tendsto ((g0_zero sim).comp h.reach) ( one_ne_zero : (1:ℝ)≠0 ); have ht:=hτ.trans V0; have h2 := L.budget.trans V0
    exact Fare.sum h0 (fun i _=> (Fare.mul (Fare.bare (powers (shoots U J N L.toCash h.reach hJ hp H hd) ht h2 i)) (V'' i)).extend (Eventually.of_forall fun i=>mul_one _))
  have hs := Fare.over_pow (q+1) (w+1) (by omega) F g (( (g0_zero sim).comp h.reach ).abs.eventually (ge_mem_nhds (by simp))); have e:= (((Fare.add h0 fund (cost_insert U J N hp M H L h R hx hy v ν) ).sub h0 Vc).transport hs)
  have H': Fare T F (fun i=>g i^(q+1)) (fun i=> Paper.point U J (r i) d (n+m) (Jx i) v - crop p (t (r i)) (B i)) := by
    apply e.congr; refine Eventually.of_forall fun i=>?_ ; simp_rw [array_eq]; unfold B; abel
  refine ⟨V'',?_⟩; exact (Fare.add h0 (H'.extend (v:=fun i=>g i^(q+1)*1) (Eventually.of_forall fun _=>(mul_one _).symm)) (Tunes.excess h0 h' hτ p q (by have e:=L.repays; omega) V'')).congr (Eventually.of_forall fun i=> sub_add_sub_cancel ..)
end YM.FVA2.GradedFar259.Flash
