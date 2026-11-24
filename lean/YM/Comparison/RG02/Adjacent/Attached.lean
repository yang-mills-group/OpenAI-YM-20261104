import YM.Comparison.RG02.Adjacent.Warp
/-!
# Low order test on THIS η, α and path after re-expression in the formal *coarse* coupling

Earlier `Thermal` compared to `draft` at the old coupling and `Bare` carried on the
incoming normalization/step aperture. Here we actually transfer those figures to the scheme after first-loop
re-expression, subtracting the *real* classical & canonical one-loop coarse formal germs.
No mask clipping. Keeps same assembled stationary witness for P0/P1/P2 and gives precisely the
exponential uncertainty of the torus construction, for stipulated angular waves & budgets. In a
future step that piece of uncertainty may have to stay in a separate O discrepancy. Must still
supply trajectory-β to caliber matching on actual calendars. Script composition below
therefore doesn't authorize uniform iteration.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Adjacent.Attach
open Function Filter Finset MeasureTheory ProbabilityTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested
open Marker Multi Order YM.Next.SectorChange Integral Laplace Symmetry Symmetry.Orbit
open Moving Moving.Path Moving.Shift Valence
open Thermal LocalScript
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V:Type} [DecidableEq V] [Fintype V] {R:Census V}
variable {G:Gauge} {c f:Side} {S:StepData c f} {p:Clip}{P:PathData G}{O:ChartRatio G}
    (K:Bulk.Kernel S p P O) (D:BudgetPoint)(F:Forest S.ratio)(w:S.Choices)
    (W:Bulk.Colors R G f)(T:UnitCost)(C:Caliber)(s:R.Mode)(r:ℕ)(x:fieldDir G c 1)
local notation "U"=> ground K F w W r
local notation "ζ"=> C.back r
local notation "μ"=> C.measure

lemma remains0 : born U (C.back r) 0 r 0=U 0:= funext fun x=> by rw [ledger ζ 0 r (rank K F w W r) _ (Nat.zero_le _)]; simp
lemma remains1 (he:C.EvenK r)(hp:1≤r): born U (C.back r) 0 r 1=U 1 := by
   funext x; rw [ledger ζ 0 r (rank K F w W r) 1 hp, sum_range_one]; simp_rw [Preserves.oddPrice 0 (C.even_back r he) (by omega : 0 ≤ (1:ℕ)) (by simp : Odd (1-0:ℕ)),zero_mul,sum_const_zero,add_zero]
lemma ante (he:C.EvenK r)(hp:2≤r) : born U (C.back r) 0 r 2 = U 2 - (↑(C.measure 2) : ℂ) • U 0 := by
   funext x; rw [ledger ζ 0 r (rank K F w W r) 2 hp,sum_range_succ,sum_range_one]; simp_rw [Preserves.oddPrice 0 (C.even_back r he) (by omega : 1 ≤ (2:ℕ)) (by norm_num : Odd (2-1:ℕ)), zero_mul,sum_const_zero,add_zero]
   rw [show U 0= _ from funext (precedence K F w W r)]
   simp_rw [LocalScript.here,mul_ite,mul_zero]; rw [Finset.sum_ite_eq',if_pos (by decide : 2∈ range ((↑(0:ℕ)+2:ℤ).toNat+1)),C.proceeds r hp he]; simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]; ring

open Extra.Iteration
open Extra.Iteration.Calibration (main core)
lemma sec_match (P:PathData G) (p:Clip) {σ A Λ:ℝ}(h:P.Bounds p σ A Λ): Assembly.jet (main (n:=c) P p) 2 x=Assembly.jet (core P p) 2 x := by
    unfold Assembly.jet; rw [Calibration.splits]
    have hs : ∀ (k:ℕ) (v:ℝ) (b:ℕ→Atom G k), Charged b σ v→ ContDiffAt ℝ (↑(2:ℕ)) (Calibration.acted (n:=c) b) 0:= fun _ _ b hq=> (Calibration.acted_jet (n:=c) b h.width hq).of_le le_top
    rw [iteratedFDeriv_add_apply (f:=core P p + Calibration.acted P.cubic) (((Calibration.core_jet (n:=c) h).of_le le_top).add (hs _ _ _ h.three)) (hs _ _ _ h.four),iteratedFDeriv_add_apply ((Calibration.core_jet h).of_le le_top) (hs _ _ _ h.three),show iteratedFDeriv ℝ 2 (Calibration.acted (n:=c) P.cubic) 0=0 from Extra.Iteration.lower_jet h.width h.three 2 (by omega),show iteratedFDeriv ℝ 2 (Calibration.acted (n:=c) P.quartic) 0=0 from Extra.Iteration.lower_jet h.width h.four 2 (by omega), add_zero,add_zero]

section Output
variable {C' : History G} (K' : Bulk.Chain C') (N m q:ℕ) (h:m<N)
    (F : Forest (C'.levels.clock.op m q).ratio)(t:(C'.levels.clock.op m q).Choices)
    (W : Bulk.Colors R G (C'.S.side (m+1) q))
    (he:W.Standard) (x:fieldDir G (C'.S.side m q) 1)
local notation "α"=> K'.kin.alpha N m
local notation "c₀"=> C'.S.side m q
local notation "d"=> C'.S.side (m+1) q
local notation "R'"=> C'.rep N q m
local notation "S"=> K'.step N m q h
local notation "L"=> ground (K'.step N m q h) F t W r
local notation "η"=> Rep.path (C'.rep N q m)
local notation "δ"=> Rep.clip (C'.rep N q m)
local notation "T"=> thermal F t (Rep.clip (C'.rep N q (m+1))) (Rep.path (C'.rep N q (m+1))) (Bulk.Kernel.b (K'.step N m q h) F) K'.O

include h
open Bulk
lemma zero_kinetic: born (ground S F t W r) ζ 0 r 0 x= -Complex.ofReal (Assembly.jet (main (n:=c₀) η δ) 2 x) := by rw [remains0,precedence,Symmetry.price,maps K' N m q h F t]
include he
lemma first_kinetic (r:ℕ) (hr:1≤r)(he':C.EvenK r)(hG:G.Simple): born (ground (K'.step N m q h) F t W r) (C.back r) 0 r 1 x= -Complex.ofReal (Assembly.jet (main (n:=c₀) η δ) 3 x) := by rw [remains1 _ _ _ W C r he' hr]; exact Orbit.Linked.id_cubic (C'.levels.budget m) r K' N m q h F t W hG hr he x

variable (hp:2≤r) (hx:C.EvenK r)(hy:C.measure 2=K'.kin.alpha N m)
-- projected coarse output minus loop-subtracted; scalar p2 constants untouched
-- accounting in REAL convention (no imaginaries by signals).
def proceeds (u : fieldDir G (C'.S.side m q) 1): ℝ:= -Complex.re (born L ζ 0 r 2 u)- (Assembly.jet (main η δ) 4 u+ Assembly.jet (loop η ∘ (represent (G:=G))) 2 u) -- represent field type
omit he
include K'
lemma health : ∃ a v w:ℝ, (C'.rep N q m).path.Bounds δ a v w := by rw [K'.selected N q m h.le,K'.clips N q _ h.le]; exact ⟨_,_,_,K'.planned.cap N m h.le⟩
include hp hx hy he
lemma curve_est (a:ℕ)(ha:a≠0) : iteratedFDeriv ℝ a (proceeds C r K' N m q h F t W) 0= if a=2 then (iteratedFDeriv ℝ a T 0- (iteratedFDeriv ℝ a (draft (K'.kin.alpha N m) η δ) 0)) else 0 := by
   let D:= draft (c:=c₀) α η δ; let B:= actionResponse K' N m q h F t W r
   obtain ⟨A,v,w,H'⟩:= health K' N m q h
   let Q:= main (n:=c₀) η δ; let Q':= loop η ∘ (represent (G:=G) (n:=c₀)); let Y:= core (n:=c₀) η δ
   have h1 : ContDiffAt ℝ ω Q 0:= Calibration.main_jet H'; have h2:ContDiffAt ℝ ω Q' 0:= Bulk.loop_smooth _ _ H'
   have h3:ContDiffAt ℝ ω Y 0:= Calibration.core_jet H'; have hD:ContDiffAt ℝ ω D 0:= (retained K' N m q h (F:=F)).classicalResult
   have hY : Assembly.jet D 2 = α • Assembly.jet Y 2+ Assembly.jet Q' 2:= by
      funext x; unfold Assembly.jet; rw [show D= α • Y+Q' from rfl,iteratedFDeriv_add_apply (f:=α • Y) (h3.const_smul α|>.of_le le_top) (h2.of_le le_top), iteratedFDeriv_const_smul_apply (h3.of_le le_top)]; simp only [Pi.add_apply,Pi.smul_apply, _root_.add_apply, _root_.smul_apply, smul_add]; rw [smul_comm α _]
   have hB : ContDiff ℝ ω B:= (((Complex.reCLM.contDiff.comp (vacuum_read S F t W r 2).smooth).neg).sub (levelJet h1 4).smooth) -- defeq
   have ht : proceeds C r K' N m q h F t W=B- Assembly.jet D 2:= by
      funext y; unfold proceeds; rw [ante _ _ _ W C r hx hp,Pi.sub_apply,Pi.smul_apply, precedence S F t W r];
      rw [Symmetry.price,Thermal.maps K' N m q h F t,hy,hY]
      unfold B actionResponse ground; rw [if_neg (by omega),add_zero]; -- meticulous cast
      let u:= detail (logVac (Fk S F t W y r)) R.quiet 2; let z:= Assembly.jet Q 2 y; let q':=Assembly.jet Q 4 y; let y':= Assembly.jet Q' 2 y; let o:= Assembly.jet Y 2 y
      change -(u - (↑α:ℂ) * -(z:ℂ)).re - (q'+ y')=(-u.re-q')-(α*o+y')
      rw [show z=o from sec_match y η δ H']; simp only [Complex.sub_re, Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.neg_re]; ring
   rw [ht,iteratedFDeriv_sub_apply (hB.contDiffAt.of_le le_top) ((levelJet hD _).smooth.contDiffAt.of_le le_top),show iteratedFDeriv ℝ a B 0=_ from Thermal.slope K' N m q h F t W he r hp a ha, re_jet hD]
   dsimp only [D]; split <;> simp

local notation "J"=> C'.levels.clock.J (m+1)
lemma retained_cost (i j : Site (C'.S.side m q)) (σ τ : TypeFace 1 → G.ColorIndex → ℂ)
      (Hσ : ∀ x y, ‖σ x y‖≤1) (Hτ : ∀ x y, ‖τ x y‖≤1) :
       |iteratedFDeriv ℝ 2 (proceeds C r K' N m q h F t W) 0 ![Precision.wave i σ, Precision.wave j τ]| ≤ (Fintype.card (Site c₀):ℝ)*K'.post.Γ J*C'.levels.clock.loopCap (m+1)*Real.exp (-(K'.post.c J)*(c₀).val) := by rw [curve_est C r K' N m q h F t W he hp hx hy 2 (by decide),if_pos rfl]; exact (Thermal.retained K' N m q h).wave_price t i j σ τ Hσ Hτ

end Output
end YM.Comparison.RG02.Adjacent.Attach
