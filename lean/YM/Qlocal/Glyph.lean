import YM.Qlocal.Drink
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Bind
open Function Filter Set Metric Lattice MeasureTheory ProbabilityTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid
open AllOrder Ker Laplace Laplace.SigmaP Response Catch
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open Marker Multi PertExtension.Series Radial Extra.Iteration Floe PositionX.Jet
open Comparison.RG02.Order
open Comparison.RG02.Assembly
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge} {k j i q r:ℕ} {n c f :Side}{S:StepData c f} {b α t:ℝ}
open PertExtension PertExtension.Series Sienna Lantern Catch Catch.Clock tether
variable {ι:Type} [DecidableEq ι]{Z:Census ι}
open Extra.Trajectories Comparison.RG02.Cumulants
namespace Glyph
variable (l:Multi.Hot Z)
-- single permitted set (not necessarily one element), positive-degree.(Use linearity polarize arbitrary finite disjoint groups in the connected extractor)
local notation "Γ"=> l.val
local notation "W"=> PTable Z
@[simp]
lemma never : l.val ≠ Z.quiet:= (hot_iff_ne _).1 l.property
include l in
lemma inhabited_c : Nonempty ι:= by obtain ⟨x,hx⟩:= l.property; exact ⟨x⟩
section alg
variable {a b c : Word ℝ}
def wire (l: Multi.Hot Z)(a :Word ℝ):W:= PowerSeries.mk (fun i=> Poly.send l.val (↑(a i):ℂ))
@[simp] lemma wired (i:ℕ)(v:Z.Mode): ((PowerSeries.coeff i (wire l a))).part v= if v=l.val then ↑(a i) else 0:= by simp [wire]
lemma stamps : realCurve Z a * wire l b= wire l (Laplace.SigmaP.plus a b):= by
 ext n t; rw [PowerSeries.coeff_mul,Poly.part_sum]; simp_rw [realCoeff,wire,PowerSeries.coeff_mk,show ∀v y,(Poly.bead Z v) * Poly.send l.val y=Poly.send l.val (v*y) from fun v y=> tagged_mul _ _ _ ((Poly.vacuum Γ Γ).2 rfl) _ _,Poly.part_send]; split
 next he=> rw [Response.plus_sum, Complex.ofReal_sum]; simp
 next he=> simp
lemma nil : wire l a * wire l b=0:= by
 ext n t; rw [PowerSeries.coeff_mul,map_zero,Poly.part_nil, Poly.part_sum]; refine Finset.sum_eq_zero fun i hi=>?_ ; simp only [wire,PowerSeries.coeff_mk]
 rw [show (Poly.send Γ (↑(a i.1):ℂ))*(Poly.send Γ ↑(b i.2))=0 from ?_,Poly.part_nil]; by_contra hh; obtain ⟨z,hz⟩:= merges_of_tagged_mul hh; exact l.property.ne_empty (disjoint_self.mp hz.1)
-- Mark exp trailing coefficient analysis uses pointwise Ward.Basis.
variable [Fintype ι]
lemma shard : markExp (wire l a)=1+ wire l a:= by
 let f:= wire l a; have he(n:ℕ) : 2≤n→ f^n=0:= by intro hn; rw [show n=(n-2)+2 from (Nat.sub_add_cancel hn).symm,pow_add,pow_two,nil,mul_zero] -- f not unfold
 have ht: 0 < Fintype.card ι:= Fintype.card_pos_iff.mpr (inhabited_c l)
 unfold markExp; rw [← Finset.sum_subset (s₁:=range 2) (range_mono (by omega)) (fun i hi hh=> by rw [he _ (Nat.le_of_not_gt fun h=> hh (mem_range.mpr h)), smul_zero])]; rw [show (2:ℕ)=1+1 from rfl,Finset.sum_range_succ]; simp
lemma monochrome : (series Z k (wire l a)).part (Board Z k).quiet=0:= by rw [← Join.pair_quiet,polarization, wired,if_neg (never l|>.symm),mul_zero]
lemma bare : (bottom Z k) (series Z k (wire l a))=0:= by
 apply Join.both_parts; intro i j; rw [bottom_value,Poly.part_nil]; split; · rw [polarization,wired,if_neg (never l|>.symm),mul_zero]
 exact Eq.refl _
lemma passive : Poly.pass (series Z k (wire l a))=1+series Z k (wire l a):= by rw [← mark_exp (fun n=> ?_),shard,map_add,map_one]; rw [wired,if_neg (never l|>.symm)]
end alg
variable (R:reed G f)(X:Layout G)(A:Finset Age) (h:Legal A X) (hR:Flute R q)
open Comparison.RG02.Bulk
abbrev solo (q:ℕ): Colors Z G f:= {vac:=Binding.drawn X A f, power:=fun _=>q,mark:=fun i=> if i=l then fun x V=> (↑(R x V):ℂ) else fun _ _=>0 }
include h hR
local notation "L"=> solo l R X A q
lemma approved : (L).Standard:= by
 have he := Binding.planted X A (n:=f) h; constructor; constructor
 case suppose_vac=> exact he.lower (by decide)
 case suppose_mark=>
    let v:=Comparison.RG02.Bulk.projected R; intro i; unfold solo; dsimp only; split; rename_i hx; · exact GradeAt.linear_contact Complex.ofRealCLM hR.zeroAt
    exact GradeAt.grade_zero _
 case natural=> intro u t; exact (Binding.standard X A (Comparison.RG02.Bulk.Colors.noHole (V:=ι) G f Z) h (Comparison.RG02.Bulk.Colors.no_hole G f _|>.1)).1.natural u t
 case gauges=>
    intro i u; unfold solo; dsimp only; split; rename_i ht; · exact fun t v=> congr_arg Complex.ofReal (hR.byfield _ _ _)
    exact fun t v=>rfl
 case envelope=> exact fun t=>(Binding.standard X A (Comparison.RG02.Bulk.Colors.noHole (V:=ι) G f Z) h (Comparison.RG02.Bulk.Colors.no_hole _ _ _|>.1)).1.envelope t
 case prices=>
    intro i t; unfold solo; dsimp only; split; swap; · exact ⟨measurable_const,0,by simp⟩
    obtain ⟨c,hc⟩:= (hR.envelope t).cost; exact ⟨Complex.measurable_ofReal.comp (hR.envelope t).meas,c,fun u=> by simpa using hc u⟩
 case right=> exact he
end Glyph
end YM.Qlocal.Bind
