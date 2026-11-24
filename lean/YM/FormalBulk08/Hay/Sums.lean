import YM.FormalBulk08.Hay.Matrix

/-! t,N unaffected. Taking supplied `FiniteBound` on increasing actual SIDE. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Hay
open Filter Set Function MeasureTheory Lattice RG Exterior Wilson Precision Tree Work.F05
open Stationary hiding shine Rays
open Reef Series Wick Jets Orb Plait PowerSeries Lava Mesa Broc City Cork Lotus Shore Gorge Laurent Bloch Flat Next.Free
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{c f n:Side}{S:StepData c f}(F:Forest S.ratio){p q:Clip}{R U:PathData G}{σ α γ Γ Λ B C:ℝ}{r c':ℝ}
variable {d t j :ℕ}
lemma tolling {m:ℕ→Side}(h:Tendsto m atTop atTop)(hx:0<γ)(G:Gauge)(A:ℝ) :
      Tendsto (fun i=>skyL G (m i) * (Fintype.card (Site (m i))*A* Real.exp (-γ*(m i).val))) atTop (𝓝 0):= by
   have ht:=tendsto_natCast_atTop_atTop (R:=ℝ) |>.comp (North.highlim.comp h); let K:ℝ:= A* ((Fintype.card (Loc G 1):ℝ)^2);let L i:=(m i).val
   have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (↑(12:ℕ)) γ hx).comp ht
   have he:Tendsto (fun i=> (L i:ℝ)^12*Real.exp (-γ*(L i:ℝ))) atTop (𝓝 0):= by simpa only [Function.comp_def, Real.rpow_natCast] using! ht
   refine (show Tendsto (fun i=> K*((L i:ℝ)^12*Real.exp (-γ*(L i:ℝ)))) atTop _ from (by simpa using he.const_mul K)).congr' (.of_forall fun i=>?_)
   dsimp only; rw [sky_value]; have hq:(Fintype.card (Site (m i)):ℝ)= (L i:ℝ)^4:=by simp [Site,Per,ZMod.card,Four,Axis,L]
   rw [hq]; unfold L K; ring
lemma cardBeam (n:Side)(f g:Bid.Dir G n→ℝ)(h:SameJet j f g): coeff j (paste (f ∘ arm G n 1))=coeff j (paste (g∘ arm G n 1)):= by
   rw [←beam_price,←beam_price]; apply congr_arg;ext v; unfold Broc.beam Tensor.coeff; simp only [_root_.smul_apply]; let Q:= (arm G n 1).toContinuousLinearMap; rw [show iteratedFDeriv ℝ j (f∘ (arm G n 1)) 0 _= _ from wired Q (by rw [map_zero];exact h.1.analyticAt) j _,show iteratedFDeriv ℝ j (g ∘ (arm G n 1)) 0 _= _ from wired Q (by rw [map_zero]; exact h.2.1.analyticAt) j _, map_zero,h.2.2]
-- `Through` Hanna
variable {J V:Type*}[Fintype V][Fintype J][DecidableEq V]
omit [Fintype J] in lemma out_change (T:Hull V J)(p q:Pap (V⊕J))(h:Solved T p)(hp:Through t p q): Through t (out T p) (out T q) := by
    have hx:Through t (positive T p) (positive T q):= ((Through.change_congr _ hp).sub (Through.exact_eq _ _)).sub (Through.exact_eq _ _)
    exact Through.add (Through.exact_eq _ _) (Through.cove_congr (beam_through (Orb.variation T.saddle J).call (hx.expan_congr (plur T p h))) (voice T p h))
lemma from_acc (t:ℕ){p q: Pap (wire G f)}(h:Through t p q)(A:ChartRatio G)(x:S.Choices): Through t (flush F x A p) (flush F x A q) := by
    unfold flush;exact (Through.change_congr _ ((h.map_left _).sub (Through.exact_eq _ _))).add (Through.exact_eq _ _)
-- jets tree
variable {K: KernelChoices} (P:Flight j t)(T:Lodge P.patch) (c: Side) (Z:ChartRatio G)(hZ:P.patch.Branches K G)(ht:4≤t)
local notation "S'"=>primary P.patch K c
variable (b:(primary P.patch K c).Choices)
variable (W:Pot G)(hp:Story W (pink K.penalty P.wing))
  (h:R.Bounds p σ B C) (Y:Bid.Dir G c→AxisChart G (Reef.floor K P T c))
   -- need F S' annotation
  (hy:Critical (S:=primary P.patch K c) (Reef.floor K P T c) p R Y)(hw:Through 2 (stone W _) (novel p R (c*P.patch.L)))(hG:G.Simple)(hz:LocalRatio Z)
include hp h hZ hy hw hG hz ht
lemma ready :
    let a:=landed P Z hZ T c b (stone W _); let X:=victory (S:=primary P.patch K c) (Reef.floor K P T c) b p R Y; let z:= Precision.thermal (S:=primary P.patch K c) (Reef.floor K P T c) b p R Y Z ∘ Stationary.arm G c 1
    coeff 0 a= -coeff 2 (paste X) ∧
     MvPolynomial.homogeneousComponent 3 (coeff 1 a) = -coeff 3 (paste X) ∧ MvPolynomial.homogeneousComponent 4 (coeff 2 a) = -coeff 4 (paste X) ∧ MvPolynomial.homogeneousComponent 2 (coeff 2 a) = -coeff 2 (paste z) := by
    let S:=primary P.patch K c;let V:=ferry P hZ T c; let f:=Reef.floor K P T c; let c':=c*P.patch.L
    let p':=stone W c'; let q':=novel p R c'
    obtain ⟨v,x,hs,hc,hX,-⟩:= colors G K.penalty K.penalty_pos P.legal
    have hA : coeff 0 p' = crunch (kernelP G K.penalty P.wing _) := stoned_main hs.le hc.le (hX _).1 hp.toVivid hp.ink _
    have hP : Solved V (flush f b Z p') := consolidate P Z hZ T c hz b _ hA ht
    have hv : Through 2 (out V (flush f b Z p')) (out V (flush f b Z q')):= out_change _ _ _ hP (from_acc f 2 hw Z b)
    intro a x y; rw [show coeff 0 a=_ from hv 0 (by omega),show coeff 1 a=_ from hv 1 (by omega), show coeff 2 a=_ from hv 2 (by omega)]
    exact rung f b p R Z Y hy hz V hG hZ h (consolidate P Z hZ T c hz b _ ((hw 0 (by omega)).symm.trans hA) ht) (honey P hZ T c).1.det_pos
end YM.FormalBulk08.Hay
