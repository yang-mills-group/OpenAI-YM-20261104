import YM.OPE.Compatible.Straws.Cake
/-!
# Gauged parameterized fiber integration. No borrowed hypotheses
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision Cascade Cascade.Pilot Arc Adhesion Flock Coin
open Radial ScriptJ JetS
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E] [BorelSpace E]
variable {D I:Type}[Fintype D][Fintype I]{G:Gauge}
local notation "Lf" => Tested.germ
local notation "Y!" => Keys G I
local notation "K!" => Keys G (D ⊕ I)
local notation "U!" => Keys G D
local notation "BL" => prL (Equiv.refl (D ⊕ I)) G
local notation "BR" => prR (Equiv.refl (D ⊕ I)) G
namespace Fiber
open Stranded Shift Glass Score
variable {J V:Type}[Fintype J][Fintype V]
variable {F:Fiber (Keys G J) G I}{M:Score J V}{Y:Score I V} {X T:Path (Keys G J) G D}{Ω:Dimes G (D⊕I) (D⊕I)} {g:Keys G D→Tile G V} {q:ScriptJ (Keys G J×Keys G I)}
omit [Fintype V] in
lemma curler (hp:q.B)(x:ℝ→Keys G (D ⊕ I))(hx: Gael x):
      let f(i:ℝ):=q (i⁻¹ • Spine T (i • x i))
      (jur f-jur (Caul T q ∘ x))=O[Lf](gradeP 3):=by
         intro f; obtain ⟨p,h⟩:= Pawn.amplified _ (SpineJet (I:=I) T) (SpineBlew T) q hp; rw [show Caul T q=p from funext fun i=> Gael.chooses (h.stale i)]; exact Gael.rut (u:=x) (Gael.oath hx).limit h
omit [Fintype V] in
lemma pollster (P':Crave (M:=M) (Y:=Y) X T Ω g)(he:Creative q M Y): Ω.pulse (Caul X q) (Caul T q):=by
    intro x; let v:= Spine (I:=I) X ∘ σray x; let A:ℝ→ K!:= Ω.gradient ∘ σray x; let u:= Spine T ∘ A; let P(t:ℝ):=q (t⁻¹ • u t); let Q(t:ℝ):=q (t⁻¹ • v t); let K(t:ℝ):=t⁻¹ • A t
    have hV: (jur Q-jur P)=O[Lf](gradeP 3):= he.book (craving P' x); let k':= Caul X q x; have ht: ContDiffAt ℝ ∞ (σray x) 0:= contDiffAt_id.smul contDiffAt_const
    have hv0:(σray x (0:ℝ))=0:=zero_smul ..; have hd:Reads (jur Q) k':=Gael.oath ( Gael.start q he.wise (Gael.walk v ((show ContDiffAt ℝ ∞ (Spine X (I:=I)) (σray x 0) from hv0.symm ▸ SpineJet X).comp (f:=σray x) 0 ht) (by unfold v; rw [Function.comp_apply,hv0,SpineBlew])))
    have hp := hd.clash hV; have hx:Gael K:= Gael.walk A ((show ContDiffAt ℝ ∞ Ω.gradient (σray x 0) from hv0.symm ▸ Ω.gradC).comp (f:=σray x) _ ht) (by rw [show A 0= _ from (show A 0=Ω.gradient (σray x 0) from rfl),hv0,Ω.grad0]); apply hp.clash
    apply (curler (T:=T) he.wise K hx).congr' _ EventuallyEq.rfl; filter_upwards [Tested.eventually_pos] with i (hi:0 < i); change (q (i⁻¹ • Spine T (i • (i⁻¹ • _)))).atK i-_=(P i).atK _-_; rw [smul_inv_smul₀ hi.ne'];rfl
-- Append extension
variable {P:ChartRatio G}(R:LocalRatio P)
include R
lemma ArchRise (H:Pursue F M Y)(a: Keys G D)(s:Keys G D→L[ℝ] ℝ)(hs:s a=1)(hp:Creative q M Y): M.Marbles (F.predicts P q):=by
     refine ⟨predictB R _ hp.wise,fun {x y t} he=>?_⟩; obtain ⟨X,hX⟩:= extStay (s:=s) he.hX he.gx; obtain ⟨T,hT⟩:= extStay (s:=s) he.hY he.gy; let k:= t ∘ s; have ht(i):ContDiffAt ℝ ∞ (fun x:U!=>G.mat (k x i)) 0:=((show ContDiffAt ℝ ∞ _ (s 0) from s.map_zero.symm ▸ he.chart i)).comp (g:=fun x=>G.mat (t x i)) (f:=s) 0 s.contDiff.contDiffAt
     have hh : ∀ᶠ i:U! in 𝓝 0, M.dress (k i) (put (X.A i))= put (T.A i):= by
          filter_upwards [hX,hT, (show Tendsto s (𝓝 0) (𝓝 0) from s.map_zero ▸ s.continuous.tendsto 0).eventually he.law] with i hx hy h; rw [hx,hy]; exact h
     have he0:Y.dress (k 0) 1 =1:= H.bud _ (by have he: M.dress (k 0) (put (X.A 0))= put (T.A 0):= Filter.EventuallyEq.eq_of_nhds (show (fun i=> M.dress (k i) (put (X.A i)))=ᶠ[𝓝 0] fun i=>put (T.A i) from hh); simpa only [X.ha,T.ha,put_zero] using he)
     obtain ⟨Ω,hsΩ⟩:= spar Y k ht he0 -- parser?
     have hr:Crave (M:=M) (Y:=Y) X T Ω k:=⟨hsΩ,hh,ht⟩; obtain ⟨b,⟨W⟩,⟨B⟩⟩:= ((restores F X).and (restores F T)).exists
     apply (W.Saga B R (earn hr H) q q hp.wise hp.wise (pollster hr hp) a).congr' _ EventuallyEq.rfl; have hx:Tendsto (fun t:ℝ=>t•a) Lf (𝓝 0):=by simpa only [ContinuousWithinAt,zero_smul] using! (show Continuous (fun t:ℝ=>t•a) from continuous_id.smul continuous_const).continuousAt.continuousWithinAt (x:=0) (s:=Set.Ioi 0)
     filter_upwards [hx.eventually hX,hx.eventually hT] with z hz hy; change (F.predicts P q (z⁻¹ • X.A (z • a))).atK z-(F.predicts P q (z⁻¹ • T.A (z • a))).atK z=_; rw [hz,hy,Function.comp_apply, Function.comp_apply,map_smul,hs,smul_eq_mul,mul_one]
end Fiber
end YM.OPE.Libra
