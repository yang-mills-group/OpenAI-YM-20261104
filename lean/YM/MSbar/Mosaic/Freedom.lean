import YM.MSbar.Mosaic.Extract
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Mosaic
open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Bakery.Film
open Measuring Cane Laurent Bloch UVNext.PricedKernels Spruce Lapaz
open Next.SectorChange Bulk Posture
variable {G:Gauge}
namespace Issue
variable {ι:Type}{X μ f' g:ι→ℝ}{A:ι→Issue G}{φ:Filter ι}[φ.NeBot] (hX:Tendsto X φ atTop) (χ:ChartRatio G)(J:Voice G)(H H':Stage)(K:Patch)(D:KernelChoices)
variable (hG:G.Simple) (hD:K.Branches D G)(hQ: Clear G J)(hχ:LocalRatio χ)
local notation "α'" i=> tip G K.L (X i)
local notation "Y"=> fun i:ι=> tip G K.L (X i)
local notation "w!" i=> (vol (tip G K.L (X i)))
local notation "N" i=> A i
local notation "f" i=> (A i).f
local notation "c" i=> (A i).c
variable (hp:∀ᶠ i in φ,Paid (A i) K H H' J (X i)) (hq:∀ᶠ i in φ,(A i).S.kernel=D)
variable (W:(i:ι)→Positions (Primary (A i).c G))(hW:∀ᶠ i in φ,‖W i‖ ≤ hull (X i))
variable (z:(i:ι)→Site (A i).f) 
local notation "X₀" i=> boxX (tip G K.L (X i)) (z i)
local notation "W₁" i=>(A i).fClock • W i
local notation "X₁" i=> boxY (tip G K.L (X i)) (z i)
local notation "L!" i=> (A i).F
local notation "ϑ!" i=> (A i).v
local notation "t!" i=> (A i).fClock
variable {p m k q:ℕ}(hk:3≤ k)
local notation "Π'"=>αm
-- obtain Tin bounds at arbitrary curvature small after.
lemma sunk {φ:Type}[Fintype φ][DecidableEq φ]{A:Pot φ}{k n:ℕ}{D K T v w:ℝ}{s:Side}{l:φ→Site s}(h: Tokew l v m k 0 A D)(hp: w≤v)(hu:0≤w)(hq:p ≤ m): Tokew l w p k 0 A D:=by
    obtain ⟨hd,h⟩:= h.soft hp hu; refine ⟨hd,fun i=> ⟨hd,fun j hj=>le_trans ?_ ((h i).2 j hj)⟩⟩; apply shiny; intro v _; unfold Whisk.rate Whisk.spread liftW -- name
    gcongr; simp
-- cane tilt shrink JetTab
lemma shiftJ {φ:Type}[Fintype φ]{T:View φ→ℝ}{k n:ℕ}{D v w X0:ℝ}{s:Side}{S:Set (View φ)}{l:φ→ Site s}(h:JetTab l v p X0 S T k D)(hp:w≤ v)(hv:0≤w)(hh:q ≤ p): JetTab l w q X0 S T k D:=by
    obtain ⟨ha,Fz,hg,hF⟩:= h; refine ⟨ha,Fz,hg,fun i=> ?_⟩; refine le_trans ?_ (hF i); apply shiny; intro L hL; apply mul_le_mul_of_nonneg_left _ (hg _ (by rw [List.length_cons,hL])|>.1); unfold swipe Whisk.spread liftW; gcongr; simp
variable (M:StageCost)(i':G.ColorIndex){s e ν b:ℝ}(hc:∀ᶠ i in φ,Festival (A i) χ p i' ∧ ClockD (A i) p m M.s (X i)∧ Cs (A i) χ M.s p m (X i) i' (f' i) b ∧ Issue.Receipt (A i) M (X i))
include hX hG hp hc
variable (hh:p+2 ≤ m)
noncomputable def tangle (x h b:ℝ)(p:ℕ):=Alto.purse Alto.Dean h p+h^2*b
lemma server (hh':p+2≤ m) (ha: Run φ X f' 0): let Q:=M; ∃ g:ι→ℝ, Run φ X g 0∧∀ᶠ i in φ,
           let R:= A i; let b:=Alto.cWidth (R.passage (X i)); let y:=Alto.cWidth (X i)
           ∀ j≤p, (Tokew (Measuring.chart R.f G) b M.s m 0 (PowerSeries.coeff j R.T) (g i) ∧ Tokew (Measuring.chart R.f G) b M.s m 0 (PowerSeries.coeff j (tariff R.f p R.pre.clip R.pre.path R.T)) (g i)) ∧ (Tokew (Measuring.chart R.c G) y M.s m 0 (PowerSeries.coeff j (R.color χ)) (g i) ∧ Tokew (Measuring.chart R.c G) y M.s m 0 (PowerSeries.coeff j (tariff R.c p R.post.clip R.post.path (R.color χ))) (g i)):=by
           intro Q; let u:=Y; let w:=fun i=>hatW (X i); let v:=fun i=>hatW (u i); have hu:= (Work.E09.betaF_growth G K.L).comp hX; let p'(i):= Alto.purse Alto.Dean (v i) p; let a(i):= p' i+(v i)^2*b; let k(i):=f' i+(w i)^2*b
           have hr: Run φ X v 0:=(Run.wander hX G hG K.L _ _).2 (Run.stanza hu); have hPo:Run φ X p' 0:=hr.Ypow hX _
           refine ⟨a+k,Run.addR hX (hPo.addR hX ((hr.Ypow hX _).mulY hX _)) (ha.addR hX (((Run.stanza hX).Ypow hX _).mulY hX _)),?_⟩
           filter_upwards [hp,hc,(Alto.broad.comp hX).eventually_ge_atTop 1,(Alto.broad.comp hu).eventually_ge_atTop 1] with i he ⟨h,hQ,hC,hV⟩ hw hv; have hu0:(A i).passage (X i)=u i:=by unfold passage; rw [he.space]
           intro R α y j hj; let x:=v i; let z:=w i; let B(i:ℝ):=i^2*b; let v0:= p' i; have hξ:0<x:=zero_lt_one.trans_le hv; have hY:0<z:=zero_lt_one.trans_le hw; let J:=fun u=>Alto.purse Alto.Dean x u; have he:=hQ.paths j hj; have hm:= hC.top; have hN:=hC.pre_; unfold α R; rw [hu0] at he hN ⊢ -- replaces shadow.Y.n.Program
           have ht:Tin (Measuring.chart R.f G) _ M.s m x (PowerSeries.coeff j R.T) v0:= he.it hξ (pow_le_pow_right₀ hv (Alto.ranked hj)) le_rfl -- `simp` shadow
           have hg:0≤ B z:=hm.dec; have hl:0≤ B x:= hN.dec; have hZ := hC.oak j hj; let U:= PowerSeries.coeff j (R.color χ)
           let y0:= X i; have hX':0 ≤ k i:=add_nonneg hZ.dec hg; have hf:0≤ a i:=add_nonneg ht.dec hl
           have hP := h.preT; have hF:= hP.choose_spec.plane.profile j hj; have hz0:= h.postC.choose_spec.plane.profile j hj
           exact ⟨⟨(Tin.weightTok hξ hv ht).delta le_rfl (le_trans (le_add_of_nonneg_right hl) (le_add_of_nonneg_right hX')), (Ruby.stopP R.pre R.T M.s hv ht (by unfold R; omega) hN).delta le_rfl (le_add_of_nonneg_right hX')⟩, ⟨(Tin.weightTok hY hw hZ).delta le_rfl (le_trans (le_add_of_nonneg_right hg) (le_add_of_nonneg_left hf)), (Ruby.stopP R.post (R.color χ) M.s hw hZ (by unfold R; omega) hm).delta le_rfl (le_add_of_nonneg_left hf)⟩⟩
end Issue
end YM.MSbar.Mosaic
