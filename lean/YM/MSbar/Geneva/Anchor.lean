import YM.MSbar.Geneva.Resources
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Geneva
open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film
open Measuring Cane Laurent Bloch UVNext.PricedKernels Spruce Lapaz Mosaic Issue
open Next.SectorChange Bulk Posture JetTab
variable {G:Gauge}{ι:Type}{X:ι→ℝ}{A:ι→BudgetPoint}{φ:Filter ι}(hX:Tendsto X φ atTop)
variable (P:Patch)(K:KernelChoices)(J:Voice G)
variable {α:ℝ}{n:ι→Side}(H:Stage)
variable (Q:(i:ι)→Rep G (n i)) (J:Voice G) (U:(i:ι)→Nesting G (n i)) (Z:G.ColorIndex) (k:ℕ)
local notation "F" i=> FaceValue H (X i) (Q i)
local notation "G!" i=> film (Q i) (U i) (cue (Q i).beta) k
variable (hp:∀ᶠ i in φ,(hatW (X i))^4≤(n i).val)(hv:∀ᶠ i in φ,FaceValue H (X i) (Q i))
variable (hT:∀ᶠ i in φ, (∃ g:ℝ → Config G (n i)→ℝ, Trend g (U i) (Q i).path (Q i).clip k)∧ Keeps (U i) k (sun G Z))
include hv hX
lemma cars : Run φ X (fun i=>cue (Q i).beta) (-(1/2))∧Run φ X (fun i=> (cue (Q i).beta)⁻¹) (1/2) ∧∀ᶠ i in φ,0<cue (Q i).beta ∧ cue (Q i).beta ≤ 4*cue (X i):=by
    let v(x):=cue (Q x).beta; have he:∀ᶠ i in φ, lensT (X i) (v i):= (hv.and (hX.eventually_gt_atTop 0)).mono fun i h=> Mosaic.ever h.2 h.1.beta h.1.upper
    exact ⟨charges hX he|>.1,charges hX he|>.2,(cuff hX he|>.and he).mono fun i h=> ⟨h.1,h.2.2.trans (by have hx:= h.1.trans_le h.2.2; linarith)⟩⟩
include P K
lemma peggy (p:ℕ) : Run φ X (fun i=> earnE (Q i).p G p) (1/2*(p:ℝ)):=by
    obtain ⟨-,hp'⟩:=melody hX P K G; have hh:Run φ X (fun i=>((Q i).p.threshold^p)⁻¹) (1/2*(p:ℝ)):=by simp_rw [← inv_pow]; exact (Run.raise hX (hp'.1.alter (g:=fun i=>(Q i).p.threshold⁻¹) (hv.mono (fun i hi=>by dsimp only; rw [hi.threshold]))) p);
    exact (Run.mulY hX (Run.mulK hX (Run.mulK hX hh (deed p)) (p.factorial:ℝ)) _)
variable (h:G.Simple)(hJ:Clear G J)
include hp hT h hJ
lemma anchors : ∃ c:ι→ℝ, Van φ X c ∧∀ᶠ i in φ,|stackH (n i) (sun G Z) (rim (G! i))| ≤ c i:=by
     let a:= H.width; let z(i):=lag (n i) (X i); let v(i):= cue (Q i).beta
     let P'(i):= Bristol.prestige (sun G Z) (Q i) (v i) (lbt (X i)) H.width (ability (X i)) (lag (n i) (X i)) (lag (n i) (X i)); obtain ⟨hv1,-,hv2⟩:= cars hX H Q hv
     obtain ⟨hz,hz'⟩:= cone hX hp _ H.width_pos; obtain ⟨hp0,hp1⟩:= cone hX hp _ H.price_pos
     obtain ⟨-,-,he,hD⟩:= melody hX P K G
     refine ⟨P',?_,?_⟩
     · let Cv(i):= Midpoint.url (n i) (z i) a; have hc : Van φ X Cv:=by
           intro b; have h :Run φ X (fun i=>16*(Midpoint.size (n i)*Real.exp (-a*↑(z i)))+2*Real.exp (-a*↑(z i))) b:=Run.addR hX (Run.mulK hX (hz b) _) (Run.mulK hX (hz' b) _); exact h.alter (Eventually.of_forall fun i=>by unfold Cv Midpoint.url; ring)
       let B(i):= Midpoint.brim (n i) (Q i).p G (z i); have ht := peggy hX P K H Q hv 2 -- order
       have hB:Van φ X B:=by intro s; have he:=(Van.mulL hX ht hp0 s); refine he.alter ?_; filter_upwards [hv] with i hi; unfold B Midpoint.brim; rw [hi.support]; ring
       have hc0: Van φ X (fun i=> 2*lbt (X i)*Cv i+B i * ability (X i)):= by intro s; exact (Run.Ycost hX (Run.mulK hX (Run.mulK hX he 2) 2) (hc s)).addR hX (Van.mulL hX hD hB s)
       intro s; let y(i):= 2*lbt (X i)*Cv i+B i*ability (X i); refine Run.loosen ((Run.raise hX hv1 2).mulR hX (hc0 s)) (by linarith)
     have he:= hv.mono (fun i h=> h.threshold); filter_upwards [quell hX hp, hv,hT, (Geneva.sizeF (Tx:=v) hX (fun i=>(Q i).p) J hJ n he hv2),hv2] with i hN he ⟨⟨S,hS⟩,hh⟩ hs ht
     refine Bristol.farther (Q i) (U i) Z hS hh ht.1 (hx:=isOpen_ball) (Ω:=Metric.ball 0 (2*v i*hull (X i))) (convex_ball ..) (Metric.mem_ball_self hs.1) hs.2.2 h ?_ hN.1 he.lawful he.size.le hN.2
     have hv':0 < (Q i).beta:= lt_of_lt_of_le (half_pos (zero_lt_one.trans he.enough)) he.beta; unfold cue; rw [inv_pow,Real.sq_sqrt hv'.le,mul_inv_cancel₀ hv'.ne']
end YM.MSbar.Geneva
