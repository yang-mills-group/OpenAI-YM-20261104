import YM.MS.ScaleForest.SternGroup
import YM.MS.ScaleForest.RoseBridge

/-!
# Applying Wick and the actual pole to horizontal ports

Do it in all `m`. For the positions kernel later, use this with
`D₀` the legitimate specialization of THE QUOTIENT NUMERATOR ALONE
(not of a meromorphic product). -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.Beamline
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Halo
open Lattice Momentum Tone Detect Osc Fiddle XSpace XSpace.Chiral Cylinder Quadratic
open scoped Topology ContDiff
variable {G : Gauge} {I : Type} {m:ℕ}

abbrev Shaft (G:Gauge)(m:ℕ) := G.ColorIndex × L m
abbrev rod (i:Shaft G m) := at_g i.2 i.1
abbrev armI (i:Shaft G m)(p:SectorP m) : Shore G m := (rod i,p)
abbrev aim (F:Mob G)(p q:SectorP m)(i j:Shaft G m) := F m [armI i p,armI j q]
abbrev allA (F:Cfield G m→ℂ) := ∑ i:Shaft G m,F (rod i)

def stableA (p:SectorP m) (f:Shaft G m→ℂ) : Prop:= ∀ a:G.ColorIndex, ∑ i:L m,(p i:ℂ)* f (a,i)=0
lemma stableA.mirror {p:SectorP m}{f:Shaft G m→ℂ}(h: stableA p f): stableA (-p) f := fun i=> by simp [h i]

structure Radiant (K: Rip G) (p:SectorP m) (d:ℂ) : Prop where
    solo (i j:Cfield G m)(h:K m i j p ≠ 0): (∃ i':Shaft G m,i=rod i')∧ ∃ j':Shaft G m,j=rod j'
    swap (i j:Shaft G m): K m (rod i) (rod j) p=K m (rod j) (rod i) p
    focus (i:Shaft G m) (f:Shaft G m→ℂ)(h:stableA p f): ∑ j:Shaft G m,2*K m (rod i) (rod j) p * f j=d*f i
lemma Radiant.all {K : Rip G}{p:SectorP m}{d:ℂ} (h:Radiant K p d) (F : Cfield G m→ Cfield G m→ℂ)
    (ht:∀ i j,K m i j p=0→ F i j=0) : ∑ i,∑ j,F i j = ∑ i:Shaft G m,∑ j:Shaft G m,F (rod i) (rod j) := by
    rw [onlyAs]; swap; · intro i hi; refine Finset.sum_eq_zero fun j _=> ht i j (by by_contra hp; obtain ⟨ k,hK⟩:= (h.solo _ _ hp).1; exact hi _ _ hK)
    have he(i:Shaft G m): ∑ j,F (rod i) j=∑ j:Shaft G m, F (rod i) (rod j):= by
       rw [onlyAs,Fintype.sum_prod_type]; exact fun j hj=> ht _ j (by by_contra hp; obtain ⟨ k,hK⟩:= (h.solo _ _ hp).2; exact hj _ _ hK)
    rw [Fintype.sum_prod_type]; exact Finset.sum_congr rfl (fun i _=> Finset.sum_congr rfl (fun j _=> he (i,j)))

-- multipliers for half line API (but already **factor 2 included** at this port)
abbrev cleanP (G:Gauge) (s:ℝ): Rip G := pickLine false (halfP G (exp s))
abbrev cleanJet (G:Gauge) (s:ℝ): Rip G:= pickLine false (A0 G s)
def evenPart (p: SectorP m) (s:ℝ) : ℂ:= (( (1 - low (exp s) p)/p.sq:ℝ):ℂ)
def shining (p:SectorP m) (s:ℝ) : ℂ:= ((2*exp s * City.brush (exp s) p * p.sq:ℝ):ℂ)
theorem even_jet (p:SectorP m)(s:ℝ) : HasDerivAt (evenPart p) (shining p s) s:= by
   have h (t:ℝ) := City.xH (exp t) p; 

   convert! ((((h s).comp s (hasDerivAt_exp s)).const_sub 1).div_const p.sq).ofReal_comp using 1;
   apply congr_arg Complex.ofReal; by_cases he:p.sq=0 <;> first | (solve|simp [he]) |  (field_simp)

lemma even_parity (p:SectorP m)(s:ℝ): evenPart (-p) s= evenPart p s:= by simp only [evenPart,Swirl.Near.lown,sq_neg]
lemma shine_parity (p:SectorP m)(s:ℝ): shining (-p) s=shining p s:= by simp [shining, City.brush]
lemma even_gone (p:SectorP m): Tendsto (evenPart p) atBot (𝓝 0) := by
    let f(t:ℝ):ℂ:= (( (1-(1+t^2*p.sq)*exp (-(t^2*p.sq)) ) / p.sq:ℝ):ℂ); have hc : Continuous f:= by unfold f; fun_prop
    obtain ht:= hc.continuousAt.tendsto.comp tendsto_exp_atBot
    rw [ show evenPart p=f ∘ Real.exp from funext fun t=>by unfold evenPart; rw [Swirl.Near.lown]; rfl ]; simpa [f] using ht

-- single glyph proof, no color assumption required
private def beamMat (p:SectorP m)(η χ:ℂ)(i j:Shaft G m): ℂ:= if i.1=j.1 then
   η * ( precision i.2 j.2 p : ℂ) + χ * (p i.2 : ℂ)*(p j.2:ℂ) else 0
private lemma beam_swap (p:SectorP m)(η χ:ℂ)(i j:Shaft G m): beamMat p η χ i j=beamMat p η χ j i:= by
   unfold beamMat; rw [show ∀ i j:L m, precision i j p=precision j i p from fun i j=>by simp [precision, Landau.delta, eq_comm,mul_comm] ]; split_ifs <;> first|(solve| tauto)| ring
lemma cleanM (p:SectorP m)(η χ:ℂ)(i:Shaft G m)(f:Shaft G m→ℂ)(h:stableA p f): (∑ j:Shaft G m,beamMat p η χ i j*f j) = η*p.sq*f i:= by
   rcases i with ⟨a,j⟩; rw [ Fintype.sum_prod_type ]; rw [Finset.sum_eq_single a];
   · simp only [beamMat,if_true]; unfold precision Landau.delta; simp only [Complex.ofReal_sub, Complex.ofReal_mul,mul_sub, sub_mul,add_mul,Finset.sum_sub_distrib,Finset.sum_add_distrib]; simp only [ (show ∀ y z :ℂ,∀ i:L m, y * (z * (p i:ℂ))*f (a,i)= (y*z)*((p i:ℂ)*f (a,i)) from fun y z i=>by ring),mul_assoc, ← Finset.mul_sum,h a,mul_zero ]; simp [apply_ite,ite_mul]
   · intro b _ h; simp [beamMat,Ne.symm h]
   simp

def Coupling (G:Gauge) := (G.casimir:ℂ)*TwoPoint.counterScale
-- actual color sign and R normalization
theorem poleMat (g:G.Simple)(p:SectorP m)(i j:Shaft G m) :
    aim (TwoPoint.poleTensor G true true) (-p) p i j = beamMat p (Coupling G) (3*Coupling G) i j := by
    rw [show aim _ (-p) p i j= _ from (show _=TwoPoint.kinetic _ i.1 j.1 (-p) i.2 j.2 from ?_),TwoPoint.ghost_bill]; swap; · change _= aim _ (-p) (- -p) i j; rw [neg_neg]
    unfold TwoPoint.ghost_residue TwoPoint.traceAd; rw [ sums_angles g ]; unfold beamMat Coupling precision Landau.delta; split_ifs <;> push_cast <;> simp only [Pi.neg_apply,Complex.ofReal_neg,sq_neg] <;> ring

lemma PoleAction (g:G.Simple)(p:SectorP m)(i:Shaft G m) (f:Shaft G m→ℂ)(h:stableA p f):
    (∑ j:Shaft G m, aim (TwoPoint.poleTensor G true true) (-p) p j i*f j)=Coupling G*p.sq*f i := by
    simp_rw [poleMat g,show ∀ j:Shaft G m,beamMat p (Coupling G) (3*Coupling G) j i = beamMat p _ _ i j from fun j=> beam_swap .. ]; exact cleanM _ _ _ i f h

private def metricFull (p:SectorP m)(s:ℝ) : ℂ:= ((((1-low (exp s) p)/p.sq^2:ℝ)):ℂ)
private def metricJet (p:SectorP m)(s:ℝ) : ℂ:= ((2*exp s* City.brush (exp s) p:ℝ):ℂ)

private lemma cleanMShell (p:SectorP m)(s:ℝ)(i j:Shaft G m): 2*(cleanP G s) m (rod i) (rod j) p= beamMat p (metricFull p s) 0 i j:= by
    unfold cleanP pickLine; rw [if_pos (show parity (rod i)=false from rfl),halfP_components]; unfold Landau.choir; dsimp only [id,rod,at_g]; unfold beamMat metricFull; rw [Swirl.Near.lown]; by_cases he:i.1=j.1 <;> simp [he,Swirl.Near.Tail]; ring

private lemma cleanMJet (p:SectorP m)(s:ℝ)(i j:Shaft G m): 2*(cleanJet G s) m (rod i) (rod j) p= beamMat p (metricJet p s) 0 i j:= by
    unfold cleanJet pickLine; rw [if_pos (show parity (rod i)=false from rfl), radial_log ]; unfold beamMat radial City.LegsK Landau.choir metricJet; split_ifs <;> simp_all [rod,at_g,City.L0] ; ring

-- zero on every other species (B channel even, but not paired)
private lemma reachJet (p:SectorP m)(s:ℝ)(i j:Cfield G m)(h:(cleanJet G s) m i j p≠0): (∃ i':Shaft G m,i=rod i')∧ ∃ j':Shaft G m,j=rod j' := by
   unfold cleanJet pickLine at h; split at h; next h₁=>
      rw [radial_log] at h; rcases i with ⟨⟨_|x,_|_⟩,a⟩ <;> rcases j with ⟨⟨_|y,_|_⟩,b⟩ <;> first| exact ⟨ ⟨ (a,x),rfl⟩,⟨(b,y),rfl⟩⟩ | (solve|simp [parity,Landau.p] at h₁)| (simp [radial, City.LegsK,Landau.choir,City.L0] at h)
   contradiction
private lemma reachFull (p:SectorP m)(s:ℝ)(i j:Cfield G m)(h:(cleanP G s) m i j p≠0): (∃ i':Shaft G m,i=rod i')∧ ∃ j':Shaft G m,j=rod j' := by
   unfold cleanP pickLine at h; split at h; next h₁=>
      rcases i with ⟨⟨_|x,_|_⟩,a⟩ <;> rcases j with ⟨⟨_|y,_|_⟩,b⟩ <;> first| exact ⟨ ⟨ (a,x),rfl⟩,⟨(b,y),rfl⟩⟩ | (solve|simp [parity, Landau.p] at h₁) | (simp [halfP,Landau.choir,Swirl.Near.Fuel,Swirl.Near.Tail] at h)
   contradiction

lemma shell_act (p:SectorP m)(s:ℝ): Radiant (cleanP G s) p (evenPart p s) := by
   refine ⟨ reachFull _ _,fun i j=> mul_left_cancel₀ (a:=(2:ℂ)) (by norm_num) (Eq.trans (cleanMShell p s i j) ((beam_swap ..).trans (cleanMShell p s j i).symm)),fun i f h=>?_⟩;
   simp_rw [cleanMShell,cleanM p (metricFull p s) 0 i f h]; unfold metricFull evenPart; by_cases he:p.sq=0; · simp [he]
   have ht:(↑p.sq:ℂ)≠0:= by exact_mod_cast he
   push_cast; field_simp
lemma jet_act (p:SectorP m)(s:ℝ): Radiant (cleanJet G s) p (shining p s) := by
   refine ⟨ reachJet _ _,fun i j=> mul_left_cancel₀ (a:=(2:ℂ)) (by norm_num) (Eq.trans (cleanMJet p s i j) ((beam_swap ..).trans (cleanMJet p s j i).symm)),fun i f h=>?_⟩; simp_rw [cleanMJet,cleanM p (metricJet p s) 0 i f h]; unfold metricJet shining; push_cast; rfl

end YM.MS.ScaleForest.Beamline
