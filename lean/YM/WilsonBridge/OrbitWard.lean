import YM.WilsonBridge.Position

/-!
# Exact finite based-gauge master on the Wilson inversion quotient

No gauge-frame, Taylor-matching or scaling hypotheses. Actual log coordinate Wilson
energy with the half multiplicity on the ordinary torus, Haar and quotient gauge. The
interpretation (reflected equivariance) uses even side though some formulas below
hold more generally. No ∆ on fixed-site antifield weights from halving the Jacobian!
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge.Based.Position
open PertExtension Orb
open MS Native Bare Focus Koszul Lattice Filter Function Finset
open MS.Book Book.Convolve Cylinder Cylinder.Taylor FreeBV
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

local notation "τφ" => Position.Parity G n
local notation "β" => Position.Bracket G n

def array (F:E G n) : Wilson.Config G n:= liftLinks (G.lieExp ∘ F)
lemma array_full (F:E G n) : array F=Native.Chart.nation (edgeField n G.Color F) := by
  classical
  funext e; unfold array liftLinks Native.Chart.nation
  simp only [Function.comp_apply,edge_spec]; split_ifs; · rfl
  exact (Next.SectorChange.exp_negative _).symm

-- smooth via native Taylor apparatus, on *full* periodic chart, no averaging choices.
def exponent (G:Gauge) (n:Side)(F:E G n): ℝ := - Wilson.energy (array F)/2
lemma multiplier (G:Gauge)(n:Side)(F:E G n) : exponent G n F=Native.Chart.rent (Native.Chart.drive n) (edgeField n G.Color F)/2:= by rw [exponent,array_full, Native.Chart.original_W]
lemma expGerm (G:Gauge)(n:Side): germ (exponent G n):= by
    rw [funext (multiplier G n)]
    let L := (edgeField n G.Color).toContinuousLinearMap
    have he : germ (Native.Chart.rent (Native.Chart.drive n) ∘ L) := by
        apply ContDiffAt.comp (f:=⇑L); · rw [map_zero]; exact Native.Chart.rent_s _
        exact L.contDiff.contDiffAt
    exact he.div_const _
lemma expense_tree (F : Cotree n → G.Color) : -exponent G n (genJet F)=fiscal F := by
  classical
  unfold exponent fiscal
  rw [show array (genJet F)= representative F from ?_]; · ring
  change liftLinks _=liftLinks _; congr 1; funext i; unfold splitLink genJet comp; split_ifs <;> first | rfl | simp_all
@[simp] lemma at_flat : exponent G n 0=0 := by
  classical
  have hh: genJet (0:Dir G n)=0:= by funext e; unfold genJet; split <;> rfl
  rw [← hh]; exact neg_eq_zero.mp ( (expense_tree (0:Dir G n)).trans fiscal_zero )
lemma stationary : fderiv ℝ (exponent G n) 0=0 := by
    apply IsLocalMax.fderiv_eq_zero (f:=exponent G n); refine Eventually.of_forall fun x=>?_
    change exponent _ _ x ≤ exponent _ _ 0; rw [at_flat]; exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Wilson.energy_nonneg _)) (by norm_num)

-- all based gauge transformations. Gauge group conventions are exactly linked in `array_rot`
-- into the `OpenGauge` convention in MS.Native.Chart. No gauge action on a field label.
def inverseAction (i:Ghost G n)(s:ℝ)(x:Site n): G.El := G.lieExp (s • siteField n G.Color (priv i) x)
def rotLinks (i:Ghost G n)(F:E G n)(s:ℝ) (e:OEdge n): G.El:= Maurer.step (endpoints G n e (priv i)) (F e) s
def rotatedLog (i:Ghost G n)(F:E G n)(s:ℝ): E G n:= fun e=> G.plog (G.mat (rotLinks i F s e))
lemma array_rot (i:Ghost G n)(F:E G n)(s:ℝ): liftLinks (rotLinks i F s) = Lattice.gauge (fun x=>(inverseAction i s x)⁻¹) (array F):= by
    let g : Site n → G.El:= fun x=> (inverseAction i s x)⁻¹
    have hg x : g (-x)=g x:= by simp [g,inverseAction,site_even]
    change _=Lattice.gauge g (array F)
    rw [show Lattice.gauge g (array F)=liftLinks (fun e=> Lattice.gauge g (array F) e.val) from funext (path_law g _ hg)]
    apply congr_arg liftLinks; funext e;
    rw [Lattice.gauge, array,lift_at]; dsimp only [Function.comp_apply]; unfold rotLinks Maurer.step
    simp_rw [Next.SectorChange.exp_negative]; simp [g]; rfl

section test
variable (O:Wilson.Config G n→ℝ)
abbrev Invariant : Prop:= ∀ t: Site n→G.El,(∀ x,t (-x)=t x) → ∀ U,O (Lattice.gauge t U)=O U
def charted : E G n→ℝ:= O∘ array
lemma chartGerm (h : germ (O ∘ Native.Chart.nation)) : germ (charted O):= by
    let L := (edgeField n G.Color).toContinuousLinearMap
    have he : charted O = (O∘ Native.Chart.nation) ∘ L:= funext fun i=> congr_arg O (array_full i)
    rw [he]; apply ContDiffAt.comp (f:=⇑L); · rw [map_zero]; exact h
    exact L.contDiff.contDiffAt
lemma inert (h:Invariant O) (hc:germ (charted O)) : Inert generator (charted O):= by
    intro i
    obtain ⟨r,hr,W⟩:=LocalH.geom_patch G
    let A:= W r le_rfl
    filter_upwards [eventually_all.mpr (fun j:OEdge n=> (show ∀ᶠ F:E G n in 𝓝 0,F j∈Metric.ball 0 r from (continuous_apply j|>.tendsto (0:E G n)).eventually (Metric.ball_mem_nhds _ hr))), hc.eventually (by simp)] with F hF hc
    have hd : HasDerivAt (rotatedLog i F) (generator i F) 0:= hasDerivAt_pi.mpr fun j=> Maurer.amp _ A (hF j)
    have he : rotatedLog i F 0=F := by funext j; rw [rotatedLog,rotLinks,Maurer.step_start]; exact Maurer.snap_on A (hF j)
    let J:=charted O
    have hJ : J ∘ rotatedLog i F=ᶠ[𝓝 0] fun _=> J F := by
        filter_upwards [eventually_all.mpr (fun j:OEdge n=> Maurer.walk_on (endpoints G n j (priv i)) A (hF j))] with t ht
        change O (array (rotatedLog i F t))=O (array F)
        rw [show array (rotatedLog i F t)=liftLinks (rotLinks i F t) from congr_arg liftLinks (funext (fun j=> A.2.2.2.1 (ht j))), array_rot]; exact h _ (fun x=> by rw [inverseAction,site_even]; rfl) _
    have hy : HasDerivAt (J ∘ rotatedLog i F) (rotate (generator i) J F) 0:=
        HasFDerivAt.comp_hasDerivAt_of_eq 0 (hc.differentiableAt (by simp)).hasFDerivAt hd he.symm
    exact (hy.congr_of_eventuallyEq hJ.symm).unique (hasDerivAt_const ..)
lemma expInvariant : Inert generator (exponent G n):= by
    let A (U:Wilson.Config G n):= -Wilson.energy U / 2
    exact inert A (fun t _ U=> by simp [A,Wilson.energy_gauge]) (expGerm ..)
end test

def actionW (G:Gauge)(n:Side): Raw (Position.Letter G n) ℂ:= Focus.Sourced (exponent G n) (colorTerm G (BasedSite n)) generator (Position.glow G n)
def haarW (G:Gauge)(n:Side): Raw (Letter G n) ℂ:= ink (Position.glow G n).e0 logHaar
local notation "WΘ" => actionW G n
local notation "FΘ" => haarW G n

-- min rank for S gauge/Haar body. Force equations through *all* ranks at once in position
private lemma letter_min (i: Position.Letter G n): From (atLetter (R:=ℂ) i) 1:= by rintro (_| ⟨i,l⟩) h; rfl; simp at h; omega
local notation "gγ" => generator (G:=G) (n:=n)
local notation "fΔ" => colorTerm G (BasedSite n)
local notation "Nβ" => launch (Position.glow G n) fΔ gγ
lemma minimal : From WΘ 2:= by
    let X:= Position.glow G n
    suffices H:From ((β).hung (launch X fΔ gγ)) 2 by
        refine From.add ?_ H; rintro (_|⟨i,_|l⟩) he
        · change ((exponent G n 0:ℝ):ℂ)=0; simp
        · change ((fderiv ℝ (exponent G n) 0 (X.e0 i) :ℝ):ℂ)=0; rw [stationary]; simp
        simp at he; omega
    refine From.sum univ fun i _=> From.smul _ ((letter_min _).pair (show From (launch X fΔ gγ i) 1 from ?_))
    intro l hl; suffices (Nβ i) []=0 by
        rcases l with _|⟨z,w⟩; · exact this
        simp at hl; omega
    rcases i with i|i
    · change (stone _ gγ i) []=0; simp only [stone, Finset.sum_apply, nil_product]
      exact Finset.sum_eq_zero fun _ _=> zero_mul _
    change (Focus.shadow (focus G n) fΔ i) []=0; simp [Focus.shadow, Finset.sum_apply,spark,atLetter]
lemma master : FreeBV.MasterLaw β WΘ FΘ := by
    let X:= Position.glow G n; let V:= Position.winds (G:=G) (n:=n)
    exact {
      smoothW:=(ink_s _ X.never (expGerm G n)).add ((lifting X _ _ V.smooth).acted_s)
      smoothH:=ink_s _ X.never haarSmooth
      evenW:=(ink_p _ X.never _).add ((lifting X _ _ V.smooth).acted_e)
      evenH:=ink_p _ X.never _
      start:=minimal
      haar_normalized:= by simp [haarW,logHaar,Maurer.lac,LocalH.spin_zero]
      classicalWard:= V.classicalGauge X (expGerm G n) expInvariant
      determinant:= V.quantum_pay X haarSmooth volume_charge
      flatDet:= Focus.lap_g X _
      detCentral:= Focus.link_g X _ _ }

def insertion (O:Wilson.Config G n→ℝ): Raw (Letter G n) ℂ:= ink (Position.glow G n).e0 (charted O)
lemma physical {O:Wilson.Config G n→ℝ}{d:ℤ} (he:Invariant O) (h:germ (charted O)) (hd:From (insertion O) d): FreeBV.PhysicalLaw β WΘ FΘ (insertion O) d where
    symm:=ink_s _ (Position.glow G n).never h
    even:=ink_p _ (Position.glow G n).never _
    starts:= hd
    ghost_free_lap:= Focus.lap_g (Position.glow G n) _
    gauge:= by unfold actionW insertion; rw [winds.onto (Position.glow G n) h]; simp_rw [inkit _ (inert O he h _),ink_zero,map_zero, Finset.sum_const_zero]
    ghost_free_haar:= Focus.link_g (Position.glow G n) _ _
end YM.WilsonBridge.Based.Position
