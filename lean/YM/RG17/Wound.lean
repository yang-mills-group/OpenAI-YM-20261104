import YM.RG17.Gathers
import YM.Extra.MULTISOURCE_TRAJECTORIES.Signals
import YM.Extra.MULTISOURCE_TRAJECTORIES.Probes
import YM.Overlay.Terminal
import YM.RG01.Kernel.Ratio

/-!
# Binding the unsettled Depot estimate to actual density outputs

Preserve common Marker polynomial scalar, real Haar push denominator,
mask, forced and H.Selected under readout. Need actual neighborhood
production with reserve witnesses IN THAT OUTPUT'S representation.
Unnormalized Tagged below SPECIFIES the value to represent, not claiming
that `Allows` knows how, nor that an independent coefficient is thereby
computed. See `checks/RG17/`. No reseaming at cylinder here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Extra.Trajectories Lattice Wilson RG Extraction Function Set Filter MeasureTheory Marker Overlay
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{N p m:ℕ}{C:Family G}(h:C.Makes)
variable {n:ℕ} (v:Fin n→ C.book.Token)(x:Fin n→ Lattice.Site (C.side N p))

-- Full tags directly with actual C.seen (use atRef for columns there)
def implants (v:Fin n→ C.book.Token) (x:Fin n→Lattice.Site (C.side N p)) : Insertions C.path (Fin n) N p where
    load i:= (v i).1
    field i:= observable C N p (v i).2 (x i)
    smooth _:= observable_smooth ..
lemma implants_actual (i:Fin n) : (implants v x).uses i=C.seen (v i) (x i) :=rfl
variable {Γ:Census (Fin n)}
-- exact output identity target
abbrev Tagged (m:ℕ)(U:Config G (C.side m p)) : Poly Γ:= Poly.inject fun s=> (implants v x).total s m (matrixField U)
-- H Kernel exact compatibility

lemma pushesTag (hm:m<N) (s:Γ.Mode) : (fun U: Config G (C.side m p)=> (Tagged v x m U).part s)=
    Ride.bump (C.S.block m).val s (implants v x).load • (C.path.levels.clock.op m p).push (C.path.β N p (m+1))
      (fun U: Config G (C.side (m+1) p)=> (Tagged v x (m+1) U).part s) := by
   let Z:= implants v x; funext U; change Z.total s _ _ = Ride.bump _ s Z.load * _
   rw [Z.total_step s m hm]; exact congr_arg (Ride.bump (C.S.block m).val s Z.load * ·) (Insertions.step_push _ (Z.smooth_total s hm).continuous U)

include h
lemma initVac (hm:m  ≤  N) : (fun U:Config G (C.side m p)=> (Tagged v x m U).part Γ.quiet) = (fun U=> ((C.path.rep N p m).eval U:ℂ)) :=by
   funext i; change (implants v x).total _ _ _= _; rw [(implants v x).quiet_eq hm]; exact congr_arg (fun x:ℝ=>(x:ℂ)) (congr_fun (Insertions.vac_eq h.wilson hm) i)
-- singleton at construction anchor. This statement deliberately doesn't promiscuously
-- translate an output-origin assertion across a nonconstant coarse kernel.
lemma homeSingle (k:Fin n)(hk:x k=0)(hw:C.ref (v k).1 ≤ m)(hr:m ≤ N):
    (let v':= v k
     let E:= C.factory v'.1 N p
     (fun U:Config G (C.side m p)=> (Tagged v x m U).part (Γ.fire k)) =
      (E.entries m (E.terminal.symm v'.2)).density 0 (C.localSection v'.1) (C.path.rep N p m)):=by
    let z:= v k; let E:=C.factory z.1 N p
    have hb:C.ref z.fst ≤ N:=hw.trans hr
    have ht:=h.calibrated _ _ p hb
    change _= (E.entries _ _).density _ _ _
    induction hr using Nat.decreasingInduction with
    | self=>
             funext U; change (implants v x).total _ _ _= _; rw [Insertions.total_top,Insertions.source_eq];
             rw [show (E.entries _ _).density _ _ _ U=_ from ht.encode (E.terminal.symm z.2) U]
             simp only [Ride.bump,Ride.Product,Census.fire,Finset.prod_singleton,h.wilson.starts N p|>.2,implants_actual,hk]; rfl
    | of_succ j hj ih=>
        rw [pushesTag v x hj,ih (hw.trans (Nat.le_succ _))];
        simp only [Ride.bump,Census.fire,Finset.prod_singleton,Complex.ofReal_natCast]
        exact (ht.unnormalized j hw hj _).symm

def ratioLine (j:ℕ)(V: Config G (C.side j p))(s:Γ.Mode) := (Tagged v x j V).part s / ((C.path.rep N p j).eval V:ℂ)
lemma ratioTo (hr:m ≤ N)(U:Config G (C.side m p))(s:Γ.Mode) : ratioLine v x m U s=((implants v x).ratios Γ m (matrixField U)).part s :=by
    unfold ratioLine; have hz:= congr_fun (Insertions.vac_eq (N:=N) (p:=p) h.wilson hr) U; rw [← hz,Insertions.part_ratios,Complex.ofReal_inv]; exact div_eq_mul_inv ..

-- Exact relation to kernel branch with full scalar denominator; reuse
-- Kernel.actual and reader prices on this domain, NOT as perturbative estimates.
set_option maxHeartbeats 400000 in
lemma road (hr:m<N)(U:Config G (C.side m p))(s:Γ.Mode):
   ratioLine v x m U s = Ride.bump (C.S.block m).val s (implants v x).load * RG01.Kernel.conditional C.path N m p U (fun _ W => ratioLine v x (m+1) W s) :=by
    let X:=(implants v x); let bump':=Ride.bump (C.S.block m).val s X.load
    let Z:= C.path.rep N p (m+1); let K:=C.path.levels.clock.op m p
    let D:ℝ:= (C.path.rep N p m).eval U
    let W(V:Config G (C.side (m+1) p)):= ratioLine v x (m+1) V s
    let μ:= prior G (C.side (m+1) p)
    have hv:Continuous W :=by
        have hp: W=(fun q=> X.total s (m+1) q * (↑((Insertions.vacuum C.path N p (m+1) q)⁻¹):ℂ))∘ matrixField:=funext fun i=> ratioTo h _ _ hr i s
        rw [hp]; exact (((X.smooth_total s hr).continuous).mul (Complex.continuous_ofReal.comp ((Insertions.vac_smooth hr).continuous.inv₀ (fun x=> (Insertions.vac_pos hr x).ne')))).comp matrixField_cont
    let F:= (fun (_:K.Choices) i=>W i)
    obtain ⟨a,ha⟩:= isCompact_univ.exists_bound_of_continuousOn hv.continuousOn
    have hh: RG01.Kernel.Bounded μ F a:= ⟨fun _=> hv.aestronglyMeasurable,fun _ i=> ha _ (mem_univ _)⟩
    let e:= RG01.Kernel.expense C.path N m p U
    let f(i:K.Choices)(V):= (↑(e i V):ℂ)* W V
    have he:= RG01.Kernel.actual N C.path h.wilson U hr
    unfold ratioLine -- unfolds RHS too
    rw [(show (Tagged v x m U).part s=bump' * _ from congr_fun (pushesTag _ _ hr s) U), mul_div_assoc]; apply congr_arg (bump' * ·)
    change _/ (D:ℂ)= ∑ i:K.Choices,∫ V,f i V ∂μ
    unfold StepData.push; rw [← integral_div, ← integral_finsetSum _ (fun i _=> he.funds hh i)]; apply integral_congr_ae; filter_upwards with V
    change (K.density Z.beta V U • ((Tagged v x (m+1) V).part s)) / (D:ℂ)= _
    rw [StepData.density,Finset.sum_smul,Finset.sum_div]; apply Finset.sum_congr rfl; intro i _
    dsimp only [f,e,RG01.Kernel.expense,W,ratioLine]; rw [Complex.real_smul]; push_cast
    have hz :(Z.eval V:ℂ)≠0:=by exact_mod_cast (Extra.Histories.Tour.bright C.path h.wilson N p (m+1) hr V|>.ne')
    unfold RG01.Kernel.upper
    change _= (((K.likelihood V i:ℂ) * _ * (Z.eval V:ℂ) / D) * ((Tagged v x (m+1) V).part s / (Z.eval V:ℂ))); field_simp; dsimp only [K,Z]; ring

set_option linter.unusedSectionVars false in -- document h
lemma terminalValue (hr:m ≤ N) :
     (∫ U,(Tagged v x m U).part (Stock.final (Fin n))∂prior G (C.side m p)) =
        Ride.bump (C.S.a m) (Stock.final (Fin n)) (implants v x).load * (Wilson.partition G (C.side N p) (C.beta N p):ℂ)* C.numeric N p v x := by
   let s:= Stock.final (Fin n); change (∫ U,(Tagged v x m U).part s ∂_) = Ride.bump _ s _ * _ * _
   induction hr using Nat.decreasingInduction with
   | self=>
            let u (U:Config G (C.side N p)):= ∏ i:Fin n,C.seen (v i) (x i) U
            let tbb (U:Config G (C.side N p)):= (Tagged v x N U).part s
            have he(U): tbb U= Ride.bump (C.S.a N) s (implants v x).load * (bare (C.beta N p) U:ℂ)* u U:=by
                 change (implants v x).total _ _ _= _; rw [Insertions.total_top,Insertions.source_eq]; rfl
            change (∫ U,tbb U ∂ _) = _ * Wilson.moment (C.beta N p) u; rw [moment_formula _ u (C.integrableR v x)];
            simp_rw [he,mul_assoc, integral_const_mul]; rw [mul_inv_cancel_left₀]; exact Complex.ofReal_ne_zero.mpr (partition_pos _).ne'
   | of_succ j hj ih=>
        have hv:Continuous (fun U=> (Tagged v x (j+1) U).part s):= ((implants v x).smooth_total s hj).continuous.comp matrixField_cont
        rw [pushesTag v x hj s]; change (∫ U,Ride.bump (C.S.block j).val s (implants v x).load * ((C.path.levels.clock.op j p).push (C.path.β N p (j+1)) (fun V=> (Tagged v x (j+1) V).part s) U)∂prior ..)=_; rw [integral_const_mul]; rw [StepData.push_integral (C.path.levels.transition_mass ..) _ (hv.integrable_of_hasCompactSupport (by exact HasCompactSupport.of_compactSpace _)), ih,← mul_assoc, ←mul_assoc];
        congr 2; unfold Ride.bump; rw [← Finset.prod_mul_distrib,C.S.a_step]; apply Finset.prod_congr rfl; intro i _
        rw [← mul_pow]; congr 1; have hi: (↑(C.S.block j).val:ℂ)≠0:=by exact_mod_cast (C.S.block j).property.ne'
        push_cast; field_simp


omit h in
def tagMeasurement {N p:ℕ} (i:ℕ) (ψ:Test n):ℂ:=
  let s:= Stock.final (Fin n)
  let t:= (Wilson.partition G (C.side N p) (C.beta N p):ℂ)
  -- N,p implicit?
  (C.S.a N:ℂ)^(4*n) * ∑ x: Fin n→ Site (C.side N p), ψ (Order.cells C N p x) *
       ((Ride.bump (C.S.a i) s (implants v x).load * t)⁻¹ * ∫ U, (Tagged v x i U).part s ∂prior G (C.side i p))
lemma measurement_at (i:ℕ)(hi:i  ≤  N)(ψ:Test n): Order.smears C N p v ψ=tagMeasurement (N:=N) (p:=p) v i ψ:=by
    unfold Order.smears tagMeasurement; apply congr_arg; apply Finset.sum_congr rfl; intro x _
    rw [terminalValue h v x hi]; have hv: Ride.bump (C.S.a i) (Stock.final (Fin n)) (implants v x).load ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _=> pow_ne_zero _ (by exact_mod_cast (C.S.a_pos i).ne')
    rw [inv_mul_cancel_left₀ (mul_ne_zero hv (Complex.ofReal_ne_zero.mpr (partition_pos _).ne'))]
end YM.RG17
