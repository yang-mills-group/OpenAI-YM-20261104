import YM.MSbar.Chord.Sensor
import YM.MSbar.Rolling.Sprout
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Midpoint
open Function Filter
open Lattice Wilson Gauge Work.F03 Push Push.Uniform RG Precision Exterior MSbar.Rolling MSbar.Wave Cacao
open MeasureTheory Set Bakery
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{c : Side}{X₀:Set (Positions (Primary c G))}{W r K Λ σ α:ℝ}
open MvPolynomial
local notation "E"=>Positions (Primary c G)
variable (S:Activities G c)(R:PathData G) (p:Clip) (u v :ℕ)
noncomputable def stackP (c:Side)(G:Gauge): Pot (Primary c G) →ₗ[ℝ] FaceRail c G where
    toFun P:= rim (fun x:Positions (Primary c G)=> MvPolynomial.eval x P)
    map_add' P Q:=by ext1 x; ext1 y; let f(P:Pot (Primary c G))(x):=MvPolynomial.eval x P; change rim (fun x:Positions (Primary c G)=> MvPolynomial.eval x _) x y=rim (f P) x y +rim (f Q) x y; simp_rw [map_add]; change rim (f P+f Q) x y= _; have he:= congr_arg (fun v:Tensor.T _ ℝ 2=>v ![x,y]) (iteratedFDeriv_add_apply (show ContDiffAt ℝ (↑(2:ℕ)) (f P) 0 from (vent P|>.contDiffAt).of_le le_top) ((vent Q|>.contDiffAt).of_le le_top)); change iteratedFDeriv ℝ _ _ _ _=_ at he; simp only [_root_.add_apply,iteratedFDeriv_two_apply] at he; exact he
    map_smul' c' P:=by
        ext1 x; ext1 y; let f(P:Pot (Primary c G))(x):=MvPolynomial.eval x P; change rim (f (c' • P)) x y= c'* rim (f P) x y; have hx : f (c' • P)= c' • f P:=funext fun i=> by unfold f; rw [← C_mul',map_mul,eval_C]; rfl
        rw [hx]; have ht:= congr_arg (fun i:Tensor.T _ ℝ 2=>i ![x,y]) (iteratedFDeriv_const_smul_apply (a:=c') (show ContDiffAt ℝ (↑(2:ℕ)) (f P) 0 from (vent P|>.contDiffAt).of_le le_top)); change iteratedFDeriv ℝ _ _ _ _= _ at ht; simp only [_root_.smul_apply,iteratedFDeriv_two_apply] at ht; exact ht
noncomputable def stackH (c:Side)(e:G.Color): FaceRail c G →ₗ[ℝ] ℝ where
    toFun v:= grossH v e
    map_add' P Q:= by unfold grossH gross; dsimp only; simp only [_root_.add_apply,add_mul, Finset.sum_add_distrib,mul_add]
    map_smul' r P:=by unfold grossH gross; simp only [_root_.smul_apply, RingHom.id_apply,smul_eq_mul]; simp_rw [mul_assoc,← Finset.mul_sum,mul_left_comm r]
noncomputable def caliper (c:Side)(e:G.Color): Pot (Primary c G) →ₗ[ℝ] ℝ:= (stackH c e).comp (stackP c G)
lemma ion (h :Premier (main c p R)) : stackP c G (ink c p R) = rim (collectT c R p):=by
    let z:= collectT c R p; let Z(x:Positions (Primary c G)):= eval x (ink c p R); have hh: Premier z:= h.line (tint G (Body 1 c)).toContinuousLinearMap
    have hx:z=z:=rfl; have he(x:E) : Z x= Work.G05.blockTaylor 2 z x:=by unfold Work.G05.blockTaylor; rw [Finset.sum_apply]; rw [Finset.sum_eq_single_of_mem 2 (by decide)]; exact pots z x 2; intro i hi hr; apply hh.zeroP; have hv:= Finset.mem_range.mp hi; omega
    ext1 x; ext1 y; change rim Z x y = _; rw [funext he]; have ht:= congr_arg (fun i:Tensor.T _ ℝ 2=> i ![x,y]) (Work.G05.blockTaylor_jets (hh.1.of_le (m:=↑(2:ℕ)) le_top) 2 le_rfl); change iteratedFDeriv ℝ _ _ _ _=_ at ht; rw [iteratedFDeriv_two_apply,iteratedFDeriv_two_apply] at ht; exact ht
open Tree
variable {f: Side}{W:StepData c f}
variable (B: Forest W.ratio) (P:PathData G)(q: Clip)(i:W.Choices) (e:G.Color)(S:Nesting G f)(x: fieldDir G c 1→AxisChart G B)
structure Keeps (W:Nesting G c)(h:ℕ)(v:G.Color):Prop where
    sitting (i:ℕ):i≤ h→ caliper c v (PowerSeries.coeff i W)=0
    level : Expanse W 1 h
noncomputable def tiltMap (e:PowerSeries ℝ) (p:ℕ)(x:ℝ):= x/taste p e x
variable (J:ChartRatio G)
-- Export chosen higher counterterm. Actual continuation parameter shown for convenience.Ward & cone proofs can take returned Truth; β estimating progress ties uniquely to this tilt, not a surface-flat suggestion.
theorem prices (he:‖e‖=1){F:ℝ → Config G f→ℝ}(h:Trend F S P q u)(ho : Serves W G)(hc : Critical B q P x)(hQ:ClassicalMatch B q p P R x)(hv : Matrix.PosDef (Push.Uniform.block (priced B i q P) 0))(hg: R.Bounds p σ K Λ)(hJ:LocalRatio J)(hm: 10*(v+4)< c.val)(hy:(Fintype.card PlaqAxes:ℝ)*(K*K*url c v σ)≤1) :
   ∃ T:PowerSeries ℝ,∃ U : Nesting G c, U=bley T (colorCut B i P q J S x) (ink c p R) ∧ PowerSeries.coeff 0 T=1 ∧ Keeps U u e∧ Trend ((shunt W F) ∘ tiltMap T u) U R p u:=by
    let Z:= colorCut B i P q J S x; have ht:Trend (shunt W F) Z R p u:=newT B i P R q p x J hJ S F u ho hc hQ h hv
    let k:=ink c p R; let z:=caliper c e; have hP:z k=grossH (rim (collectT c R p)) e:= (congr_arg (stackH c e) (ion R p ht.quiet))
    have hM:z k≠0:=by
        have he: |z k+2|≤1:= hP.symm ▸ (sampled e R p (a:=σ) hg v hm he).trans hy
        intro hz; linarith only [(abs_le.mp he).2,hz]
    obtain ⟨T,hq,hr⟩:= payer ht.bond hM u; let V:= bley T Z k
    have he : Trend ((shunt W F) ∘ tiltMap T u) V R p u:=given T u Z R p ht (manifest u T) hq
    exact ⟨T,V,rfl,hq,⟨hr,he.plane⟩,he⟩
end YM.MSbar.Midpoint
