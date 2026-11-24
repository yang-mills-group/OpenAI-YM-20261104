import YM.OPE.Compatible.Kiwi.Layer
/-!
# Nested limit. Fixed h.R. then aperture to infinity on startup keys
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Prairies
open Function MeasureTheory Set Topology Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir
open GaussianScore Libra WithLp RG Precision Votive Glass Flume Flume.Script Flock StageLight Balsam Nestle Pert.Full
open Silt Silt.Float Shell Char FreeResolvent Paver Rill Saga Shrew Maxwell Maxwell.Free
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {N:Side}{G:Gauge}{L:RG.KernelChoices}{P:ChartRatio G}{d k j r w e m:ℕ} {V:Type}{ℓ:Filter V}
local notation "Q"=> LakeT ℓ
variable (u:V→Side)(q:Side)(h:q.val>1) (p p':Cover)
variable (A: Saga G e k)(B:Saga G m d){hu:4≤r} {H:∀ i,Even (u i).val}
local notation "Ψ"=> (fun i:V×ℕ=> boost (Nsp u q H i) (Train.top r) hu L (G:=G))
local notation "ρ"=> (fun i:V×ℕ=>Chart.tangent G (Weir.Limb (Nsp u q H i)))
abbrev limMark {K D: ℕ}(A:Saga G K D)(i:V×ℕ): Libra.Keys G (Weir.Limb (Nsp u q H i))→ℝ:= Wish A (Nsp _ _ H i) (stow u q p i)
abbrev pulseF (i:V×ℕ):ℂ:= ((baseR q i.2^(e+m) * (Ψ i).average (ρ i) (limMark (H:=H) u q p A i * limMark (H:=H) u q p' B i):ℝ):ℂ)
include h
lemma borne (hp:Ncap u ℓ)(hx:p≠p'):
     Tendsto (pulseF (hu:=hu) (H:=H) (L:=L) u q p p' A B) Q (𝓝 (Maxwell.Free.bond G (incVec 1 p) (incVec 1 p') A.terra B.terra)):=by
         let P(X:Saga G e k)(Y:Saga G m d):= pulseF (hu:=hu) (H:=H) (L:=L) u q p p' X Y; let g:= Maxwell.Free.bond G (incVec 1 p) (incVec 1 p'); have hp₁(X:Saga G e k)(Y:Saga G m d)(i):Bond (limMark u q (H:=H) p X i *limMark (H:=H) u q p' Y i):= (phiB X ..).mul (phiB Y ..)
         change Tendsto (P A B) Q (𝓝 (g _ _)); induction A with
         | @mon i a hA ht=>
           let Z:= Saga.mon a hA ht; induction B with
           | @mon j b hB hh=>
             have he:=pursuit (L:=L) (hu:=hu) (H:=H) Finset.univ Finset.univ u q h p p' a b hp hx; rw [show rung a Finset.univ=e from hA, show rung b Finset.univ=m from hB] at he; exact he
           | empty=> rw [Saga.terra,Saga.terra,map_zero]; have hv(i): P Z Saga.empty i=0:=by unfold P pulseF limMark;rw [show Wish (Saga.empty (e:=m) (G:=G) (k:=d)) _ _=0 from rfl,mul_zero,show (Ψ i).average (ρ i) 0=0 from singleConst ..,mul_zero,Complex.ofReal_zero] -- `(Saga.empty ..)`? syntax
                     exact Tendsto.congr' (Eventually.of_forall fun i=>(hv i).symm) tendsto_const_nhds
           | add a b I W=> rw [show (Saga.add a b).terra=terra a+terra b from rfl,map_add]; apply Tendsto.congr' ?_ (I.add W); filter_upwards with i; unfold P pulseF limMark; rw [show Wish (Saga.add a b) _ _= _ from (show limMark (H:=H) u q p' (Saga.add a b) i=_ from (show limMark (H:=H) u q p' (Saga.add a b) i=limMark (H:=H) u q p' a i+limMark (H:=H) u q p' b i from rfl)), mul_add, sun (ρ i) (Ψ i) (hp₁ Z a i) (hp₁ Z b i),mul_add,Complex.ofReal_add]
           | sml c x I=> rw [show (sml c x).terra= _ from (show (sml c x).terra=(c:ℂ)•terra x from rfl),map_smul,smul_eq_mul]; apply Tendsto.congr' ?_ (I.const_mul (c:ℂ)); filter_upwards with i; unfold P pulseF; rw [show limMark (H:=H) u q p' (sml c x) i=c • limMark (H:=H) u q p' x i from rfl, mul_smul_comm, scooted]; push_cast;ring -- _implicit
         | empty=> rw [Saga.terra,map_zero,LinearMap.zero_apply]; have hv(i): P Saga.empty B i=0:=by unfold P pulseF; rw [show limMark (H:=H) _ _ _ (Saga.empty (G:=G) (e:=e) (k:=k)) _=0 from rfl,zero_mul,show (Ψ i).average (ρ i) 0=0 from singleConst ..,mul_zero,Complex.ofReal_zero]
                   exact Tendsto.congr' (Eventually.of_forall fun i=>(hv i).symm) tendsto_const_nhds
         | add a b I W=> rw [show (Saga.add a b).terra=terra a+terra b from rfl,map_add,LinearMap.add_apply]; apply Tendsto.congr' ?_ (I.add W); filter_upwards with i; unfold P pulseF; rw [show limMark (H:=H) u q p (Saga.add a b) i=limMark (H:=H) u q p a i+limMark (H:=H) u q p b i from rfl, add_mul, sun (ρ i) (Ψ i) (hp₁ a B i) (hp₁ b B i),mul_add,Complex.ofReal_add]
         | sml c x I=> rw [show (sml c x).terra= _ from (show (sml c x).terra=(c:ℂ)•terra x from rfl),map_smul,LinearMap.smul_apply,smul_eq_mul]; apply Tendsto.congr' ?_ (I.const_mul (c:ℂ)); filter_upwards with i; unfold P pulseF; rw [show limMark (H:=H) u q p (sml c x) i=c • limMark (H:=H) u q p x i from rfl, smul_mul_assoc, scooted]; push_cast; ring
omit h in
lemma Outerm {X:Type*}[TopologicalSpace X][RegularSpace X]{c:X}{a:V×ℕ→X}(b:V→X)(hp:Tendsto a Q (𝓝 c))(hx:∀ᶠ v in ℓ,Tendsto (fun j=>a (v,j)) atTop (𝓝 (b v))): Tendsto b ℓ (𝓝 c):=by
     refine tendsto_def.mpr fun s hs=>?_; obtain ⟨t,⟨ht,hT⟩,he⟩:= (closed_nhds_basis c).mem_iff.mp hs; filter_upwards [sails.mp (hp.eventually ht),hx] with v hv hb; exact he (hT.mem_of_tendsto hb hv)
end YM.OPE.Prairies
