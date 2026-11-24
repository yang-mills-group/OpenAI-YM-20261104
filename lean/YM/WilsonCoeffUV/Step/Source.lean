import YM.WilsonCoeffUV.Step.Ward.Invariance
/-!
# Source linear push

One unscaled mark element before average/join, no length restrictions at a
single step here. Vector algebra formulation for finite load arrays retaining
tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue
open Matrix Function PowerSeries Filter
open scoped BigOperators
variable {U R R':Type*}[AddCommGroup R][AddCommGroup R'][Module ℝ R][Module ℝ R']
variable (f:R→ₗ[ℝ]R')

def tinct {r:ℕ} : Ten R U r→ₗ[ℝ] Ten R' U r where
  toFun P:=f ∘ P
  map_add' p q:= by ext; simp
  map_smul' c p:= by ext; simp

def cloaks : Gen R U→ₗ[ℝ] Gen R' U := LinearMap.pi fun i=> (tinct (U:=U) (r:=i) f).comp (LinearMap.proj i)
lemma cloak_e (P:Gen R U)(i) : cloaks f P i=tinct f (P i):=rfl
lemma cloak_sever (P:Gen R U)(a:U): cloaks f (sever a P) = sever a (cloaks f P) := by
  ext i j; change f ((i+1) • P _ _)= (i+1) • f _; rw [map_nsmul]; rfl

lemma cloak_spore (P:Gen ℝ U)(Q:Gen R U): cloaks f (spore P Q)= spore P (cloaks f Q):= by
  ext1 i; simp_rw [cloak_e,spore,map_sum]; apply Finset.sum_congr rfl; intro j _; funext v
  change f (if h:_ then _ else _) = if h:j.1+j.2=i then _ else 0
  split; · apply map_smul
  rw [map_zero]
lemma cloak_swirl {i:ℕ}(P:Ten R U i) : tinct f (swirl P) = swirl (tinct f P) := by
  ext x; change f (swirl _ x)= _; simp_rw [swirl, Pi.smul_apply,map_smul,Finset.sum_apply,map_sum]; rfl
variable [Fintype U]
lemma cloak_ripple (G:Matrix U U ℝ)(P:Gen R U) : cloaks f (ripple G P)=ripple G (cloaks f P):=by unfold ripple; simp_rw [map_sum,map_smul,cloak_sever]
lemma cloak_arbor (G:Matrix U U ℝ)(P:Gen ℝ U)(Q:Gen R U): cloaks f (arbor G P Q)=arbor G P (cloaks f Q):= by
  unfold arbor; simp_rw [map_sum,map_smul]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; apply congrArg (fun v:Gen R' U=> (G i j/2) • v)
  ext1 r; simp only [cloak_e,cloak_swirl]
  apply congrArg swirl; rw [←cloak_e, cloak_spore, cloak_sever]
lemma cloak_bul (G:Matrix U U ℝ)(D:Layers ℝ U)(P:Pal R U)(k i : ℕ): cloaks f (bul G D P k i)=bul G D (fun j=>cloaks f (P j)) k i:= by
  induction k using Nat.strong_induction_on generalizing i with
  | h n ih=>
    cases n with
    | zero=> rw [bul_zero,bul_zero]
    | succ n=>
      have he G': cloaks f (ravel G' D (bul G D P) n i)=ravel G' D (bul G D (fun j=>cloaks f (P j))) n i:=by
        unfold ravel; simp_rw [map_sum]; apply Finset.sum_congr rfl; intro j hj; have hj:=Finset.mem_antidiagonal.mp hj; apply Finset.sum_congr rfl; intro s _; rw [cloak_arbor,ih j.2 (by omega)]
      rw [bul_next,bul_next,map_smul,map_add,map_add,cloak_ripple, ih n n.lt_succ_self,he,he]
lemma cloak_fade {V:Type*}(M:Matrix U V ℝ)(P:Gen R U): cloaks f (fade M P)=fade M (cloaks f P):= by
  ext i v; change f (fade M P i v)= _; simp_rw [fade,map_sum, map_smul]; rfl
end YM.WilsonCoeffUV.Blue

namespace YM.WilsonCoeffUV
open Matrix Function PowerSeries Filter Precision Tree
open RG Blue Wilson Lattice Laurent Exterior Bloch FreeResolvent
open scoped BigOperators
variable {G:Gauge}{c f: Side}(S:StepData c f)(F:Forest S.ratio) (H:FaceRow) (Q:Matrix (Body 1 f) (Body 1 c) ℝ)

section
variable {R:Type*}[AddCommGroup R][Module ℝ R]
def srCold (w:Pal R (Woods G f))(M: Matrix (Woods G f) (Woods G c) ℝ):Pal R (Joint G f c) := fun i=>fade (camber G M) (w i)
def srShade (Ñ:ChartRatio G) (P:PChart G f) (w:Pal R (Woods G f)) := bul (fillSlots (Woods G c) (covariance G S F H)) (xray S F H Q Ñ P) (srCold w (extractV G S F Q))
def reed (Ñ:ChartRatio G)(P:PChart G f)(l:ℕ)(w:Pal R (Woods G f)) : Pal R (Woods G c) := fun i=> fade plug (∑ j∈Finset.range (1+l+3*i), srShade S F H Q Ñ P w j i)
variable {P:PChart G f} {w:Pal R (Woods G f)}(l:ℕ){Ñ:ChartRatio G}
lemma srStops (p:shellK 2 P)(h:LocalRatio Ñ)(c:shellK l w): stops l (srShade S F H Q Ñ P w):= stops_bul _ (span_abr _ (pack_band S p) (pack_zero S h)) l (fade_shell (camber G (extractV G S F Q)) c)
lemma srPure (Ñ:ChartRatio G)(P:PChart G f)(r:∀ i,Pure (w i))(i j): Pure (srShade S F H Q Ñ P w i j):= pure_bul _ _ (fun i=> fade_pure (r i) (camber G (extractV G S F Q))) _ _
lemma reed_band (p:shellK 2 P)(h:LocalRatio Ñ)(c:shellK l w): shellK l (reed S F H Q Ñ P l w) := by
  unfold reed; apply fade_shell; intro i r t; simp_rw [Finset.sum_apply]; exact Finset.sum_eq_zero fun b _=> srStops S F H Q l p h c b i r (Or.inl t)
lemma reed_smooth (Ñ:ChartRatio G)(P:PChart G f)(r:∀ i,Pure (w i))(i) : Pure (reed S F H Q Ñ P l w i) := by
  apply fade_pure
  intro j; rw [Finset.sum_apply]; exact Blue.Smooth.sum (fun v _=> srPure S F H Q Ñ P r v i j)
lemma reed_maps {R':Type*}[AddCommGroup R'][Module ℝ R'](u:R→ₗ[ℝ]R') :
    (fun i=> cloaks u (reed S F H Q Ñ P l w i))=reed S F H Q Ñ P l (fun i=>cloaks u (w i)) := by
  ext1 i; change cloaks u _ =_
  have he i : cloaks u (srCold w (extractV G S F Q) i)= srCold (fun i=>cloaks u (w i)) (extractV G S F Q) i := cloak_fade ..
  simp_rw [reed, cloak_fade,map_sum,srShade,cloak_bul,he]
end
section
variable {Ñ:ChartRatio G}{P w:PChart G f}(l:ℕ)

def insideMark (Ñ:ChartRatio G)(P w:PChart G f) : Ink (Woods G c):=
  Wick (Woods G c) (treeInverse G S F H 0) (raiseE (shot S F Q Ñ P) * loom (camSlice G S F (extractV G S F Q)) (flash w))
lemma inside_reed (p:shellK 2 P)(h:LocalRatio Ñ)(c':shellK l w)(e: S.patch.Branches S.kernel G) (hs:(H.acts f).transpose=H.acts f)(u:∀ i,Pure (P i))(v:∀ i,Pure (w i)) :
    insideMark S F H Q Ñ P w= inside S F H Q Ñ P* flash (reed S F H Q Ñ P l w):= by
  let I:= reveal G S F; let B:= covariance G S F H; let T:=treeInverse G S F H 0
  let M:=extractV G S F Q; let R:=casePW S Ñ M P; let D:=srCold w M; let O:=overM G S F
  have hk : loom O=railCov I (path (U:=Woods G c)) := bridge_rail _
  have hT: T.transpose=T:= by unfold T treeInverse resolve; rw [zero_smul,add_zero,transpose_nonsing_inv,treeMatrix,transpose_submatrix,full_symmetric _ hs]
  have hB:B= I*T*I.transpose:=rfl
  have heq q : Wick (Woods G c) T (loom O q)=Wick (Woods G c) B q:=by rw [hk,W_linear _ _ (by rw [hB,transpose_mul,transpose_mul,hT,transpose_transpose,Matrix.mul_assoc]) hT hB, train_id,RingHom.id_apply]
  have hy : loom O (flash D)= loom (camSlice G S F M) (flash w):= by
    rw [show flash D= _ from (loom_fade (camber G M) w (finite_shell c')).symm]; exact DFunLike.congr_fun (loom_loom (camber G M) O) _
  have hf : loom O (raiseE (flash R))= raiseE (shot S F Q Ñ P):= raise_map (loom O) (by simp [loom]) (flash_blank (pack_zero S h))
  unfold insideMark inside; change Wick _ T (raiseE _ * loom (camSlice G S F M) (flash w))= Wick _ T _* _
  rw [←hy,←hf, ← map_mul,heq,heq, wick_product (P:=R) (Q:=D) (pack_band S p) (pack_zero S h) (pack_pure S h e u) (fade_shell (camber G M) c') (fun i=> fade_pure (v i) (camber G M)) B]
  have hh :=srStops S F H Q l p h c'
  let A : Pal ℝ (Joint G f c) := fun i=> (∑ j∈Finset.range (1+l+3*i), srShade S F H Q Ñ P w j i)
  have he: stopF 1 (ramp (bul (fillSlots (Woods G c) B) (abr _ R) D) l)=flash A := at_one _ _ hh
  congr 1
  classical
  rw [he,plug_project]
  exact loom_fade _ A (fun i=> finite_sum fun j _=> finite_stops hh j i)
end
namespace Power
variable (Y:FaceRow){Ñ:ChartRatio G}{P w w':PChart G f}
open Gauge
lemma reed_turn (p:shellK 2 P)(r:P 0=shine (orbQ (precisionC G f H)))(h:LocalRatio Ñ)(l:ℕ)(ha:shellK l w)(ha':shellK l w')(e: S.patch.Branches S.kernel G) (hs:(H.acts f).transpose=H.acts f)(u:∀ i, Pure (P i))(v:∀ i,Pure (w i))(v':∀ i,Pure (w' i))
    (hu:IsUnit (treeMatrix G S F H).det) (he:Inputs S Q (H.acts f) (Y.acts c)) (hw: Warded (flash P)) {s:Signed}{b:Site c} (m:rollTest (flash w) (flash w') s (S.ratio.embed b)):
    rollTest (flash (reed S F H Q Ñ P l w)) (flash (reed S F H Q Ñ P l w')) s b := by
  intro Z H' z X X' A
  classical
  let M:= extractV G S F Q; let J:= treeMatrix G S F H
  have hx:=converge_transport S F H Y Q p r e h hu he hs hw _ _ A
  let V:=loom (camSlice G S F M); let a:=train (spool X); let a':=train (spool X')
  have hk : J.transpose=J:= by unfold J; rw [treeMatrix,transpose_submatrix,full_symmetric _ hs]
  have ν := hx.move hk hu (V (flash w)) (V (flash w')) (wire_orbit S F M _ _ _ _ _ (sweeps G S F Q Y hu he) A _ _ m)
  have hν := hx.move hk hu 1 1 (by simp)
  let B:=raiseE (a' (orbC (precisionC G c Y))-a (orbC (precisionC G c Y)))
  let I:=inside S F H Q Ñ P
  have he': treeInverse G S F H 0=J⁻¹:= by unfold treeInverse resolve; rw [zero_smul,add_zero]
  have hl: a' I = B*a I := by unfold I inside; rw [he']; rw [mul_one] at hν; exact hν
  rw [←he'] at ν;
  change a' (insideMark S F H Q Ñ P w')=B*a (insideMark S F H Q Ñ P w) at ν
  rw [inside_reed S F H Q l p h ha' e hs u v', inside_reed S F H Q l p h ha e hs u v,map_mul,map_mul,← mul_assoc] at ν
  change a' I * _= (B * a I)* _ at ν
  rw [← hl] at ν; exact (((PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [inside_mass S F H Q h]; simp) : IsUnit I).map a').mul_right_inj.mp ν.symm)
end Power
end YM.WilsonCoeffUV
