import YM.MS.Class.Common
import YM.MS.Class.Kinetic
import YM.MS.Local.Number

set_option autoImplicit false
noncomputable section
namespace YM.MS.Local.BV
open Function Filter Set Finset Plane Koszul Real Momentum Tensor Submodule MatrixLet
open Landau Detect Detect.Mark
open Complex (I)
open scoped Topology ContDiff
variable {G: Gauge}
abbrev Gof : Shift ℂ (field (Landau.parity (A:=Axis) (C:=G.ColorIndex)) (P:=FourP)) true := (send (id:FourP→FourP)).move
abbrev mslug (a: Branch G Axis) := wfield a-ghostNo a
abbrev Grade (G : Gauge):= Twig (Branch G Axis) FourP
abbrev yields (r:ℤ) (q:ℤ):= seed FourP (mslug (G:=G)) ghostNo r q
lemma m_pos (i : Branch G Axis): 0≤mslug i:= by rcases i with ⟨⟨_|i,_|_⟩,c⟩ <;> norm_num [mslug,wfield,dim,ghostNo,ghostChannel]
lemma split_parity (i : Branch G Axis): Landau.parity i = Local.parity (ghostNo i):=by rcases i with ⟨⟨_|i,_|_⟩,c⟩ <;> rfl
abbrev Q := MatrixLet.one (Gof (G:=G))
variable (f: Grade G) (i j k:CI G) (a:Axis) (p:FourP)
lemma movesA : Q f (W a i p)=∑ j:Axis,-(precision j a p:ℂ)*f (U j i p):= by
    simp_rw [Q,by_basis]; change natQ (bud f hit) _=_; rw [qAA]; simp
lemma movesC : Q f (C i p)=∑ j:Axis,I*(p j:ℂ)*f (W j i p):= by
    simp_rw [Q,by_basis]; change natQ (bud f hit) _=_; rw [qGhost]; simp
lemma movesU : Q f (U a i p)= -(I*(p a:ℂ))*f (S i p):=by
    simp_rw [Q,by_basis]; change natQ (bud f hit) _=_; rw [qAnti]; simp
lemma movesS : Q f (S i p)=0:= by
    simp_rw [Q,by_basis]; change natQ (bud f hit) _=_; rw [qS]; simp
lemma port_token (i j : Branch G Axis) : Plane.Shape ((send id).table i j : FourP→ℂ) (1+wfield j-wfield i) := (criterion (R:=r) (y:=0) (primary_large zero_le_one)).shape i j
where
  r : LogTime.IntervalFamily Unit := {
    beg _:=0
    window _:= Set.Ici 0
    beg_nn _:=le_refl _
    ci _:=subset_rfl
    used _:=by simp
    ord _:=ordConnected_Ici
    logPart _:=1
    lg _:=le_refl _ }
lemma port_cons (i j : Branch G Axis) : (send (id:FourP→FourP)).table i j≠0→ ghostNo i=ghostNo j+1:= by
   intro h; by_contra! hh; refine h (funext fun p=>?_)
   change choir _ _ _ _ _=0; rcases i with ⟨⟨_|i,_|_⟩,a⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,b⟩ <;> norm_num [ghostNo,ghostChannel] at hh <;> simp [choir,bare]
lemma stays (h q:ℤ) (F : f∈ yields h q) : Q f∈ yields h (q+1):= by
   refine seedStar.mpr ⟨fun a=>?_, fun i hi=>?_⟩
   · change Plane.Shape (fun p=> MatrixLet.one (send id).move f (a,p)) _; simp_rw [charge]
     let g (j:Branch G Axis) (p:FourP) := (send id).table a j p * f (j,p)
     have ht j: Plane.Shape (g j) (h-mslug a):= by
         by_cases he : (send (id:FourP→FourP)).table a j=0
         · unfold g; rw [he]; simp only [Pi.zero_apply,zero_mul]; exact form_zero _
         convert (port_token a j).mul ((seedStar.mp F).form j) using 1; rfl; have hv:=port_cons a j he; unfold mslug; omega
     convert Plane.Shape.sum (s:=Finset.univ) (fun i _=> ht i) using 1; ext; rw [Finset.sum_apply]
   rcases i with ⟨i,p⟩; change ghostNo i ≠ _ at hi; unfold Q Gof; rw [charge]; apply Finset.sum_eq_zero; intro j h'
   by_cases he: (send (id:FourP→FourP)).table i j=0; rw [he,Pi.zero_apply,zero_mul]; rw [(seedStar.mp F).real' (j,p) (by simpa [port_cons i j he] using hi),mul_zero]
lemma Q_zero : Q (Q f)=0:= by
    ext i; rcases i with ⟨⟨⟨_|a,_|_⟩,i⟩,p⟩ <;> change _ = 0
    · change Q (Q f) (C i p)=0; simp_rw [movesC,movesA, Finset.mul_sum]; rw [Finset.sum_comm]; apply Finset.sum_eq_zero; intro k hk
      have he (j:Axis): I*(p j:ℂ)*(-(precision k j p:ℂ)*f (U k i p))= -(I*f (U k i p))*((precision j k p:ℂ)*(p j:ℂ)):=by rw [realK k j]; ring
      simp_rw [he,← Finset.mul_sum, Detect.Mark.czero,mul_zero] -- need Kinetic import Cube upstream
    · exact movesS ..
    · change Q (Q f) (W a i p)=0; simp_rw [movesA, movesU]; have he k : -(precision k a p:ℂ)*(-(I*(p k:ℂ))*f (S i p))= (I*f (S i p))*((precision k a p:ℂ)*(p k:ℂ)):=by ring
      simp_rw [he,← Finset.mul_sum,Detect.Mark.czero,mul_zero]
    change Q (Q f) (U a i p)=0; rw [movesU,movesS,mul_zero]
end YM.MS.Local.BV
