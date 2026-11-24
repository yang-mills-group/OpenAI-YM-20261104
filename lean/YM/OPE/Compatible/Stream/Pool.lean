import YM.OPE.Compatible.Stream.Hully
/-!
# Curvature for history bridges. The same block predictor/penalty. Schur relation in true kinetic, so no need to enforce an evolution in unobservable extension on horizontal lifts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free.Frequency
open Function Filter Set Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08
open scoped Topology BigOperators ComplexConjugate
open Flight
variable {L:Side} {j k:ℕ} {η x U a B:ℝ} (P: Flight j k) (C:KernelChoices)
local notation "T"=> TypeFace 2
local notation "L₀"=> TypeFace 1
lemma itinerary (hk:4≤k){f c:Side}(hc:f.val=c.val*P.L.val) :
    let r:= P.visitRatio hc; installed r (P.psi C.penalty)*d 1 c=d 1 f*installed r (P.duo C.penalty).A0 :=by
   intro r
   let x:= C.penalty
   have he:= tangent P C hk hc
   let H:= (pink x P.wing).acts f; let V:= (blue x P.wing).acts f
   calc
      _ = V * (installed r (P.duo x).T * (pink x P.land).acts c * d 1 c):=by rw [psi_bridge x C.penalty_pos hk P hc]; simp only [← Matrix.mul_assoc];rfl
      _ = _:=by rw [show installed r (P.duo x).T * (pink x P.land).acts c*d 1 c=H*d 1 f*installed r (duo C.penalty P).A0 from he.2.2]; have h : V*H=1:=mul_eq_one_comm.mp (heart_inverse x C.penalty_pos P.legal P.wing f|>.1); simp only [← Matrix.mul_assoc,h,Matrix.one_mul]
-- 
lemma kato {f:Side} (H:Matrix (Body 2 f) (Body 2 f) ℝ)(h:Hᵀ=H) : (K H)ᵀ=K H:=by simp only [Precision.K, Matrix.transpose_mul,h,Matrix.transpose_transpose]; rw [Matrix.mul_assoc]
lemma kwon {f c:Side} (S: StepData c f) {W V:Matrix (Body 1 f) (Body 1 c) ℝ}{h g: Matrix (Body 2 f) (Body 2 f) ℝ}{l t :Matrix (Body 2 c) (Body 2 c) ℝ} (i:Inputs S W h l)(j: Inputs S V g t)
   (hh:hᵀ=h) (hl:lᵀ=l): Wᵀ*(K h-K g)*V = K l-K t:=by
   rw [Matrix.mul_sub,Matrix.sub_mul]
   have he: Wᵀ * K h= K l * mean S:= by
      apply Matrix.transpose_injective; rw [Matrix.transpose_mul, Matrix.transpose_mul,kato h hh,kato l hl, Matrix.transpose_transpose, i.primal]
   rw [he, Matrix.mul_assoc, j.dual, Matrix.mul_assoc, j.primal, ← Matrix.mul_assoc Wᵀ,← Matrix.transpose_mul,i.dual, transpose_sub,transpose_one, transpose_smul,kato l hl,Matrix.mul_sub,Matrix.mul_one, Matrix.sub_mul,Matrix.one_mul,Matrix.smul_mul,Matrix.mul_smul]; abel
local notation "Wing" v => pink C.penalty v
def Key (x y : Train j)(A:Row T T):Prop:= ∀ n:Side,K (A.acts n)=K ((Wing x).acts n)-K ((Wing y).acts n)
-- explicit Flight cadex same patch
variable {P₀:Patch} {h:P₀.J=j} -- instead
lemma pack_next (D:Patch)(v w: Train D.J)(hc:k ≤ D.J)(h' : D.J≤ k+1) (ht:4 ≤ k)
   (ha:0 < η)(hi: Covers η C.penalty U D.J k){A:Row T T} (g:Key C v w A)(hh:A.strip η a)(hR:A.read 0=0):
     let p :Flight D.J k:=⟨D.L,D.odd_side,D.coarse,D.order_cut,hc,h',v⟩; let q:Flight D.J k:= {p with wing:=w}
     Key C p.land q.land (sling q C.penalty (psi C.penalty p) A):=by
     intro p q f
     let F:= f*p.L; have hF : F.val=f.val*p.L.val:=rfl; have hQ : F.val=f.val*q.L.val:=rfl
     let r:=p.visitRatio hF
     let s:= visit p C hF
     let X:= installed r (p.duo C.penalty).A0; let Y:= installed r (q.duo C.penalty).A0
     have hp: (p.psi C.penalty).strip η (U / (p.L.val:ℝ)^2) := hi p [] (by simp)
     let G:= sling q C.penalty (psi C.penalty p) A
     have hf := sailed q (psi C.penalty p) ha hi hh hp C.penalty_pos ht hR hQ
     change (G.acts f) = (installed r _)ᵀ*(A.acts F)*_ at hf
     have hk:=(g F)
     let M := installed r (p.psi C.penalty); let N:= installed r (q.psi C.penalty)
     calc
        K (G.acts f)= Xᵀ*K (A.acts F)*Y:=by
            have hX:M*d 1 f=d 1 F*X:= itinerary p C ht hF; have hY:N*d 1 f=d 1 F*Y:= itinerary q C ht hQ
            rw [hf,Precision.K]; change (d 1 f)ᵀ*(Mᵀ*A.acts F*N)*_=_
            rw [Matrix.mul_assoc Mᵀ,← Matrix.mul_assoc (d 1 f)ᵀ, ← Matrix.transpose_mul,hX, Matrix.mul_assoc _ (A.acts F*N), Matrix.mul_assoc (A.acts F),hY, Precision.K]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = K ((Wing p.land).acts f)-K ((Wing q.land).acts f):= by rw [hk]; exact kwon s (tangent p C ht hF).1 (tangent q C ht hQ).1 (heart_inverse _ C.penalty_pos p.legal _ F).2.1 (heart_inverse _ C.penalty_pos ht _ f).2.1
end YM.Next.Free.Frequency
