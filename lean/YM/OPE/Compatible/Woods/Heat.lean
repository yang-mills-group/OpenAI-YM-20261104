import YM.OPE.Compatible.Woods.Still
/-!
# Fixed patch tree quote on arbitrary tape and continuity in same weight by kinetic difference. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Woody
open Function Filter Set Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Next.Free FreeResolvent
open scoped Topology BigOperators ComplexConjugate
variable {G: Gauge}{ι:Type*} {c f L:Side}{t: ℕ}{P:Patch}{C:KernelChoices}{η v A s: ℝ}
open Frequency
lemma meet_root (D E:Row (TypeFace 2) (TypeFace 2))(N:Row (TypeFace 1) (TypeFace 1))(P:Patch)(K': KernelChoices)(hD: Whole D)(hE:Whole E)
    (hp: N.strip s A)(he:0<s)(hN:∀ n:Side,N.acts n=K (D.acts n)-K (E.acts n)):
 flatRow P K'.penalty D - flatRow P K'.penalty E = reblock P.L N := by
    have hz:Whole (reblock P.L N):=⟨s,_,he,reblock_price he.le hp⟩
    obtain ⟨σ,x,hσ,h⟩:= hD; obtain ⟨κ,y,hκ,hh⟩:= hE
    let T:= TypeFace 1; let X:= flatRow P K'.penalty D; let Y:= flatRow P K'.penalty E
    have hX:Whole X:=⟨σ,_,hσ,flatRow_strip P _ hσ.le h⟩; have hY:Whole Y:=⟨κ,_,hκ,flatRow_strip P _ hκ.le hh⟩
    apply bank_injective (A:=X-Y) (hX.minus hY).safe hz.safe
    intro n; change (minusRows X Y).acts n=_; rw [hX.less hY]; ext i j
    let S: StepData n (n*P.L):=⟨P,K',rfl⟩; let g:= S.ratio; let Q:Body 1 (n*P.L)≃ Co n (Co P.L T):= splitCo g T
    have hg: (X.acts n-Y.acts n).submatrix Q Q=((reblock P.L N).acts n).submatrix Q Q:= by
       have hx: baseMatrix S D=(X.acts n).submatrix Q Q:=flatRow_periods S hσ.le h
       have hy: baseMatrix S E=(Y.acts n).submatrix Q Q:=flatRow_periods S hκ.le hh
       have hv:N.acts _=_:= reblock_periods g he.le hp
       change N.acts (n*P.L)=((reblock P.L N).acts n).submatrix Q Q at hv
       rw [Matrix.submatrix_sub, Pi.sub_apply, Pi.sub_apply, ← hx, ←hy,← hv,hN]; unfold baseMatrix; abel
    have hv:=congr_fun (congr_fun hg (Q.symm i)) (Q.symm j);
    simp only [Matrix.submatrix_apply,Equiv.apply_symm_apply] at hv; exact hv
lemma hedge_delta {D E:Row (TypeFace 2) (TypeFace 2)}{N:Row (TypeFace 1) (TypeFace 1)}(hD:Whole D)(hE:Whole E)
   (hp: N.strip s A)(hs:0<s)(ha:0 ≤ A)(hN:∀ n:Side,N.acts n=K (D.acts n)-K (E.acts n)) : (hedge G P C D - hedge G P C E).strip s (Fintype.card (TypeFace 1)*A):=by
   have he: hedge G P C D-hedge G P C E=grove (colorRow G (reblock P.L N)):=by
      rw [← meet_root D E N P C hD hE hp hs hN]; funext i j a; dsimp only [hedge,FreeResolvent.fullRow,grove,colorRow,Pi.sub_apply]; split <;> first | rfl | simp
   rw [he]; intro i j; unfold grove
   by_cases H: (bird i).2.2=(bird j).2.2
   · rw [show colorRow _ _ _ _= reblock P.L N ((bird i).1,(bird i).2.1) ((bird j).1,(bird j).2.1) from funext fun x=> if_pos H]; exact reblock_price hs.le hp _ _
   simp [H,colorRow,Laurent.Width,RG.SumBudget,ha]
lemma Op_stays {C: KernelChoices}(hx: 4 ≤ t)(D : Train t)(n: Side): (Op C D).acts n = K ((pink C.penalty D).acts n):=by
    have hv:= (heart_saves C.penalty C.penalty_pos hx (fun i:Train t => i)).1.whole D; let W:=Whole.boundary 1; unfold Op; rw [(W.flipped.prod hv).acts W,W.flipped.acts hv,acts_trans]; rfl
lemma Op_whole {C: KernelChoices}(hx: 4 ≤ t)(D : Train t): Whole (Op C D):= ((Whole.boundary 1).flipped.prod ((heart_saves C.penalty C.penalty_pos hx (fun i:Train t=>i)).1.whole D)).prod (Whole.boundary 1)
def forge (P: Patch)(C:KernelChoices) (G:Gauge)(D : Train t) := hedge G P C (pink C.penalty D)
lemma hedge_trains (D E: Train t)(h:4 ≤ t)(he:0<s)(hp:(Op C D-Op C E).strip s A): (forge P C G D-forge P C G E).strip s (Fintype.card (TypeFace 1)*A) := by
    let F(i:Train t):= (heart_saves C.penalty C.penalty_pos h (fun i:Train t => i)).1.whole i
    have ha:0≤A:=by
       let v:=coord 0; exact (tsum_nonneg (hp v v).1).trans (hp v v).2.2
    refine hedge_delta (F D) (F E) hp he ha fun n=>?_; change (minusRows _ _).acts n=_; rw [(Op_whole h D).less (Op_whole h E), Op_stays h D n,Op_stays h E n]
end YM.OPE.Woody
