import YM.OPE.Compatible.Woods.Staff
import YM.OPE.Compatible.Stream.Cinder
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Covers
/-!
# The same tree slice on every mesh: its precision
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Woody
open Function Filter Set Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Next.Free FreeResolvent
open scoped Topology BigOperators ComplexConjugate
variable {G: Gauge}{ι:Type*} {c f L:Side}{P:Patch}{C:KernelChoices}{η v A s: ℝ}
abbrev bird {L:Side}(p: Slip G L):Co L (PAC G 1) := (p.1.val.1,coord p.1.val.2,p.2)
def grove (H:Row (Co L (PAC G 1)) (Co L (PAC G 1))):Row (Slip G L) (Slip G L) := fun i j => H (bird i) (bird j)
def hedge (G : Gauge)(P: Patch) (C: KernelChoices)(H: FaceRow) := grove (fullRow G P C.penalty H)
lemma hedge_width {H:FaceRow}(h:H.strip s A)(hs:0<s)(ha:0≤A): (hedge G P C H).strip s (outputPrice P C.penalty s A):= fun i j=> fullRow_width P _ hs.le ha h (bird i) (bird j)
lemma hedge_acts (H:FaceRow)(h:Whole H)(S:StepData c f)(hp:Odd S.patch.L.val):
   (let T:= forest S.ratio hp; let a:= squad S.ratio hp G; treeMatrix G S T H=((hedge G S.patch S.kernel H).acts c).submatrix a a) := by
     intro T a; obtain ⟨s,A,hs,h⟩:=h
     rw [treeMatrix,fullRow_periods S hs.le h]; ext i j
     simp only [Matrix.submatrix_apply]; erw [← rooting S.ratio hp, ← rooting S.ratio hp]; rfl
lemma hedge_gap {H:FaceRow}(h:Whole H)(hp:Odd P.L.val)(hb:P.Branches C G)(hh:∀ n:Side,Gap (H.acts n) v)(hv:0<v)(c:Side):
  Gap ((hedge G P C H).acts c) (treeFare G P C v):=by
     apply AnalyticBridge.LocalGaussianLaws.Current.cofinal_prices _ ?_ _ (100*Pressure.macroR P + 3) _ c
     · obtain ⟨s,A,hs,ht⟩:=h
       exact Whole.safe (show Whole _ from ⟨_,_,hs,hedge_width (strip_mono ht le_rfl (le_max_left A 0)) hs (le_max_right _ _)⟩)
     intro n hn; let S:StepData n (n*P.L):=⟨P,C,rfl⟩
     have hy:Bid.Larger (G:=G) S:= ⟨hb,by
       change 100*Pressure.macroR _ ≤ n.val*P.L.val
       exact (show 100*Pressure.macroR P≤n.val by omega).trans (Nat.le_mul_of_pos_right _ P.L.pos), by omega⟩
     let a:= squad S.ratio hp G; let F:=forest S.ratio hp; let A:= (hedge G P C H).acts n
     have he :=tree_gap S F H hy hv (hh _); have hX := he.submatrix a.symm a.symm.injective
     have hr: treeMatrix G S F H=A.submatrix a a:=hedge_acts H h S hp
     have hk:(treeMatrix G S F H).submatrix a.symm a.symm=A:= calc
          _=(A.submatrix a a).submatrix a.symm a.symm:= congrArg (fun X:Matrix (Active G F) (Active G F) ℝ=>X.submatrix a.symm a.symm) hr
          _=A:=by ext; simp
     rw [hk] at hX; exact hX
end YM.OPE.Woody
