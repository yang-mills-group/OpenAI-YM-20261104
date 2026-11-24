import YM.LocalLTE.Keels.Values
/-! Reach the calibrated norm on changing actual probes. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Keels
open Function Filter Lattice Wilson RG Source Labels Extra.Histories Bid
open LocalLTE.Vinca LocalLTE.Drift LocalLTE.FrameBox AnalyticBridge VerifiedReset Collection Price PhysicalNext.Repeat Blush
open Push Local Planned.GuardedAtom LocalLTE.River YM.MergeProof
open Finset MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{H:History G}{N m p:ℕ}{d:ℕ}(F:Labels.Frame G d)
open Work.G08
variable {a b e α κ η c v s:ℝ}{k ℓ:ℕ}
local notation "Ψ"=> F.Coeff
local notation "K"=> F.coeffSize
variable (D:SectionData F) (B: Hol G)

-- bank assembly at printed basis
variable (X: Voice F H p (m+1)) (Y:Voice F H p m)
local notation "uP"=> X.index
local notation "vP"=> Y.index
variable (M:Worth)
open Motion
variable (P:F.Coeff→ Coefficient F (H.S.side m p))(hP:Ledger F (H.S.side m p) P)
variable (hp:Heard D H N p B (m+1) X)(hy:Heard D H N p B m Y)
noncomputable def rotor := X.index.symm.trans Y.index
-- explicit matrix preview.All apt P. No X.output formula in this definition.
noncomputable def nextK : Ψ→ₗ[ℂ] Ψ:= (IsLinearMap.mk' _ hP.x).comp X.index.symm.toLinearMap -- API check.
local notation "T" => H.rep N p m
local notation "Ω"=> nextK F X P hP
local notation "U"=> rotor F X Y
local notation "δ" => Real.sqrt (H.levels.clock.forcedAllowance m)
variable (hE: ∀ v:F.Coeff, Exhibition D α ℓ k B (H.rep N p m) (Y.plays v) (P v) (Real.sqrt (H.levels.clock.forcedAllowance m)) (s* F.coeffSize (Y.index v)) (e* F.coeffSize (Y.index v)))
variable (hs:0 ≤ s)(he:0≤e)(he':e ≤1/2)
variable (hM:Responds D H N p M m X Y)(hΒ:roomCost H.levels M)(hΓ: Bank M H.levels)
set_option quotPrecheck false
local notation "A0"=> (H.levels.params m).columns
local notation "T1" => (H.levels.params (m+1)).columns
local notation "S"=> ((H.S.block m).val:ℝ)
include hM hp hy hΒ hΓ
lemma orbitBound : ∀ u:F.Coeff, F.coeffSize (Y.index u) ≤ (H.levels.params (m+1)).columns*((H.S.block m).val:ℝ)^d* F.coeffSize (X.index u)∧ K ((uP) u) ≤ T1* K ((vP) u):=by
   intro v; have hk:= Work.G08.cone_step M H hΒ hΓ m F _ _ _ _ (hM.tally v) (by rw [hp.currents]; exact hp.cone v); rw [hp.currents,hy.currents] at hk; exact ⟨hk.2.2,hk.2.1⟩
omit hM hp hΒ hΓ
include hy hE hP
lemma trend (x:Ψ): K (U x - Ω x) ≤ e * K (U x):=by
    let u:= X.index.symm x
    have hp : U x - Ω x = (decrement (Y.plays u) (P u)).x:=by change Y.index u-(P u).x= (Y.plays u).x -(P u).x; rw [hy.currents]
    rw [hp]; exact (hE u).canon
include hM hΒ hΓ hp he he' hs
-- normalization at output canon.Lift.Error.K.main. lead EXACT.Ph. inertia prepared from entire ledger.Fixed costs not optimal.Pose preserves transformations supplied.
lemma tender : ∃ A:Ψ≃ₗ[ℂ] Ψ,A.toLinearMap = Ω ∧
    ∀ x:Ψ,let V:= x; let s₀:= K V; let hat:= X.index.symm (A.symm V); let actual:= Y.index.symm V
            K (U V - A V) ≤ e*(T1*S^d)*s₀ ∧ K ((U).symm V-A.symm V) ≤ T1*e*(2*s₀) ∧ (P hat).x=V∧ Exhibition D α ℓ k B T (Y.plays actual) (P hat) δ (s*(2*s₀)) ((1+A0)*e*(2*s₀)):=by
   have hΨ:= Keels.trend F D B X Y P hP hy hE
   obtain ⟨A,hA,Hq⟩:= Keels.supplies F (U) (Ω) he he' hΨ
   refine ⟨A,hA,?_⟩; intro x v s₀ hat u; let y:=X.index.symm v
   obtain ⟨hz,hz'⟩:= Hq v
   have hΛ:= Keels.orbitBound F D B X Y M hp hy hM hΒ hΓ
   have hw: K (U v) ≤ T1*S^d*s₀:=by change K (Y.index y)≤ _; have hx:= hΛ y|>.1; rw [show X.index y=v from X.index.apply_symm_apply v] at hx;exact hx
   have hQ:K (U v-(Ω) v)≤ e*(T1*S^d*s₀):= (hΨ v).trans (mul_le_mul_of_nonneg_left hw he)
   have hb: ∀ x,A x=(P (X.index.symm x)).x:=fun x=> (show A x=Ω x from LinearMap.congr_fun hA x)
   have hs':F.coeffSize (Y.index (hat-u)) ≤ e*(2*s₀):=by rw [map_sub,show Y.index u=v from Y.index.apply_symm_apply v];exact hz'
   have hu : F.coeffSize (Y.index (u-hat)) ≤ e*(2*s₀):=by rw [map_sub, size_sub_rev, ← map_sub];exact hs'
   refine ⟨?_, ?_,(hb _|>.symm).trans (A.apply_symm_apply v),?_⟩
   · rw [hb]; exact hQ.trans_eq (mul_assoc ..|>.symm)
   · have hp : K ((U).symm v - A.symm v)=K (X.index (u-hat)):=by rw [map_sub, show X.index hat=A.symm v from X.index.apply_symm_apply _]; rfl
     rw [hp]; exact (hΛ (u-hat)|>.2).trans ((mul_le_mul_of_nonneg_left hu (zero_le_one.trans (H.levels.params _).columns_ge)).trans_eq (mul_assoc ..|>.symm))
   have hP:= hE hat
   apply (Keels.remark F D B P Y hy u hat hP).pledge (mul_le_mul_of_nonneg_left hz hs) (?_)
   
   rw [hy.currents]
   refine le_trans (add_le_add (mul_le_mul_of_nonneg_left hz he) (mul_le_mul_of_nonneg_left hu (zero_le_one.trans (H.levels.params m).columns_ge))) (le_of_eq (?_)); ring
end YM.LocalLTE.Keels
